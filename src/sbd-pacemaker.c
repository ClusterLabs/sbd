/* 
 * Copyright (C) 2013 Lars Marowsky-Bree <lmb@suse.com>
 * 
 * Based on crm_mon.c, which was:
 * Copyright (C) 2004 Andrew Beekhof <andrew@beekhof.net>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/* TODO list:
 *
 * - Trying to shutdown a node if no devices are up will fail, since SBD
 * currently uses a message via the disk to achieve this.
 *
 * - Shutting down cluster nodes while the majority of devices is down
 * will eventually take the cluster below the quorum threshold, at which
 * time the remaining cluster nodes will all immediately suicide.
 *
 */

#include <sys/param.h>

#include <crm/crm.h>

#include <stdio.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>
#include <libgen.h>
#include <sys/utsname.h>

#ifdef __linux__
#include <grp.h>  /* getgrnam_r, initgroups */
#include <pwd.h>  /* getpwuid_r */
#endif

#include <config.h>

#include <crm_config.h>
#include <crm/msg_xml.h>
#include <crm/common/util.h>
#include <crm/common/xml.h>
#include <crm/common/ipc.h>
#include <crm/common/mainloop.h>
#include <crm/cib.h>
#include <crm/pengine/status.h>

#include "sbd.h"

#ifndef HAVE_PE_NEW_WORKING_SET

#define pe_reset_working_set(data_set) cleanup_calculations(data_set)

static pe_working_set_t *
pe_new_working_set()
{
	pe_working_set_t *data_set = calloc(1, sizeof(pe_working_set_t));
	if (data_set != NULL) {
		set_working_set_defaults(data_set);
	}
	return data_set;
}

static void
pe_free_working_set(pe_working_set_t *data_set)
{
	if (data_set != NULL) {
		pe_reset_working_set(data_set);
		free(data_set);
	}
}

#endif

extern int disk_count;

static void clean_up(int rc);
static void crm_diff_update(const char *event, xmlNode * msg);
static int cib_connect(gboolean full);
static void compute_status(pe_working_set_t * data_set);
static gboolean mon_refresh_state(gpointer user_data);

static GMainLoop *mainloop = NULL;
static guint timer_id_reconnect = 0;
static guint timer_id_notify = 0;
static int reconnect_msec = 1000;
static int cib_connected = 0;

static cib_t *cib = NULL;
static xmlNode *current_cib = NULL;
static pe_working_set_t *data_set = NULL;

static long last_refresh = 0;

static gboolean
mon_timer_reconnect(gpointer data)
{
	int rc = 0;

	if (timer_id_reconnect > 0) {
		g_source_remove(timer_id_reconnect);
	}

	rc = cib_connect(TRUE);
	if (rc != 0) {
		cl_log(LOG_WARNING, "CIB reconnect failed: %d", rc);
		timer_id_reconnect = g_timeout_add(reconnect_msec, mon_timer_reconnect, NULL);
	} else {
		cl_log(LOG_INFO, "CIB reconnect successful");
	}

	return FALSE;
}

static void
mon_cib_connection_destroy(gpointer user_data)
{
	if (cib) {
		cib->cmds->signoff(cib);
		set_servant_health(pcmk_health_transient, LOG_WARNING, "Disconnected from CIB");
		timer_id_reconnect = g_timeout_add(reconnect_msec, mon_timer_reconnect, NULL);
	}
	cib_connected = 0;
	return;
}

static void
mon_retrieve_current_cib()
{
	xmlNode *xml_cib = NULL;
	int options = cib_scope_local | cib_sync_call;
	int rc = pcmk_ok;

	free_xml(current_cib);
	current_cib = NULL;

	rc = cib->cmds->query(cib, NULL, &xml_cib, options);

	if (rc != pcmk_ok) {
		crm_err("Couldn't retrieve the CIB: %s (%d)", pcmk_strerror(rc), rc);
		free_xml(xml_cib);
		return;

	} else if (xml_cib == NULL) {
		crm_err("Couldn't retrieve the CIB: empty result");
		return;
	}

	if (safe_str_eq(crm_element_name(xml_cib), XML_TAG_CIB)) {
		current_cib = xml_cib;

	} else {
		free_xml(xml_cib);
	}

	return;
}

static gboolean
mon_timer_notify(gpointer data)
{
	static int counter = 0;
	int counter_max = timeout_watchdog / timeout_loop;

	if (timer_id_notify > 0) {
		g_source_remove(timer_id_notify);
	}

	if (cib_connected) {
		if (counter == counter_max) {
			mon_retrieve_current_cib();
			mon_refresh_state(NULL);
			counter = 0;
		} else {
			cib->cmds->noop(cib, 0);
			notify_parent();
			counter++;
		}
	}
	timer_id_notify = g_timeout_add(timeout_loop * 1000, mon_timer_notify, NULL);
	return FALSE;
}

/*
 * Mainloop signal handler.
 */
static void
mon_shutdown(int nsig)
{
	clean_up(0);
}

static int
cib_connect(gboolean full)
{
	int rc = 0;

	CRM_CHECK(cib != NULL, return -EINVAL);

	cib_connected = 0;

	crm_xml_init();

	if (cib->state != cib_connected_query && cib->state != cib_connected_command) {

		rc = cib->cmds->signon(cib, crm_system_name, cib_query);

		if (rc != 0) {
			return rc;
		}

		mon_retrieve_current_cib();
		mon_refresh_state(NULL);

		if (full) {
			if (rc == 0) {
				rc = cib->cmds->set_connection_dnotify(cib, mon_cib_connection_destroy);
				if (rc == -EPROTONOSUPPORT) {
					/* Notification setup failed, won't be able to reconnect after failure */
					rc = 0;
				}
			}

			if (rc == 0) {
				cib->cmds->del_notify_callback(cib, T_CIB_DIFF_NOTIFY, crm_diff_update);
				rc = cib->cmds->add_notify_callback(cib, T_CIB_DIFF_NOTIFY, crm_diff_update);
			}

			if (rc != 0) {
				/* Notification setup failed, could not monitor CIB actions */
				clean_up(-rc);
			}
		}
	}
	
	if (!rc) {
		cib_connected = 1;
	}
	return rc;
}


static void
compute_status(pe_working_set_t * data_set)
{
    static int updates = 0;
    static int ever_had_quorum = FALSE;

    node_t *node = pe_find_node(data_set->nodes, local_uname);

    updates++;

    if (data_set->dc_node == NULL) {
        set_servant_health(pcmk_health_transient, LOG_INFO, "We don't have a DC right now.");
        notify_parent();
        return;
    }


    if (node == NULL) {
        set_servant_health(pcmk_health_unknown, LOG_WARNING, "Node state: %s is UNKNOWN", local_uname);

    } else if (node->details->online == FALSE) {
        set_servant_health(pcmk_health_unknown, LOG_WARNING, "Node state: OFFLINE");

    } else if (node->details->unclean) {
        set_servant_health(pcmk_health_unclean, LOG_WARNING, "Node state: UNCLEAN");

    } else if (node->details->pending) {
        set_servant_health(pcmk_health_pending, LOG_WARNING, "Node state: pending");

#if 0
    } else if (node->details->shutdown) {
        set_servant_health(pcmk_health_shutdown, LOG_WARNING, "Node state: shutting down");
#endif

    } else if (data_set->flags & pe_flag_have_quorum) {
        set_servant_health(pcmk_health_online, LOG_INFO, "Node state: online");
        ever_had_quorum = TRUE;

    } else if(disk_count > 0) {
        set_servant_health(pcmk_health_noquorum, LOG_WARNING, "Quorum lost");

    } else if(ever_had_quorum == FALSE) {
        set_servant_health(pcmk_health_online, LOG_INFO, "We do not have quorum yet");

    } else {
        /* We lost quorum, and there are no disks present
         * Setting healthy > 2 here will result in us self-fencing
         */
        switch (data_set->no_quorum_policy) {
            case no_quorum_freeze:
                set_servant_health(pcmk_health_transient, LOG_INFO, "Quorum lost: Freeze resources");
                break;
            case no_quorum_stop:
                set_servant_health(pcmk_health_transient, LOG_INFO, "Quorum lost: Stop ALL resources");
                break;
            case no_quorum_ignore:
                set_servant_health(pcmk_health_transient, LOG_INFO, "Quorum lost: Ignore");
                break;
            case no_quorum_suicide:
                set_servant_health(pcmk_health_unclean, LOG_INFO, "Quorum lost: Self-fence");
                break;
        }
    }

    notify_parent();
    return;
}

static crm_trigger_t *refresh_trigger = NULL;

static gboolean
mon_trigger_refresh(gpointer user_data)
{
    mainloop_set_trigger(refresh_trigger);
    mon_refresh_state(NULL);
    return FALSE;
}

static void
crm_diff_update(const char *event, xmlNode * msg)
{
	int rc = -1;
	const char *op = NULL;
        long now = time(NULL);
        static int updates = 0;
        static mainloop_timer_t *refresh_timer = NULL;

        if(refresh_timer == NULL) {
            refresh_timer = mainloop_timer_add("refresh", 2000, FALSE, mon_trigger_refresh, NULL);
            refresh_trigger = mainloop_add_trigger(G_PRIORITY_LOW, mon_refresh_state, refresh_timer);
        }

        if (current_cib != NULL) {
		xmlNode *cib_last = current_cib;
		current_cib = NULL;

		rc = cib_apply_patch_event(msg, cib_last, &current_cib, LOG_DEBUG);
		free_xml(cib_last);

		switch(rc) {
			case -pcmk_err_diff_resync:
			case -pcmk_err_diff_failed:
                            crm_warn("[%s] %s Patch aborted: %s (%d)", event, op, pcmk_strerror(rc), rc);
                            break;
			case pcmk_ok:
                            updates++;
                            break;
			default:
                            crm_notice("[%s] %s ABORTED: %s (%d)", event, op, pcmk_strerror(rc), rc);
                            break;
		}
	}

	if (current_cib == NULL) {
		mon_retrieve_current_cib();
	}

    /* Refresh
     * - immediately if the last update was more than 5s ago
     * - every 10 updates
     * - at most 2s after the last update
     */
    if (updates > 10 || (now - last_refresh) > (reconnect_msec / 1000)) {
        mon_refresh_state(refresh_timer);
        updates = 0;

    } else {
        mainloop_set_trigger(refresh_trigger);
        mainloop_timer_start(refresh_timer);
    }
}

static gboolean
mon_refresh_state(gpointer user_data)
{
    xmlNode *cib_copy = NULL;

    if(current_cib == NULL) {
        return FALSE;
    }

    if(user_data) {
        mainloop_timer_t *timer = user_data;

        mainloop_timer_stop(timer);
    }

    cib_copy = copy_xml(current_cib);
    if (cli_config_update(&cib_copy, NULL, FALSE) == FALSE) {
        cl_log(LOG_WARNING, "cli_config_update() failed - forcing reconnect to CIB");
        if (cib) {
            cib->cmds->signoff(cib);
        }

    } else {
        last_refresh = time(NULL);
        data_set->input = cib_copy;
        data_set->flags |= pe_flag_have_stonith_resource;
        cluster_status(data_set);

        compute_status(data_set);

        pe_reset_working_set(data_set);
    }

    return FALSE;
}

static void
clean_up(int rc)
{
	if (timer_id_reconnect > 0) {
		g_source_remove(timer_id_reconnect);
		timer_id_reconnect = 0;
	}

	if (timer_id_notify > 0) {
		g_source_remove(timer_id_notify);
		timer_id_notify = 0;
	}

	if (data_set != NULL) {
		pe_free_working_set(data_set);
		data_set = NULL;
	}

	if (cib != NULL) {
		cib->cmds->signoff(cib);
		cib_delete(cib);
		cib = NULL;
	}

	if (rc >= 0) {
		exit(rc);
	}
	return;
}

#ifdef __linux__
#define CLUSTER_GROUP  "haclient"
/* Try to add well-known cluster stack group (CLUSTER_GROUP) as a supplementary
   group to this root-privileged process for good measure (see the call site);
   returns 0 in case of success, respective positive exit status (different
   from 0, 1, and EXIT_MD_IO_FAIL...EXIT_MD_REQUEST_CRASHDUMP) otherwise. */
static int
add_cluster_group()
{
    int rc = 0;
    long gr_limit = -1, pw_limit = -1, limit;
    char *buf;
    struct group group, *group_result;
    struct passwd passwd, *passwd_result;
    gid_t cluster_gid;

    limit = sysconf(_SC_PAGESIZE);
    limit = (limit > 0) ? limit : 4096;  /* assume sufficient, just in case */
    gr_limit = sysconf(_SC_GETGR_R_SIZE_MAX);
    gr_limit = (gr_limit > 0) ? gr_limit : limit;
    pw_limit = sysconf(_SC_GETPW_R_SIZE_MAX);
    limit = (gr_limit >= pw_limit) ? gr_limit : pw_limit;

    if ((buf = malloc(limit)) == NULL) {
        return 74;  /* EX_IOERR */
    }

    do {
        rc = getgrnam_r(CLUSTER_GROUP, &group, buf, limit, &group_result);
    } while (rc == -1 && errno == EINTR);
    if (rc == -1 || group_result == NULL) {
        if (rc == -1) {
            cl_perror("Unable to get group entry for %s", CLUSTER_GROUP);
            rc = 69;  /* EX_UNAVAILABLE */
        } else {
            cl_log(LOG_ERR, "Unable to get group entry for %s", CLUSTER_GROUP);
            rc = 78;  /* EX_CONFIG */
        }
        goto bail;
    }
    cluster_gid = group.gr_gid;

    do {
        rc = getpwuid_r(0, &passwd, buf, limit, &passwd_result);
    } while (rc == -1 && errno == EINTR);
    if (rc == -1 || passwd_result == NULL) {
        if (rc == -1) {
            cl_perror("Unable to get passwd entry for UID=0");
            rc = 69;  /* EX_UNAVAILABLE */
        } else {
            cl_log(LOG_ERR, "Unable to get passwd entry for UID=0");
            rc = 78;  /* EX_CONFIG */
        }
        goto bail;
    }

    /* this is supposed to be root, hence (1) shall succeed and
       (2) the root shall not gain any new unwanted group-based
       access over what it already has per its standard supplementary
       groups even if they have been explicitly dropped by now (not
       the case now; root is usually just in its own group, too) */
    rc = initgroups(passwd.pw_name, cluster_gid);
    if (rc == -1) {
        cl_perror("Unable to set supplementary group %s", CLUSTER_GROUP);
        rc = (errno == EPERM) ? 77  /* EX_NOPERM */
                              : 74  /* EX_IOERR */;
    }

bail:
    free(buf);
    return rc;
}
#endif

int
servant_pcmk(const char *diskname, int mode, const void* argp)
{
	int exit_code = 0;

        crm_system_name = strdup("sbd:pcmk");
	cl_log(LOG_NOTICE, "Monitoring Pacemaker health");
	set_proc_title("sbd: watcher: Pacemaker");
        setenv("PCMK_watchdog", "true", 1);

#ifdef __linux__
        /* since we run this as root, we may actually be prevented from
           accessing hacluster:haclient owned shared IPC mmap'd files of,
           e.g., pacemakerd-based ("CIB daemon") in some cases where
           root is not "all powerful" (e.g. under strict SELinux
           confinement not allowing a DAC_OVERRIDE for any reasons)
           TODO: first check if CAP_DAC_OVERRIDE is missing? */
        if ((exit_code = add_cluster_group()) > 0) {
            cl_log(LOG_CRIT, "Unable to ensure Pacemaker can be watched");
            clean_up(exit_code);
        }
#endif

        if(debug == 0) {
            /* We don't want any noisy crm messages */
            set_crm_log_level(LOG_CRIT);
        }


	if (data_set == NULL) {
		data_set = pe_new_working_set();
	}
	if (data_set == NULL) {
		return -1;
	}

	if (current_cib == NULL) {
		cib = cib_new();

		do {
			exit_code = cib_connect(TRUE);

			if (exit_code != 0) {
				sleep(reconnect_msec / 1000);
			}
		} while (exit_code == -ENOTCONN);

		if (exit_code != 0) {
			clean_up(-exit_code);
		}
	}

	mainloop = g_main_new(FALSE);

	mainloop_add_signal(SIGTERM, mon_shutdown);
	mainloop_add_signal(SIGINT, mon_shutdown);
	timer_id_notify = g_timeout_add(timeout_loop * 1000, mon_timer_notify, NULL);

	g_main_run(mainloop);
	g_main_destroy(mainloop);

	clean_up(0);
	return 0;                   /* never reached */
}


