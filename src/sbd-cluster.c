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

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <config.h>
#include <crm_config.h>

#include <crm/cluster.h>
#include <crm/common/mainloop.h>

#if CHECK_TWO_NODE || CHECK_QDEVICE_SYNC_TIMEOUT
#include <glib-unix.h>
#endif

#include "sbd.h"

//undef SUPPORT_PLUGIN
//define SUPPORT_PLUGIN 1

/* binary for pacemaker-remote has changed with pacemaker 2 */
#ifdef CRM_SCORE_INFINITY
#define PACEMAKER_REMOTE_BINARY "pacemaker-remoted"
#else
#define PACEMAKER_REMOTE_BINARY "pacemaker_remoted"
#endif

static bool remote_node = false;
static pid_t remoted_pid = 0;
static int reconnect_msec = 1000;
static GMainLoop *mainloop = NULL;
static guint notify_timer = 0;
static crm_cluster_t cluster;
static gboolean sbd_remote_check(gpointer user_data);
static long unsigned int find_pacemaker_remote(void);
static void sbd_membership_destroy(gpointer user_data);
static bool wait_for_pacemaker_remote_lost = false;

static void signal_exitreq(void)
{
    union sigval signal_value;
    pid_t ppid = getppid();

    memset(&signal_value, 0, sizeof(signal_value));
    sigqueue(ppid, SIG_EXITREQ, signal_value);
}

#if SUPPORT_PLUGIN
static void
sbd_plugin_membership_dispatch(cpg_handle_t handle,
                           const struct cpg_name *groupName,
                           uint32_t nodeid, uint32_t pid, void *msg, size_t msg_len)
{
    if(msg_len > 0) {
        set_servant_health(pcmk_health_online, LOG_INFO,
                           "Connected to %s", name_for_cluster_type(get_cluster_type()));
    } else {
        set_servant_health(pcmk_health_unclean, LOG_WARNING,
                           "Broken %s message", name_for_cluster_type(get_cluster_type()));
    }
    notify_parent();
    return;
}
#endif

#if SUPPORT_COROSYNC

#if CHECK_VOTEQUORUM_HANDLE
#include <corosync/votequorum.h>

static votequorum_handle_t votequorum_handle = 0;
#endif

#if CHECK_TWO_NODE
static bool two_node = false;
#endif
static bool ever_seen_both = false;
static int cpg_membership_entries = -1;

#if CHECK_QDEVICE_SYNC_TIMEOUT
#include <corosync/votequorum.h>
static bool using_qdevice = false;
static uint32_t qdevice_sync_timeout = /* in seconds */
    VOTEQUORUM_QDEVICE_DEFAULT_SYNC_TIMEOUT / 1000;
#endif

#if CHECK_TWO_NODE || CHECK_QDEVICE_SYNC_TIMEOUT
#include <corosync/cmap.h>

static cmap_handle_t cmap_handle = 0;
static cmap_track_handle_t track_handle = 0;
static GSource *cmap_source = NULL;
#endif

void
sbd_cpg_membership_health_update()
{
    if(cpg_membership_entries > 0) {
#if CHECK_TWO_NODE
        bool quorum_is_suspect_two_node =
            (two_node && ever_seen_both && cpg_membership_entries == 1);
#endif
#if CHECK_QDEVICE_SYNC_TIMEOUT
        bool quorum_is_suspect_qdevice_timing =
            using_qdevice && (qdevice_sync_timeout > timeout_watchdog);
#endif

        do {
#if CHECK_TWO_NODE
            if (quorum_is_suspect_two_node) {
               /* Alternative would be asking votequorum for number of votes.
                * Using pacemaker's cpg as source for number of active nodes
                * avoids binding to an additional library, is definitely
                * less code to write and we wouldn't have to combine data
                * from 3 sources (cmap, cpg & votequorum) in a potentially
                * racy environment.
                */
                set_servant_health(pcmk_health_noquorum, LOG_WARNING,
                    "Connected to %s but requires both nodes present",
                    name_for_cluster_type(get_cluster_type())
                    );
                break;
            }
#endif
#if CHECK_QDEVICE_SYNC_TIMEOUT
            if (quorum_is_suspect_qdevice_timing) {
               /* We can't really trust quorum info as qdevice-sync_timeout
                * makes reaction of quorum too sluggish for our
                * watchdog-timeout.
                */
                set_servant_health(pcmk_health_noquorum, LOG_WARNING,
                    "Connected to %s but quorum using qdevice is distrusted "
                    "for SBD as qdevice-sync_timeout (%ds) > watchdog-timeout "
                    "(%lus).",
                    name_for_cluster_type(get_cluster_type()),
                    qdevice_sync_timeout, timeout_watchdog
                    );
                break;
            }
#endif
            set_servant_health(pcmk_health_online, LOG_INFO,
                "Connected to %s (%u members)%s",
                name_for_cluster_type(get_cluster_type()),
                cpg_membership_entries,
#if CHECK_QDEVICE_SYNC_TIMEOUT
                using_qdevice?" using qdevice for quorum":""
#else
                ""
#endif
            );
        } while (false);

        if (cpg_membership_entries > 1) {
            ever_seen_both = true;
        }
    } else {
        set_servant_health(pcmk_health_unclean, LOG_WARNING,
                           "Empty %s membership", name_for_cluster_type(get_cluster_type()));
    }
}

void
sbd_cpg_membership_dispatch(cpg_handle_t handle,
                    const struct cpg_name *groupName,
                    const struct cpg_address *member_list, size_t member_list_entries,
                    const struct cpg_address *left_list, size_t left_list_entries,
                    const struct cpg_address *joined_list, size_t joined_list_entries)
{
    cpg_membership_entries = member_list_entries;
    sbd_cpg_membership_health_update();
    notify_parent();
}

#if CHECK_TWO_NODE || CHECK_QDEVICE_SYNC_TIMEOUT
static void sbd_cmap_notify_fn(
    cmap_handle_t cmap_handle,
    cmap_track_handle_t cmap_track_handle,
    int32_t event,
    const char *key_name,
    struct cmap_notify_value new_val,
    struct cmap_notify_value old_val,
    void *user_data)
{
    switch (event) {
        case CMAP_TRACK_ADD:
        case CMAP_TRACK_MODIFY:
            switch (new_val.type) {
                case CMAP_VALUETYPE_UINT8:
#if CHECK_TWO_NODE
                    if (!strcmp(key_name, "quorum.two_node")) {
                        two_node = *((uint8_t *) new_val.data);
                    } else {
                        return;
                    }
                    break;
#else
                    return;
#endif
                case CMAP_VALUETYPE_STRING:
#if CHECK_QDEVICE_SYNC_TIMEOUT
                    if (!strcmp(key_name, "quorum.device.model")) {
                        using_qdevice =
                            ((new_val.data) && strlen((char *) new_val.data));
                    } else {
                        return;
                    }
                    break;
#else
                    return;
#endif
                case CMAP_VALUETYPE_UINT32:
#if CHECK_QDEVICE_SYNC_TIMEOUT
                    if (!strcmp(key_name, "quorum.device.sync_timeout")) {
                        if (new_val.data) {
                            qdevice_sync_timeout =
                                *((uint32_t *) new_val.data) / 1000;
                        } else {
                            qdevice_sync_timeout =
                                VOTEQUORUM_QDEVICE_DEFAULT_SYNC_TIMEOUT / 1000;
                        }
                    } else {
                        return;
                    }
                    break;
#else
                    return;
#endif
                default:
                    return;
            }
            break;
        case CMAP_TRACK_DELETE:
            switch (new_val.type) {
                case CMAP_VALUETYPE_UINT8:
#if CHECK_TWO_NODE
                    if (!strcmp(key_name, "quorum.two_node")) {
                        two_node = false;
                    } else {
                        return;
                    }
                    break;
#else
                    return;
#endif
                case CMAP_VALUETYPE_STRING:
#if CHECK_QDEVICE_SYNC_TIMEOUT
                    if (!strcmp(key_name, "quorum.device.model")) {
                        using_qdevice = false;
                    } else {
                        return;
                    }
                    break;
#else
                    return;
#endif
                case CMAP_VALUETYPE_UINT32:
#if CHECK_QDEVICE_SYNC_TIMEOUT
                    if (!strcmp(key_name, "quorum.device.sync_timeout")) {
                        qdevice_sync_timeout =
                            VOTEQUORUM_QDEVICE_DEFAULT_SYNC_TIMEOUT / 1000;
                    } else {
                        return;
                    }
                    break;
#else
                    return;
#endif
                default:
                    return;
            }
            break;
        default:
            return;
    }
    sbd_cpg_membership_health_update();
    notify_parent();
}

static gboolean
cmap_dispatch_callback (gpointer user_data)
{
    cmap_dispatch(cmap_handle, CS_DISPATCH_ALL);
    return TRUE;
}

static void
cmap_destroy(void)
{
    if (cmap_source) {
        g_source_destroy(cmap_source);
        cmap_source = NULL;
    }

    if (track_handle) {
        cmap_track_delete(cmap_handle, track_handle);
        track_handle = 0;
    }

    if (cmap_handle) {
        cmap_finalize(cmap_handle);
        cmap_handle = 0;
    }
}

static gboolean
verify_against_cmap_config(void)
{
#if CHECK_TWO_NODE
    uint8_t two_node_u8 = 0;
#endif
#if CHECK_QDEVICE_SYNC_TIMEOUT
    char *qdevice_model = NULL;
#endif
    int cmap_fd;

    if (!track_handle) {
        if (cmap_initialize(&cmap_handle) != CS_OK) {
            cl_log(LOG_WARNING, "Cannot initialize CMAP service\n");
            goto out;
        }

#if CHECK_TWO_NODE
        if (cmap_track_add(cmap_handle, "quorum.two_node",
                            CMAP_TRACK_DELETE|CMAP_TRACK_MODIFY|CMAP_TRACK_ADD,
                            sbd_cmap_notify_fn, NULL, &track_handle) != CS_OK) {
            cl_log(LOG_WARNING, "Failed adding CMAP tracker for 2Node-mode\n");
            goto out;
        }
#endif

#if CHECK_QDEVICE_SYNC_TIMEOUT
        if (cmap_track_add(cmap_handle, "quorum.device.model",
                            CMAP_TRACK_DELETE|CMAP_TRACK_MODIFY|CMAP_TRACK_ADD,
                            sbd_cmap_notify_fn, NULL, &track_handle) != CS_OK) {
            cl_log(LOG_WARNING, "Failed adding CMAP tracker for qdevice-model\n");
            goto out;
        }

        if (cmap_track_add(cmap_handle, "quorum.device.sync_timeout",
                            CMAP_TRACK_DELETE|CMAP_TRACK_MODIFY|CMAP_TRACK_ADD,
                            sbd_cmap_notify_fn, NULL, &track_handle) != CS_OK) {
            cl_log(LOG_WARNING,
                   "Failed adding CMAP tracker for qdevice-sync_timeout\n");
            goto out;
        }
#endif

        /* add the tracker to mainloop */
        if (cmap_fd_get(cmap_handle, &cmap_fd) != CS_OK) {
            cl_log(LOG_WARNING, "Failed to get a file handle for cmap\n");
            goto out;
        }

        if (!(cmap_source = g_unix_fd_source_new (cmap_fd, G_IO_IN))) {
            cl_log(LOG_WARNING, "Couldn't create source for cmap\n");
            goto out;
        }
        g_source_set_callback(cmap_source, cmap_dispatch_callback, NULL, NULL);
        g_source_attach(cmap_source, NULL);
    }

#if CHECK_TWO_NODE
    if (cmap_get_uint8(cmap_handle, "quorum.two_node", &two_node_u8)
            == CS_OK) {
        cl_log(two_node_u8? LOG_NOTICE : LOG_INFO,
               "Corosync is%s in 2Node-mode", two_node_u8?"":" not");
        two_node = two_node_u8;
    } else {
        cl_log(LOG_INFO, "quorum.two_node not present in cmap\n");
    }
#endif

#if CHECK_QDEVICE_SYNC_TIMEOUT
    if (cmap_get_string(cmap_handle, "quorum.device.model",
                        &qdevice_model) == CS_OK) {
        using_qdevice = qdevice_model && strlen(qdevice_model);
        cl_log(using_qdevice? LOG_NOTICE : LOG_INFO,
               "Corosync is%s using qdevice", using_qdevice?"":" not");
    } else {
        cl_log(LOG_INFO, "quorum.device.model not present in cmap\n");
    }

    if (cmap_get_uint32(cmap_handle, "quorum.device.sync_timeout",
                        &qdevice_sync_timeout) == CS_OK) {
        qdevice_sync_timeout /= 1000;
        cl_log(LOG_INFO,
               "Corosync is using qdevice-sync_timeout=%ds",
               qdevice_sync_timeout);
    } else {
        cl_log(LOG_INFO,
               "quorum.device.sync_timeout not present in cmap\n");
    }
#endif

    return TRUE;

out:
    cmap_destroy();

    return FALSE;
}
#endif
#endif

static gboolean
notify_timer_cb(gpointer data)
{
    cl_log(LOG_DEBUG, "Refreshing %sstate", remote_node?"remote ":"");

    if(remote_node) {
        sbd_remote_check(NULL);
        return TRUE;
    }

    switch (get_cluster_type()) {
#if HAVE_DECL_PCMK_CLUSTER_CLASSIC_AIS
        case pcmk_cluster_classic_ais:
            send_cluster_text(crm_class_quorum, NULL, TRUE, NULL, crm_msg_ais);
            break;

#endif
        case pcmk_cluster_corosync:
            do {
#if SUPPORT_COROSYNC && CHECK_VOTEQUORUM_HANDLE
                struct votequorum_info info;

                if (votequorum_getinfo(votequorum_handle, 0, &info) != CS_OK) {

                    votequorum_finalize(votequorum_handle);
                    if (votequorum_initialize(&votequorum_handle, NULL) != CS_OK) {
                        votequorum_handle = 0;
                        break;
                    }
                    if (votequorum_getinfo(votequorum_handle, 0, &info) != CS_OK) {
                        break;
                    }
                }
#endif
                notify_parent();
            } while (0);
            break;

#if HAVE_DECL_PCMK_CLUSTER_CMAN
        case pcmk_cluster_cman:

            notify_parent();
            break;
#endif

        default:
            break;
    }
    return TRUE;
}


static void
sbd_membership_connect(void)
{
    bool connected = false;

    cl_log(LOG_INFO, "Attempting cluster connection");

    cluster.destroy = sbd_membership_destroy;

#if SUPPORT_PLUGIN
    cluster.cpg.cpg_deliver_fn = sbd_plugin_membership_dispatch;
#endif

#if SUPPORT_COROSYNC
    cluster.cpg.cpg_confchg_fn = sbd_cpg_membership_dispatch;
#endif

    while(connected == false) {

        enum cluster_type_e stack = get_cluster_type();
        if(get_cluster_type() == pcmk_cluster_unknown) {
            crm_debug("Attempting pacemaker remote connection");
            /* Nothing is up, go looking for the pacemaker remote process */
            if(find_pacemaker_remote() > 0) {
                connected = true;
            }

        } else {
            cl_log(LOG_INFO, "Attempting connection to %s", name_for_cluster_type(stack));

#if SUPPORT_COROSYNC && (CHECK_TWO_NODE || CHECK_QDEVICE_SYNC_TIMEOUT)
            if (verify_against_cmap_config()) {
#endif

                if(crm_cluster_connect(&cluster)) {
                    connected = true;
                }

#if SUPPORT_COROSYNC && (CHECK_TWO_NODE || CHECK_QDEVICE_SYNC_TIMEOUT)
            }
#endif
        }

        if(connected == false) {
            cl_log(LOG_INFO, "Failed, retrying in %ds", reconnect_msec / 1000);
            sleep(reconnect_msec / 1000);
        }
    }

    set_servant_health(pcmk_health_transient, LOG_INFO, "Connected, waiting for initial membership");
    notify_parent();

    notify_timer_cb(NULL);
}

static void
sbd_membership_destroy(gpointer user_data)
{
    cl_log(LOG_WARNING, "Lost connection to %s", name_for_cluster_type(get_cluster_type()));

    if (get_cluster_type() != pcmk_cluster_unknown) {
#if SUPPORT_COROSYNC && (CHECK_TWO_NODE || CHECK_QDEVICE_SYNC_TIMEOUT)
        cmap_destroy();
#endif
    }

    set_servant_health(pcmk_health_unclean, LOG_ERR, "Cluster connection terminated");
    notify_parent();

    /* Attempt to reconnect, the watchdog will take the node down if the problem isn't transient */
    sbd_membership_connect();
}

/*
 * \internal
 * \brief Get process ID and name associated with a /proc directory entry
 *
 * \param[in]  entry    Directory entry (must be result of readdir() on /proc)
 * \param[out] name     If not NULL, a char[16] to hold the process name
 * \param[out] pid      If not NULL, will be set to process ID of entry
 *
 * \return 0 on success, -1 if entry is not for a process or info not found
 *
 * \note This should be called only on Linux systems, as not all systems that
 *       support /proc store process names and IDs in the same way.
 *       Copied from the Pacemaker implementation.
 */
int
sbd_procfs_process_info(struct dirent *entry, char *name, int *pid)
{
    int fd, local_pid;
    FILE *file;
    struct stat statbuf;
    char procpath[128] = { 0 };

    /* We're only interested in entries whose name is a PID,
     * so skip anything non-numeric or that is too long.
     *
     * 114 = 128 - strlen("/proc/") - strlen("/status") - 1
     */
    local_pid = atoi(entry->d_name);
    if ((local_pid <= 0) || (strlen(entry->d_name) > 114)) {
        return -1;
    }
    if (pid) {
        *pid = local_pid;
    }

    /* Get this entry's file information */
    strcpy(procpath, "/proc/");
    strcat(procpath, entry->d_name);
    fd = open(procpath, O_RDONLY);
    if (fd < 0 ) {
        return -1;
    }
    if (fstat(fd, &statbuf) < 0) {
        close(fd);
        return -1;
    }
    close(fd);

    /* We're only interested in subdirectories */
    if (!S_ISDIR(statbuf.st_mode)) {
        return -1;
    }

    /* Read the first entry ("Name:") from the process's status file.
     * We could handle the valgrind case if we parsed the cmdline file
     * instead, but that's more of a pain than it's worth.
     */
    if (name != NULL) {
        strcat(procpath, "/status");
        file = fopen(procpath, "r");
        if (!file) {
            return -1;
        }
        if (fscanf(file, "Name:\t%15[a-zA-Z0-9 _-]", name) != 1) {
            fclose(file);
            return -1;
        }
        fclose(file);
    }

    return 0;
}


static gboolean
sbd_remote_check(gpointer user_data)
{
    static int have_proc_pid = 0;

    int running = 0;

    cl_log(LOG_DEBUG, "Checking pacemaker remote connection: %d/%d", have_proc_pid, remoted_pid);
    
    if(have_proc_pid == 0) {
        char proc_path[PATH_MAX], exe_path[PATH_MAX];

        /* check to make sure pid hasn't been reused by another process */
        snprintf(proc_path, sizeof(proc_path), "/proc/%lu/exe", (long unsigned int)getpid());

        have_proc_pid = 1;
        if(readlink(proc_path, exe_path, PATH_MAX - 1) < 0) {
            have_proc_pid = -1;
        }
    }
    
    if (remoted_pid <= 0) {
        set_servant_health(pcmk_health_transient, LOG_WARNING, "No Pacemaker Remote connection");
        goto notify;

    } else if (kill(remoted_pid, 0) < 0 && errno == ESRCH) {
        /* Not running */

    } else if(have_proc_pid == -1) {
        running = 1;
        cl_log(LOG_DEBUG, "Poccess %ld is active", (long)remoted_pid);

    } else {
        int rc = 0;
        char proc_path[PATH_MAX], exe_path[PATH_MAX];

        /* check to make sure pid hasn't been reused by another process */
        snprintf(proc_path, sizeof(proc_path), "/proc/%lu/exe", (long unsigned int)remoted_pid);

        rc = readlink(proc_path, exe_path, PATH_MAX - 1);
        if (rc < 0) {
            crm_perror(LOG_ERR, "Could not read from %s", proc_path);
            goto done;
        }
        exe_path[rc] = 0;

        if (strcmp(exe_path, SBINDIR "/" PACEMAKER_REMOTE_BINARY) == 0) {
            cl_log(LOG_DEBUG, "Process %s (%ld) is active",
                   exe_path, (long)remoted_pid);
            running = 1;
        }
    }

  done:
    
    if(running) {
        set_servant_health(pcmk_health_online, LOG_INFO,
                           "Connected to Pacemaker Remote %lu", (long unsigned int)remoted_pid);
    } else {
        if (wait_for_pacemaker_remote_lost) {
            signal_exitreq();
            return true;
        }
        set_servant_health(pcmk_health_unclean, LOG_WARNING,
                           "Connection to Pacemaker Remote %lu lost", (long unsigned int)remoted_pid);
    }

  notify:    
    notify_parent();

    if(running == 0) {
        sbd_membership_connect();
    }
    return true;
}

static long unsigned int
find_pacemaker_remote(void)
{
    DIR *dp;
    char entry_name[16];
    struct dirent *entry;

    dp = opendir("/proc");
    if (!dp) {
        /* no proc directory to search through */
        cl_log(LOG_NOTICE, "Can not read /proc directory to track existing components");
        return FALSE;
    }

    while ((entry = readdir(dp)) != NULL) {
        int pid;

        if (sbd_procfs_process_info(entry, entry_name, &pid) < 0) {
            continue;
        }

        /* entry_name is truncated to 16 characters including the nul terminator */
        cl_log(LOG_DEBUG, "Found %s at %u", entry_name, pid);
        if (strncmp(entry_name, PACEMAKER_REMOTE_BINARY, 15) == 0) {
            cl_log(LOG_NOTICE, "Found Pacemaker Remote at PID %u", pid);
            remoted_pid = pid;
            remote_node = true;
            break;
        }
    }

    closedir(dp);

    return remoted_pid;
}

static void
clean_up(int rc)
{
#if CHECK_VOTEQUORUM_HANDLE
    votequorum_finalize(votequorum_handle);
    votequorum_handle = 0; /* there isn't really an invalid handle value
                            * just to be back where we started
                            */
#endif
    return;
}

static void
cluster_shutdown(int nsig)
{
    clean_up(0);
}

static void
trigger_wait_for_pacemaker_remote_lost(int nsig)
{
    /* if we've never seen pacemaker_remoted request exit immeditely */
    if ((remoted_pid <= 0) || !remote_node) {
        signal_exitreq();
    }
    wait_for_pacemaker_remote_lost = true;
}

int
servant_cluster(const char *diskname, int mode, const void* argp)
{
    enum cluster_type_e cluster_stack = get_cluster_type();

    crm_system_name = strdup("sbd:cluster");
    cl_log(LOG_NOTICE, "Monitoring %s cluster health", name_for_cluster_type(cluster_stack));
    set_proc_title("sbd: watcher: Cluster");

    sbd_membership_connect();

    /* stonith_our_uname = cluster.uname; */
    /* stonith_our_uuid = cluster.uuid; */

    mainloop = g_main_loop_new(NULL, FALSE);
    notify_timer = g_timeout_add(timeout_loop * 1000, notify_timer_cb, NULL);

    mainloop_add_signal(SIGTERM, cluster_shutdown);
    mainloop_add_signal(SIGINT, cluster_shutdown);
	mainloop_add_signal(SIGUSR2, trigger_wait_for_pacemaker_remote_lost);
    
    g_main_loop_run(mainloop);
    g_main_loop_unref(mainloop);
    
    clean_up(0);
    return 0;                   /* never reached */
}
