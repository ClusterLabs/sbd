/*
 * Copyright (C) 2013 Lars Marowsky-Bree <lmb@suse.com>
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

#include <crm/common/util.h>
#include "sbd.h"
#define	LOCKSTRLEN	11

static struct servants_list_item *servants_leader = NULL;

int     disk_priority = 1;
int	check_pcmk = 1;
int	check_cluster = 1;
int	has_check_pcmk_env = false;
int	disk_count	= 0;
int	servant_count	= 0;
int	servant_restart_interval = 5;
int	servant_restart_count = 1;
int	start_mode = 0;
char*	pidfile = NULL;
bool do_flush = true;
char timeout_sysrq_char = 'b';
bool move_to_root_cgroup = true;
bool enforce_moving_to_root_cgroup = false;
bool sync_resource_startup = false;

int parse_device_line(const char *line);

static int
sanitize_numeric_option_value(const char *value)
{
    char *end = NULL;
    long int result = -1;

    if (value == NULL) {
        return -1;
    }

    errno = 0;

    result = strtol(value, &end, 10);
    if (result <= INT_MIN || result >= INT_MAX || errno != 0) {
        result = -1;
    } else if (*end != '\0') {
        result = -1;
    }

    return (int)result;
}

static const char *
sanitize_option_value(const char *value)
{
	size_t max = 0;
	size_t lpc = 0;

	if (value == NULL) {
		return NULL;
	}

	max = strlen(value);

	for (lpc = 0; lpc < max; lpc++) {
		if (!isspace(value[lpc])) {
			break;
		}
	}

	return (strlen(value + lpc) > 0 ? (value + lpc) : NULL);
}

static const char *
get_env_option(const char *option)
{
	const char *value = getenv(option);

	return sanitize_option_value(value);
}

static int
recruit_servant(const char *devname, pid_t pid)
{
	struct servants_list_item *s = servants_leader;
	struct servants_list_item *newbie;

	if (lookup_servant_by_dev(devname)) {
	    cl_log(LOG_DEBUG, "Servant %s already exists", devname);
	    return 0;
	}

	newbie = malloc(sizeof(*newbie));
	if (newbie) {
	    memset(newbie, 0, sizeof(*newbie));
	    newbie->devname = strdup(devname);
	    newbie->pid = pid;
	    newbie->first_start = 1;
	}
	if (!newbie || !newbie->devname) {
	    fprintf(stderr, "heap allocation failed in recruit_servant.\n");
	    exit(1);
	}

	/* some sanity-check on our newbie */
	if (sbd_is_disk(newbie)) {
	    cl_log(LOG_INFO, "Monitoring %s", devname);
	    disk_count++;
	} else if (sbd_is_pcmk(newbie) || sbd_is_cluster(newbie)) {
	    /* alive just after pcmk and cluster servants have shown up */
	    newbie->outdated = 1;
	} else {
	    /* toss our newbie */
	    cl_log(LOG_ERR, "Refusing to recruit unrecognized servant %s", devname);
	    free((void *) newbie->devname);
	    free(newbie);
	    return -1;
	}

	if (!s) {
		servants_leader = newbie;
	} else {
		while (s->next)
			s = s->next;
		s->next = newbie;
	}

	servant_count++;

	return 0;
}

int assign_servant(const char* devname, functionp_t functionp, int mode, const void* argp)
{
	pid_t pid = 0;
	int rc = 0;

	pid = fork();
	if (pid == 0) {		/* child */
		maximize_priority();
                sbd_set_format_string(QB_LOG_SYSLOG, devname);
		rc = (*functionp)(devname, mode, argp);
		if (rc == -1)
			exit(1);
		else
			exit(0);
	} else if (pid != -1) {		/* parent */
		return pid;
	} else {
		cl_log(LOG_ERR,"Failed to fork servant");
		exit(1);
	}
}

struct servants_list_item *lookup_servant_by_dev(const char *devname)
{
	struct servants_list_item *s;

	for (s = servants_leader; s; s = s->next) {
		if (strcasecmp(s->devname, devname) == 0)
			break;
	}
	return s;
}

struct servants_list_item *lookup_servant_by_pid(pid_t pid)
{
	struct servants_list_item *s;

	for (s = servants_leader; s; s = s->next) {
		if (s->pid == pid)
			break;
	}
	return s;
}

int check_all_dead(void)
{
	struct servants_list_item *s;
	int r = 0;
	union sigval svalue;

	for (s = servants_leader; s; s = s->next) {
		if (s->pid != 0) {
			r = sigqueue(s->pid, 0, svalue);
			if (r == -1 && errno == ESRCH)
				continue;
			return 0;
		}
	}
	return 1;
}

void servant_start(struct servants_list_item *s)
{
	int r = 0;
	union sigval svalue;

	if (s->pid != 0) {
		r = sigqueue(s->pid, 0, svalue);
		if ((r != -1 || errno != ESRCH))
			return;
	}
	s->restarts++;
	if (sbd_is_disk(s)) {
#if SUPPORT_SHARED_DISK
		DBGLOG(LOG_INFO, "Starting servant for device %s", s->devname);
		s->pid = assign_servant(s->devname, servant_md, start_mode, s);
#else
                cl_log(LOG_ERR, "Shared disk functionality not supported");
                return;
#endif
	} else if(sbd_is_pcmk(s)) {
		DBGLOG(LOG_INFO, "Starting Pacemaker servant");
		s->pid = assign_servant(s->devname, servant_pcmk, start_mode, NULL);

	} else if(sbd_is_cluster(s)) {
		DBGLOG(LOG_INFO, "Starting Cluster servant");
		s->pid = assign_servant(s->devname, servant_cluster, start_mode, NULL);

        } else {
            cl_log(LOG_ERR, "Unrecognized servant: %s", s->devname);
        }        

	clock_gettime(CLOCK_MONOTONIC, &s->t_started);
	return;
}

void servants_start(void)
{
	struct servants_list_item *s;

	for (s = servants_leader; s; s = s->next) {
		s->restarts = 0;
		servant_start(s);
	}
}

void servants_kill(int sig)
{
	struct servants_list_item *s;
	union sigval svalue;

	for (s = servants_leader; s; s = s->next) {
		if (s->pid != 0)
			sigqueue(s->pid, sig, svalue);
	}
}

static inline void cleanup_servant_by_pid(pid_t pid)
{
	struct servants_list_item* s;

	s = lookup_servant_by_pid(pid);
	if (s) {
		cl_log(LOG_WARNING, "Servant for %s (pid: %i) has terminated",
				s->devname, s->pid);
		s->pid = 0;
	} else {
		/* This most likely is a stray signal from somewhere, or
		 * a SIGCHLD for a process that has previously
		 * explicitly disconnected. */
		DBGLOG(LOG_INFO, "cleanup_servant: Nothing known about pid %i",
				pid);
	}
}

int inquisitor_decouple(void)
{
	pid_t ppid = getppid();
	union sigval signal_value;

	/* During start-up, we only arm the watchdog once we've got
	 * quorum at least once. */
	if (watchdog_use) {
		if (watchdog_init() < 0) {
			return -1;
		}
	}

	if (ppid > 1) {
		sigqueue(ppid, SIG_LIVENESS, signal_value);
	}
	return 0;
}

static int sbd_lock_running(long pid)
{
	int rc = 0;
	long mypid;
	int running = 0;
	char proc_path[PATH_MAX], exe_path[PATH_MAX], myexe_path[PATH_MAX];

	/* check if pid is running */
	if (kill(pid, 0) < 0 && errno == ESRCH) {
		goto bail;
	}

#ifndef HAVE_PROC_PID
	return 1;
#endif

	/* check to make sure pid hasn't been reused by another process */
	snprintf(proc_path, sizeof(proc_path), "/proc/%lu/exe", pid);
	rc = readlink(proc_path, exe_path, PATH_MAX-1);
	if(rc < 0) {
		cl_perror("Could not read from %s", proc_path);
		goto bail;
	}
	exe_path[rc] = 0;
	mypid = (unsigned long) getpid();
	snprintf(proc_path, sizeof(proc_path), "/proc/%lu/exe", mypid);
	rc = readlink(proc_path, myexe_path, PATH_MAX-1);
	if(rc < 0) {
		cl_perror("Could not read from %s", proc_path);
		goto bail;
	}
	myexe_path[rc] = 0;

	if(strcmp(exe_path, myexe_path) == 0) {
		running = 1;
	}

  bail:
	return running;
}

static int
sbd_lock_pidfile(const char *filename)
{
	char lf_name[256], tf_name[256], buf[LOCKSTRLEN+1];
	int fd;
	long	pid, mypid;
	int rc;
	struct stat sbuf;

	if (filename == NULL) {
		errno = EFAULT;
		return -1;
	}

	mypid = (unsigned long) getpid();
	snprintf(lf_name, sizeof(lf_name), "%s",filename);
	snprintf(tf_name, sizeof(tf_name), "%s.%lu",
		 filename, mypid);

	if ((fd = open(lf_name, O_RDONLY)) >= 0) {
		if (fstat(fd, &sbuf) >= 0 && sbuf.st_size < LOCKSTRLEN) {
			sleep(1); /* if someone was about to create one,
			   	   * give'm a sec to do so
				   * Though if they follow our protocol,
				   * this won't happen.  They should really
				   * put the pid in, then link, not the
				   * other way around.
				   */
		}
		if (read(fd, buf, sizeof(buf)) < 1) {
			/* lockfile empty -> rm it and go on */;
		} else {
			if (sscanf(buf, "%ld", &pid) < 1) {
				/* lockfile screwed up -> rm it and go on */
			} else {
				if (pid > 1 && (getpid() != pid)
				&&	sbd_lock_running(pid)) {
					/* is locked by existing process
					 * -> give up */
					close(fd);
					return -1;
				} else {
					/* stale lockfile -> rm it and go on */
				}
			}
		}
		unlink(lf_name);
		close(fd);
	}
	if ((fd = open(tf_name, O_CREAT | O_WRONLY | O_EXCL, 0644)) < 0) {
		/* Hmmh, why did we fail? Anyway, nothing we can do about it */
		return -3;
	}

	/* Slight overkill with the %*d format ;-) */
	snprintf(buf, sizeof(buf), "%*lu\n", LOCKSTRLEN-1, mypid);

	if (write(fd, buf, LOCKSTRLEN) != LOCKSTRLEN) {
		/* Again, nothing we can do about this */
		rc = -3;
		close(fd);
		goto out;
	}
	close(fd);

	switch (link(tf_name, lf_name)) {
	case 0:
		if (stat(tf_name, &sbuf) < 0) {
			/* something weird happened */
			rc = -3;
			break;
		}
		if (sbuf.st_nlink < 2) {
			/* somehow, it didn't get through - NFS trouble? */
			rc = -2;
			break;
		}
		rc = 0;
		break;
	case EEXIST:
		rc = -1;
		break;
	default:
		rc = -3;
	}
 out:
	unlink(tf_name);
	return rc;
}


/*
 * Unlock a file (remove its lockfile) 
 * do we need to check, if its (still) ours? No, IMHO, if someone else
 * locked our line, it's his fault  -tho
 * returns 0 on success
 * <0 if some failure occured
 */

static int
sbd_unlock_pidfile(const char *filename)
{
	char lf_name[256];

	if (filename == NULL) {
		errno = EFAULT;
		return -1;
	}

	snprintf(lf_name, sizeof(lf_name), "%s", filename);

	return unlink(lf_name);
}

int cluster_alive(bool all)
{
    int alive = 1;
    struct servants_list_item* s;

    if(servant_count == disk_count) {
        return 0;
    }

    for (s = servants_leader; s; s = s->next) {
        if (sbd_is_cluster(s) || sbd_is_pcmk(s)) {
            if(s->outdated) {
                alive = 0;
            } else if(all == false) {
                return 1;
            }
        }
    }

    return alive;
}

int quorum_read(int good_servants)
{
	if (disk_count > 2) 
		return (good_servants > disk_count/2);
	else
		return (good_servants > 0);
}

void inquisitor_child(void)
{
	int sig, pid;
	sigset_t procmask;
	siginfo_t sinfo;
	int status;
	struct timespec timeout;
	int exiting = 0;
	int decoupled = 0;
	int cluster_appeared = 0;
	int pcmk_override = 0;
	time_t latency;
	struct timespec t_last_tickle, t_now;
	struct servants_list_item* s;

	if (debug_mode) {
            cl_log(LOG_ERR, "DEBUG MODE %d IS ACTIVE - DO NOT RUN IN PRODUCTION!", debug_mode);
	}

	set_proc_title("sbd: inquisitor");

	if (pidfile) {
		if (sbd_lock_pidfile(pidfile) < 0) {
			exit(1);
		}
	}

	sigemptyset(&procmask);
	sigaddset(&procmask, SIGCHLD);
	sigaddset(&procmask, SIGTERM);
	sigaddset(&procmask, SIG_LIVENESS);
	sigaddset(&procmask, SIG_EXITREQ);
	sigaddset(&procmask, SIG_TEST);
	sigaddset(&procmask, SIG_PCMK_UNHEALTHY);
	sigaddset(&procmask, SIG_RESTART);
	sigaddset(&procmask, SIGUSR1);
	sigaddset(&procmask, SIGUSR2);
	sigprocmask(SIG_BLOCK, &procmask, NULL);

	servants_start();

	timeout.tv_sec = timeout_loop;
	timeout.tv_nsec = 0;
	clock_gettime(CLOCK_MONOTONIC, &t_last_tickle);

	while (1) {
                bool tickle = 0;
                bool can_detach = 0;
		int good_servants = 0;

		sig = sigtimedwait(&procmask, &sinfo, &timeout);

		clock_gettime(CLOCK_MONOTONIC, &t_now);

		if (sig == SIG_EXITREQ || sig == SIGTERM) {
			servants_kill(SIGKILL);
			watchdog_close(true);
			exiting = 1;
		} else if (sig == SIGCHLD) {
			while ((pid = waitpid(-1, &status, WNOHANG))) {
				if (pid == -1 && errno == ECHILD) {
					break;
				} else {
					s = lookup_servant_by_pid(pid);
					if (sbd_is_disk(s)) {
						if (WIFEXITED(status)) {
							switch(WEXITSTATUS(status)) {
								case EXIT_MD_SERVANT_IO_FAIL:
									DBGLOG(LOG_INFO, "Servant for %s requests to be disowned",
										s->devname);
									break;
								case EXIT_MD_SERVANT_REQUEST_RESET:
									cl_log(LOG_WARNING, "%s requested a reset", s->devname);
									do_reset();
									break;
								case EXIT_MD_SERVANT_REQUEST_SHUTOFF:
									cl_log(LOG_WARNING, "%s requested a shutoff", s->devname);
									do_off();
									break;
								case EXIT_MD_SERVANT_REQUEST_CRASHDUMP:
									cl_log(LOG_WARNING, "%s requested a crashdump", s->devname);
									do_crashdump();
									break;
								default:
									break;
							}
						}
					} else if (sbd_is_pcmk(s)) {
						if (WIFEXITED(status)) {
							switch(WEXITSTATUS(status)) {
								case EXIT_PCMK_SERVANT_GRACEFUL_SHUTDOWN:
									DBGLOG(LOG_INFO, "PCMK-Servant has exited gracefully");
									/* revert to state prior to pacemaker-detection */
									s->restarts = 0;
									s->restart_blocked = 0;
									cluster_appeared = 0;
									s->outdated = 1;
									s->t_last.tv_sec = 0;
									break;
								default:
									break;
							}
						}
					}
					cleanup_servant_by_pid(pid);
				}
			}
		} else if (sig == SIG_PCMK_UNHEALTHY) {
			s = lookup_servant_by_pid(sinfo.si_pid);
			if (sbd_is_cluster(s) || sbd_is_pcmk(s)) {
                if (s->outdated == 0) {
                    cl_log(LOG_WARNING, "%s health check: UNHEALTHY", s->devname);
                }
                s->t_last.tv_sec = 1;
            } else {
                cl_log(LOG_WARNING, "Ignoring SIG_PCMK_UNHEALTHY from unknown source");
            }
		} else if (sig == SIG_LIVENESS) {
			s = lookup_servant_by_pid(sinfo.si_pid);
			if (s) {
				s->first_start = 0;
				clock_gettime(CLOCK_MONOTONIC, &s->t_last);
			}

		} else if (sig == SIG_TEST) {
		} else if (sig == SIGUSR1) {
			if (exiting)
				continue;
			servants_start();
		} else if (sig == SIGUSR2) {
			servants_kill(SIGUSR2);
		}

		if (exiting) {
			if (check_all_dead()) {
				if (pidfile) {
					sbd_unlock_pidfile(pidfile);
				}
				exit(0);
			} else
				continue;
		}

		good_servants = 0;
		for (s = servants_leader; s; s = s->next) {
			int age = t_now.tv_sec - s->t_last.tv_sec;

			if (!s->t_last.tv_sec)
				continue;

			if (age < (int)(timeout_io+timeout_loop)) {
				if (sbd_is_disk(s)) {
                                    good_servants++;
				}
                                if (s->outdated) {
                                    cl_log(LOG_NOTICE, "Servant %s is healthy (age: %d)", s->devname, age);
				}
				s->outdated = 0;

			} else if (!s->outdated) {
                                if (!s->restart_blocked) {
                                    cl_log(LOG_WARNING, "Servant %s is outdated (age: %d)", s->devname, age);
				}
                                s->outdated = 1;
			}
		}

                if(disk_count == 0) {
                    /* NO disks, everything is up to the cluster */
                    
                    if(cluster_alive(true)) {
                        /* We LIVE! */
                        if(cluster_appeared == false) {
                            cl_log(LOG_INFO, "Active cluster detected");
                        }
                        tickle = 1;
                        can_detach = 1;
                        cluster_appeared = 1;

                    } else if(cluster_alive(false)) {
                        if(!decoupled) {
                            /* On the way up, detach and arm the watchdog */
                            cl_log(LOG_INFO, "Partial cluster detected, detaching");
                        }

                        can_detach = 1;
                        tickle = !cluster_appeared;

                    } else if(!decoupled) {
                        /* Stay alive until the cluster comes up */
                        tickle = !cluster_appeared;
                    }

                } else if(disk_priority == 1 || servant_count == disk_count) {
                    if (quorum_read(good_servants)) {
                        /* There are disks and we're connected to the majority of them */
                        tickle = 1;
                        can_detach = 1;
                        pcmk_override = 0;

                    } else if (servant_count > disk_count && cluster_alive(true)) {
                        tickle = 1;
                    
                        if(!pcmk_override) {
                            cl_log(LOG_WARNING, "Majority of devices lost - surviving on pacemaker");
                            pcmk_override = 1; /* Only log this message once */
                        }
                    }

                } else if(cluster_alive(true) && quorum_read(good_servants)) {
                    /* Both disk and cluster servants are healthy */
                    tickle = 1;
                    can_detach = 1;
                    cluster_appeared = 1;

                } else if(quorum_read(good_servants)) {
                    /* The cluster takes priority but only once
                     * connected for the first time.
                     *
                     * Until then, we tickle based on disk quorum.
                     */
                    can_detach = 1;
                    tickle = !cluster_appeared;
                }

                /* cl_log(LOG_DEBUG, "Tickle: q=%d, g=%d, p=%d, s=%d", */
                /*        quorum_read(good_servants), good_servants, tickle, disk_count); */

                if(tickle) {
                    watchdog_tickle();
                    clock_gettime(CLOCK_MONOTONIC, &t_last_tickle);
                }

                if (!decoupled && can_detach) {
                    /* We only do this at the point either the disk or
                     * cluster servants become healthy
                     */
                    cl_log(LOG_DEBUG, "Decoupling");
                    if (inquisitor_decouple() < 0) {
                        servants_kill(SIGKILL);
                        exiting = 1;
                        continue;
                    } else {
                        decoupled = 1;
                    }
                }

		/* Note that this can actually be negative, since we set
		 * last_tickle after we set now. */
		latency = t_now.tv_sec - t_last_tickle.tv_sec;
		if (timeout_watchdog && (latency > (int)timeout_watchdog)) {
			if (!decoupled) {
				/* We're still being watched by our
				 * parent. We don't fence, but exit. */
				cl_log(LOG_ERR, "SBD: Not enough votes to proceed. Aborting start-up.");
				servants_kill(SIGKILL);
				exiting = 1;
				continue;
			}
			if (debug_mode < 2) {
				/* At level 2 or above, we do nothing, but expect
				 * things to eventually return to
				 * normal. */
				do_timeout_action();
			} else {
				cl_log(LOG_ERR, "SBD: DEBUG MODE: Would have fenced due to timeout!");
			}
		}

		if (timeout_watchdog_warn && (latency > (int)timeout_watchdog_warn)) {
			cl_log(LOG_WARNING,
			       "Latency: No liveness for %ds exceeds watchdog warning timeout of %ds (healthy servants: %d)",
			       (int)latency, (int)timeout_watchdog_warn, good_servants);

                        if (debug_mode && watchdog_use) {
                            /* In debug mode, trigger a reset before the watchdog can panic the machine */
                            do_timeout_action();
                        }
		}

		for (s = servants_leader; s; s = s->next) {
			int age = t_now.tv_sec - s->t_started.tv_sec;

			if (age > servant_restart_interval) {
				s->restarts = 0;
				s->restart_blocked = 0;
			}

			if (servant_restart_count
					&& (s->restarts >= servant_restart_count)
					&& !s->restart_blocked) {
				if (servant_restart_count > 1) {
					cl_log(LOG_WARNING, "Max retry count (%d) reached: not restarting servant for %s",
							(int)servant_restart_count, s->devname);
				}
				s->restart_blocked = 1;
			}

			if (!s->restart_blocked) {
				servant_start(s);
			}
		}
	}
	/* not reached */
	exit(0);
}

int inquisitor(void)
{
	int sig, pid, inquisitor_pid;
	int status;
	sigset_t procmask;
	siginfo_t sinfo;

	/* Where's the best place for sysrq init ?*/
	sysrq_init();

	sigemptyset(&procmask);
	sigaddset(&procmask, SIGCHLD);
	sigaddset(&procmask, SIG_LIVENESS);
	sigprocmask(SIG_BLOCK, &procmask, NULL);

	inquisitor_pid = make_daemon();
	if (inquisitor_pid == 0) {
		inquisitor_child();
	} 
	
	/* We're the parent. Wait for a happy signal from our child
	 * before we proceed - we either get "SIG_LIVENESS" when the
	 * inquisitor has completed the first successful round, or
	 * ECHLD when it exits with an error. */

	while (1) {
		sig = sigwaitinfo(&procmask, &sinfo);
		if (sig == SIGCHLD) {
			while ((pid = waitpid(-1, &status, WNOHANG))) {
				if (pid == -1 && errno == ECHILD) {
					break;
				}
				/* We got here because the inquisitor
				 * did not succeed. */
				return -1;
			}
		} else if (sig == SIG_LIVENESS) {
			/* Inquisitor started up properly. */
			return 0;
		} else {
			fprintf(stderr, "Nobody expected the spanish inquisition!\n");
			continue;
		}
	}
	/* not reached */
	return -1;
}


int
parse_device_line(const char *line)
{
    size_t lpc = 0;
    size_t last = 0;
    size_t max = 0;
    int found = 0;
    bool skip_space = true;
    int space_run = 0;

    if (!line) {
        return 0;
    }

    max = strlen(line);

    cl_log(LOG_DEBUG, "Processing %d bytes: [%s]", (int) max, line);

    for (lpc = 0; lpc <= max; lpc++) {
        if (isspace(line[lpc])) {
            if (skip_space) {
                last = lpc + 1;
            } else {
                space_run++;
            }
            continue;
        }
        skip_space = false;
        if (line[lpc] == ';' || line[lpc] == 0) {
            int rc = 0;
            char *entry = calloc(1, 1 + lpc - last);

            if (entry) {
                rc = sscanf(line + last, "%[^;]", entry);
            } else {
                fprintf(stderr, "Heap allocation failed parsing device-line.\n");
                exit(1);
            }

            if (rc != 1) {
                cl_log(LOG_WARNING, "Could not parse: '%s'", line + last);
            } else {
                entry[strlen(entry)-space_run] = '\0';
                cl_log(LOG_DEBUG, "Adding '%s'", entry);
                if (recruit_servant(entry, 0) != 0) {
                    free(entry);
                    // sbd should refuse to start if any of the configured device names is invalid.
                    return -1;
                }
                found++;
            }

            free(entry);
            skip_space = true;
            last = lpc + 1;
        }
        space_run = 0;
    }
    return found;
}

#define SBD_SOURCE_FILES "sbd-cluster.c,sbd-common.c,sbd-inquisitor.c,sbd-md.c,sbd-pacemaker.c,setproctitle.c"

static void
sbd_log_filter_ctl(const char *files, uint8_t priority)
{
	if (files == NULL) {
		files = SBD_SOURCE_FILES;
	}

	qb_log_filter_ctl(QB_LOG_SYSLOG, QB_LOG_FILTER_ADD, QB_LOG_FILTER_FILE, files, priority);
	qb_log_filter_ctl(QB_LOG_STDERR, QB_LOG_FILTER_ADD, QB_LOG_FILTER_FILE, files, priority);
}

int
arg_enabled(int arg_count)
{
    return arg_count % 2;
}

int main(int argc, char **argv, char **envp)
{
	int exit_status = 0;
	int c;
	int W_count = 0;
	int c_count = 0;
	int P_count = 0;
        int qb_facility;
        const char *value = NULL;
        bool delay_start = false;
        long delay = 0;
        char *timeout_action = NULL;

	if ((cmdname = strrchr(argv[0], '/')) == NULL) {
		cmdname = argv[0];
	} else {
		++cmdname;
	}

        watchdogdev = strdup("/dev/watchdog");
        watchdogdev_is_default = true;
        qb_facility = qb_log_facility2int("daemon");
        qb_log_init(cmdname, qb_facility, LOG_WARNING);
        sbd_set_format_string(QB_LOG_SYSLOG, "sbd");

        qb_log_ctl(QB_LOG_SYSLOG, QB_LOG_CONF_ENABLED, QB_TRUE);
        qb_log_ctl(QB_LOG_STDERR, QB_LOG_CONF_ENABLED, QB_FALSE);
        sbd_log_filter_ctl(NULL, LOG_NOTICE);

	sbd_get_uname();

        value = get_env_option("SBD_PACEMAKER");
        if(value) {
            check_pcmk = crm_is_true(value);
            check_cluster = crm_is_true(value);

            has_check_pcmk_env = true;
        }
        cl_log(LOG_INFO, "SBD_PACEMAKER set to: %d (%s)", (int)check_pcmk, value?value:"default");

        value = get_env_option("SBD_STARTMODE");
        if(value == NULL) {
        } else if(strcmp(value, "clean") == 0) {
            start_mode = 1;
        } else if(strcmp(value, "always") == 0) {
            start_mode = 0;
        }
        cl_log(LOG_INFO, "Start mode set to: %d (%s)", (int)start_mode, value?value:"default");

        value = get_env_option("SBD_WATCHDOG_DEV");
        if(value) {
            free(watchdogdev);
            watchdogdev = strdup(value);
            watchdogdev_is_default = false;
        }

        /* SBD_WATCHDOG has been dropped from sbd.sysconfig example.
         * This is for backward compatibility. */
        value = get_env_option("SBD_WATCHDOG");
        if(value) {
            watchdog_use = crm_is_true(value);
        }

        value = get_env_option("SBD_WATCHDOG_TIMEOUT");
        if(value) {
            timeout_watchdog = crm_get_msec(value) / 1000;
        }

        value = get_env_option("SBD_PIDFILE");
        if(value) {
            pidfile = strdup(value);
            cl_log(LOG_INFO, "pidfile set to %s", pidfile);
        }

        value = get_env_option("SBD_DELAY_START");
        if(value) {
            delay_start = crm_is_true(value);

            if (!delay_start) {
                delay = crm_get_msec(value) / 1000;
                if (delay > 0) {
                    delay_start = true;
                }
            }
        }

        value = get_env_option("SBD_TIMEOUT_ACTION");
        if(value) {
            timeout_action = strdup(value);
        }

        value = get_env_option("SBD_MOVE_TO_ROOT_CGROUP");
        if(value) {
            move_to_root_cgroup = crm_is_true(value);

            if (move_to_root_cgroup) {
               enforce_moving_to_root_cgroup = true;
            } else {
                if (strcmp(value, "auto") == 0) {
                    move_to_root_cgroup = true;
                }
            }
        }

	while ((c = getopt(argc, argv, "czC:DPRTWZhvw:d:n:p:1:2:3:4:5:t:I:F:S:s:r:")) != -1) {
		int sanitized_num_optarg = 0;
		/* Call it before checking optarg for NULL to make coverity happy */
		const char *sanitized_optarg = sanitize_option_value(optarg);

		if (optarg && ((sanitized_optarg == NULL) ||
				(strchr("SsC12345tIF", c) &&
				(sanitized_num_optarg = sanitize_numeric_option_value(sanitized_optarg)) < 0))) {
			fprintf(stderr, "Invalid value \"%s\" for option -%c\n", optarg, c);
			exit_status = -2;
			goto out;
		}

		switch (c) {
		case 'D':
			break;
		case 'Z':
			debug_mode++;
			cl_log(LOG_INFO, "Debug mode now at level %d", (int)debug_mode);
			break;
		case 'R':
			skip_rt = 1;
			cl_log(LOG_INFO, "Realtime mode deactivated.");
			break;
		case 'S':
			start_mode = sanitized_num_optarg;
			cl_log(LOG_INFO, "Start mode set to: %d", (int)start_mode);
			break;
		case 's':
			timeout_startup = sanitized_num_optarg;
			cl_log(LOG_INFO, "Start timeout set to: %d", (int)timeout_startup);
			break;
		case 'v':
                    debug++;
                    if(debug == 1) {
                        sbd_log_filter_ctl(NULL, LOG_INFO);
                        cl_log(LOG_INFO, "Verbose mode enabled.");

                    } else if(debug == 2) {
                        sbd_log_filter_ctl(NULL, LOG_DEBUG);
                        cl_log(LOG_INFO, "Debug mode enabled.");

                    } else if(debug == 3) {
                        /* Go nuts, turn on pacemaker's logging too */
                        sbd_log_filter_ctl("*", LOG_DEBUG);
                        cl_log(LOG_INFO, "Debug library mode enabled.");
                    }
                    break;
		case 'T':
			watchdog_set_timeout = 0;
			cl_log(LOG_INFO, "Setting watchdog timeout disabled; using defaults.");
			break;
		case 'W':
			W_count++;
			break;
		case 'w':
                        free(watchdogdev);
                        watchdogdev = strdup(sanitized_optarg);
                        watchdogdev_is_default = false;
                        cl_log(LOG_NOTICE, "Using watchdog device '%s'", watchdogdev);
			break;
		case 'd':
#if SUPPORT_SHARED_DISK
			if (recruit_servant(sanitized_optarg, 0) != 0) {
				fprintf(stderr, "Invalid device: %s\n", optarg);
				exit_status = -1;
				goto out;
			}
#else
                        fprintf(stderr, "Shared disk functionality not supported\n");
			exit_status = -2;
			goto out;
#endif
			break;
		case 'c':
			c_count++;
			break;
		case 'P':
			P_count++;
			break;
		case 'z':
			disk_priority = 0;
			break;
		case 'n':
			local_uname = strdup(sanitized_optarg);
			cl_log(LOG_INFO, "Overriding local hostname to %s", local_uname);
			break;
		case 'p':
			pidfile = strdup(sanitized_optarg);
			cl_log(LOG_INFO, "pidfile set to %s", pidfile);
			break;
		case 'C':
			timeout_watchdog_crashdump = sanitized_num_optarg;
			cl_log(LOG_INFO, "Setting crashdump watchdog timeout to %d",
					(int)timeout_watchdog_crashdump);
			break;
		case '1':
			timeout_watchdog = sanitized_num_optarg;
			break;
		case '2':
			timeout_allocate = sanitized_num_optarg;
			break;
		case '3':
			timeout_loop = sanitized_num_optarg;
			break;
		case '4':
			timeout_msgwait = sanitized_num_optarg;
			break;
		case '5':
			timeout_watchdog_warn = sanitized_num_optarg;
			do_calculate_timeout_watchdog_warn = false;
			cl_log(LOG_INFO, "Setting latency warning to %d",
					(int)timeout_watchdog_warn);
			break;
		case 't':
			servant_restart_interval = sanitized_num_optarg;
			cl_log(LOG_INFO, "Setting servant restart interval to %d",
					(int)servant_restart_interval);
			break;
		case 'I':
			timeout_io = sanitized_num_optarg;
			cl_log(LOG_INFO, "Setting IO timeout to %d",
					(int)timeout_io);
			break;
		case 'F':
			servant_restart_count = sanitized_num_optarg;
			cl_log(LOG_INFO, "Servant restart count set to %d",
					(int)servant_restart_count);
			break;
		case 'r':
			if (timeout_action) {
				free(timeout_action);
			}
			timeout_action = strdup(sanitized_optarg);
			break;
		case 'h':
			usage();
			goto out;
			break;
		default:
			exit_status = -2;
			goto out;
			break;
		}
	}

    if (disk_count == 0) {
        /* if we already have disks from commandline
           then it is probably undesirable to add those
           from environment (general rule cmdline has precedence)
         */
        value = get_env_option("SBD_DEVICE");
        if ((value) && strlen(value)) {
#if SUPPORT_SHARED_DISK
            int devices = parse_device_line(value);
            if(devices < 1) {
                fprintf(stderr, "Invalid device line: %s\n", value);
                exit_status = -1;
                goto out;
            }
#else
            fprintf(stderr, "Shared disk functionality not supported\n");
            exit_status = -2;
            goto out;
#endif
        }
	}

	if (watchdogdev == NULL || strcmp(watchdogdev, "/dev/null") == 0) {
            watchdog_use = 0;

	} else if (W_count > 0) {
            watchdog_use = arg_enabled(W_count);
        }

	if (watchdog_use) {
		cl_log(LOG_INFO, "Watchdog enabled.");
	} else {
		cl_log(LOG_INFO, "Watchdog disabled.");
	}

	if (c_count > 0) {
		check_cluster = arg_enabled(c_count);
	}

	if (P_count > 0) {
		int check_pcmk_arg = arg_enabled(P_count);

		if (has_check_pcmk_env && check_pcmk_arg != check_pcmk) {
			cl_log(LOG_WARNING, "Pacemaker integration is %s: "
					"SBD_PACEMAKER=%s is overridden by %s option. "
					"It's recommended to only use SBD_PACEMAKER.",
					check_pcmk_arg? "enabled" : "disabled",
					check_pcmk? "yes" : "no",
					check_pcmk_arg? "-P" : "-PP");
		}
		check_pcmk = check_pcmk_arg;
	}

	if ((disk_count > 0) && (strlen(local_uname) > SECTOR_NAME_MAX)) {
		fprintf(stderr, "Node name mustn't be longer than %d chars.\n",
			SECTOR_NAME_MAX);
		fprintf(stderr, "If uname is longer define a name to be used by sbd.\n");
		exit_status = -1;
		goto out;
	}

	if (disk_count > 3) {
		fprintf(stderr, "You can specify up to 3 devices via the -d option.\n");
		exit_status = -1;
		goto out;
	}

	/* There must at least be one command following the options: */
	if ((argc - optind) < 1) {
		fprintf(stderr, "Not enough arguments.\n");
		exit_status = -2;
		goto out;
	}

	if (init_set_proc_title(argc, argv, envp) < 0) {
		fprintf(stderr, "Allocation of proc title failed.\n");
		exit_status = -1;
		goto out;
	}

	if (timeout_action) {
		char *p[2];
		int i;
		char c;
		int nrflags = sscanf(timeout_action, "%m[a-z],%m[a-z]%c", &p[0], &p[1], &c);
		bool parse_error = (nrflags < 1) || (nrflags > 2);

		for (i = 0; (i < nrflags) && (i < 2); i++) {
			if (!strcmp(p[i], "reboot")) {
				timeout_sysrq_char = 'b';
			} else if (!strcmp(p[i], "crashdump")) {
				timeout_sysrq_char = 'c';
			} else if (!strcmp(p[i], "off")) {
				timeout_sysrq_char = 'o';
			} else if (!strcmp(p[i], "flush")) {
				do_flush = true;
			} else if (!strcmp(p[i], "noflush")) {
				do_flush = false;
			} else {
				parse_error = true;
			}
			free(p[i]);
		}
		if (parse_error) {
			fprintf(stderr, "Failed to parse timeout-action \"%s\".\n",
				timeout_action);
			exit_status = -1;
			goto out;
		}
	}

    if (strcmp(argv[optind], "watch") == 0) {
        value = get_env_option("SBD_SYNC_RESOURCE_STARTUP");
        sync_resource_startup =
            crm_is_true(value?value:SBD_SYNC_RESOURCE_STARTUP_DEFAULT);

#if !USE_PACEMAKERD_API
        if (sync_resource_startup) {
            fprintf(stderr, "Failed to sync resource-startup as "
                "SBD was built against pacemaker not supporting pacemakerd-API.\n");
            exit_status = -1;
            goto out;
        }
#else
        if (check_pcmk && !sync_resource_startup) {
            cl_log(LOG_WARNING, "SBD built against pacemaker supporting "
                             "pacemakerd-API. Should think about enabling "
                             "SBD_SYNC_RESOURCE_STARTUP.");

        } else if (!check_pcmk && sync_resource_startup) {
            fprintf(stderr, "Set SBD_PACEMAKER=yes to allow resource startup syncing. "
                    "Otherwise explicitly set SBD_SYNC_RESOURCE_STARTUP=no if to intentionally disable.\n");
            exit_status = -1;
            goto out;
        }
#endif
    }

#if SUPPORT_SHARED_DISK
	if (strcmp(argv[optind], "create") == 0) {
		exit_status = init_devices(servants_leader);

        } else if (strcmp(argv[optind], "dump") == 0) {
		exit_status = dump_headers(servants_leader);

        } else if (strcmp(argv[optind], "allocate") == 0) {
            exit_status = allocate_slots(argv[optind + 1], servants_leader);

        } else if (strcmp(argv[optind], "list") == 0) {
		exit_status = list_slots(servants_leader);

        } else if (strcmp(argv[optind], "message") == 0) {
            exit_status = messenger(argv[optind + 1], argv[optind + 2], servants_leader);

        } else if (strcmp(argv[optind], "ping") == 0) {
            exit_status = ping_via_slots(argv[optind + 1], servants_leader);

        } else
#endif
        if (strcmp(argv[optind], "query-watchdog") == 0) {
            exit_status = watchdog_info();
        } else if (strcmp(argv[optind], "test-watchdog") == 0) {
            exit_status = watchdog_test();
        } else if (strcmp(argv[optind], "watch") == 0) {
            /* sleep $(sbd $SBD_DEVICE_ARGS dump | grep -m 1 msgwait | awk '{print $4}') 2>/dev/null */

                const char *delay_source = delay ? "SBD_DELAY_START" : "";

#if SUPPORT_SHARED_DISK
                if(disk_count > 0) {
                    /* If no devices are specified, its not an error to be unable to find one */
                    open_any_device(servants_leader);

                    if (delay_start && delay <= 0) {
                        delay = get_first_msgwait(servants_leader);

                        if (delay > 0) {
                            delay_source = "msgwait";
                        } else {
                            cl_log(LOG_WARNING, "No 'msgwait' value from disk, using '2 * watchdog-timeout' for 'delay' starting");
                        }
                    }
                }
#endif
                /* Re-calculate timeout_watchdog_warn based on any timeout_watchdog from:
                 * SBD_WATCHDOG_TIMEOUT, -1 option or on-disk setting read with open_any_device() */
                if (do_calculate_timeout_watchdog_warn) {
                    timeout_watchdog_warn = calculate_timeout_watchdog_warn(timeout_watchdog);
                }

                if (delay_start) {
                    /* diskless mode or disk read issues causing get_first_msgwait() to return a 0 for delay */
                    if (delay <= 0) {
                        delay = 2 * timeout_watchdog;
                        delay_source = "watchdog-timeout * 2";
                    }

                    cl_log(LOG_DEBUG, "Delay start (yes), (delay: %ld), (delay source: %s)", delay, delay_source);

                    sleep((unsigned long) delay);

                } else {
                    cl_log(LOG_DEBUG, "Delay start (no)");
                }

                /* We only want this to have an effect during watch right now;
                 * pinging and fencing would be too confused */
                cl_log(LOG_INFO, "Turning on pacemaker checks: %d", check_pcmk);
                if (check_pcmk) {
                        recruit_servant("pcmk", 0);
#if SUPPORT_PLUGIN
                        check_cluster = 1;
#endif
                }

                cl_log(LOG_INFO, "Turning on cluster checks: %d", check_cluster);
                if (check_cluster) {
                        recruit_servant("cluster", 0);
                }

                cl_log(LOG_NOTICE, "%s flush + write \'%c\' to sysrq in case of timeout",
                       do_flush?"Do":"Skip", timeout_sysrq_char);
                exit_status = inquisitor();
        } else {
            exit_status = -2;
        }
        
  out:
	if (timeout_action) {
				free(timeout_action);
	}
	if (exit_status < 0) {
		if (exit_status == -2) {
			usage();
		} else {
			fprintf(stderr, "sbd failed; please check the logs.\n");
		}
		return (1);
	}
	return (0);
}
