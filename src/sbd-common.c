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

#include "sbd.h"
#include <sys/reboot.h>
#include <sys/types.h>
#ifdef __GLIBC__
#include <sys/sysmacros.h>
#endif
#include <sys/stat.h>
#include <pwd.h>
#include <unistd.h>
#include <dirent.h>

#ifdef _POSIX_MEMLOCK
#  include <sys/mman.h>
#endif

/* Tunable defaults: */
#if  defined(__s390__) || defined(__s390x__)
unsigned long	timeout_watchdog 	= 15;
int		timeout_msgwait		= 30;
#else
unsigned long	timeout_watchdog 	= 5;
int		timeout_msgwait		= 10;
#endif
unsigned long	timeout_watchdog_warn 	= 3;
int		timeout_allocate 	= 2;
int		timeout_loop	    	= 1;
int		timeout_io		= 3;
int		timeout_startup		= 120;

int	watchdog_use		= 1;
int	watchdog_set_timeout	= 1;
unsigned long	timeout_watchdog_crashdump = 240;
int	skip_rt			= 0;
int	debug			= 0;
int	debug_mode		= 0;
char *watchdogdev		= NULL;
bool watchdogdev_is_default = false;
char *	local_uname;

/* Global, non-tunable variables: */
int	sector_size		= 0;
int	watchdogfd 		= -1;
int     servant_health          = 0;

/*const char	*devname;*/
const char	*cmdname;

void
usage(void)
{
	fprintf(stderr,
"Shared storage fencing tool.\n"
"Syntax:\n"
"	%s <options> <command> <cmdarguments>\n"
"Options:\n"
"-1 <N>		Set watchdog timeout to N seconds (optional, create only)\n"
"-2 <N>		Set slot allocation timeout to N seconds (optional, create only)\n"
"-3 <N>		Set daemon loop timeout to N seconds (optional, create only)\n"
"-4 <N>		Set msgwait timeout to N seconds (optional, create only)\n"
"-5 <N>		Warn if loop latency exceeds threshold (optional, watch only)\n"
"			(default is 3, set to 0 to disable)\n"
"-C <N>		Watchdog timeout to set before crashdumping (def: 240s, optional)\n"
"-d <devname>	Block device to use (mandatory; can be specified up to 3 times)\n"
"-F <N>		# of failures before a servant is considered faulty (optional)\n"
"			(default is 1, set to 0 to disable)\n"
"-h		Display this help.\n"
"-I <N>		Async IO read timeout (defaults to 3 * loop timeout, optional)\n"
"-n <node>	Set local node name; defaults to uname -n (optional)\n"
"\n"
"-P		Check Pacemaker quorum and node health (optional, watch only)\n"
"-p <path>	Write pidfile to the specified path (watch only)\n"
"-R		Do NOT enable realtime priority (debugging only)\n"
"-S <0|1>	Set start mode if the node was previously fenced (watch only)\n"
"-s <N>		Timeout to wait for devices to become available (def: 120s)\n"
"-T		Do NOT initialize the watchdog timeout (watch only)\n"
"-t <N>		Dampening delay before faulty servants are restarted (optional)\n"
"			(default is 5, set to 0 to disable)\n"
"-v		Enable some verbose debug logging (optional)\n"
"-W		Use watchdog (recommended) (watch only)\n"
"-w <dev>	Specify watchdog device (optional) (watch only)\n"
"\n"
"-Z		Enable trace mode. WARNING: UNSAFE FOR PRODUCTION!\n"
"Commands:\n"
#if SUPPORT_SHARED_DISK
"create		initialize N slots on <dev> - OVERWRITES DEVICE!\n"
"list		List all allocated slots on device, and messages.\n"
"dump		Dump meta-data header from device.\n"
"allocate <node>\n"
"		Allocate a slot for node (optional)\n"
"message <node> (test|reset|off|clear|exit)\n"
"		Writes the specified message to node's slot.\n"
#endif
"watch		Loop forever, monitoring own slot\n"
"query-watchdog	Check for available watchdog-devices and print some info\n"
"test-watchdog	Test the watchdog-device selected.\n"
"		Attention: This will arm the watchdog and have your system reset\n"
"		           in case your watchdog is working properly!\n"
                , cmdname);
}

static int
watchdog_init_interval_fd(int wdfd, int timeout)
{
	if (ioctl(wdfd, WDIOC_SETTIMEOUT, &timeout) < 0) {
		cl_perror( "WDIOC_SETTIMEOUT"
				": Failed to set watchdog timer to %u seconds.",
				timeout);
		cl_log(LOG_CRIT, "Please validate your watchdog configuration!");
		cl_log(LOG_CRIT, "Choose a different watchdog driver or specify -T to skip this if you are completely sure.");
		return -1;
	}
	return 0;
}

int
watchdog_init_interval(void)
{
	if (watchdogfd < 0) {
		return 0;
	}

	if (watchdog_set_timeout == 0) {
		cl_log(LOG_INFO, "NOT setting watchdog timeout on explicit user request!");
		return 0;
	}

	if (watchdog_init_interval_fd(watchdogfd, timeout_watchdog) < 0) {
		return -1;
	}
	cl_log(LOG_INFO, "Set watchdog timeout to %u seconds.", (int) timeout_watchdog);
	return 0;
}

static int
watchdog_tickle_fd(int wdfd, char *wddev)
{
	if (write(wdfd, "", 1) != 1) {
			cl_perror("Watchdog write failure: %s!", wddev);
			return -1;
		}
	return 0;
}

int
watchdog_tickle(void)
{
	if (watchdogfd >= 0) {
		return watchdog_tickle_fd(watchdogfd, watchdogdev);
	}
	return 0;
}

static int
watchdog_init_fd(char *wddev, int timeout)
{
	int wdfd;

	wdfd = open(wddev, O_WRONLY);
	if (wdfd >= 0) {
		if (((timeout >= 0) && (watchdog_init_interval_fd(wdfd, timeout) < 0))
					|| (watchdog_tickle_fd(wdfd, wddev) < 0)) {
			close(wdfd);
			return -1;
		}
	} else {
		cl_perror("Cannot open watchdog device '%s'", wddev);
		return -1;
	}
	return wdfd;
}

int
watchdog_init(void)
{
	if (watchdogfd < 0 && watchdogdev != NULL) {
		int timeout = timeout_watchdog;

		if (watchdog_set_timeout == 0) {
			cl_log(LOG_INFO, "NOT setting watchdog timeout on explicit user request!");
			timeout = -1;
		}
		watchdogfd = watchdog_init_fd(watchdogdev, timeout);
		if (watchdogfd >= 0) {
			cl_log(LOG_NOTICE, "Using watchdog device '%s'", watchdogdev);
			if (watchdog_set_timeout) {
				cl_log(LOG_INFO, "Set watchdog timeout to %u seconds.", (int) timeout_watchdog);
			}
		} else {
			return -1;
		}
	}
	return 0;
}

static void
watchdog_close_fd(int wdfd, char *wddev, bool disarm)
{
    if (disarm) {
        int r;
        int flags = WDIOS_DISABLECARD;;

        /* Explicitly disarm it */
        r = ioctl(wdfd, WDIOC_SETOPTIONS, &flags);
        if (r < 0) {
            cl_perror("Failed to disable hardware watchdog %s", wddev);
        }

        /* To be sure, use magic close logic, too */
        for (;;) {
            if (write(wdfd, "V", 1) > 0) {
                break;
            }
            cl_perror("Cannot disable watchdog device %s", wddev);
        }
    }

    if (close(wdfd) < 0) {
        cl_perror("Watchdog close(%d) failed", wdfd);
    }
}

void
watchdog_close(bool disarm)
{
    if (watchdogfd < 0) {
        return;
    }

    watchdog_close_fd(watchdogfd, watchdogdev, disarm);
    watchdogfd = -1;
}

#define MAX_WATCHDOGS 64
#define SYS_CLASS_WATCHDOG "/sys/class/watchdog"
#define SYS_CHAR_DEV_DIR "/sys/dev/char"
#define WATCHDOG_NODEDIR "/dev"

struct watchdog_list_item {
	dev_t dev;
	char *dev_node;
	char *dev_ident;
	char *dev_driver;
	struct watchdog_list_item *next;
};

static struct watchdog_list_item *watchdog_list = NULL;
static int watchdog_list_items = 0;

static void
watchdog_populate_list(void)
{
	dev_t watchdogs[MAX_WATCHDOGS + 1] =
		{makedev(10,130), 0};
	int num_watchdogs = 1;
	struct dirent *entry;
	char entry_name[280];
	DIR *dp;
	char buf[256] = "";

	if (watchdog_list != NULL) {
		return;
	}

	/* get additional devices from /sys/class/watchdog */
	dp = opendir(SYS_CLASS_WATCHDOG);
	if (dp) {
		while ((entry = readdir(dp))) {
			if (entry->d_type == DT_LNK) {
				FILE *file;

				snprintf(entry_name, sizeof(entry_name),
						SYS_CLASS_WATCHDOG "/%s/dev", entry->d_name);
				file = fopen(entry_name, "r");
				if (file) {
					int major, minor;

					if (fscanf(file, "%d:%d", &major, &minor) == 2) {
						watchdogs[num_watchdogs++] = makedev(major, minor);
					}
					fclose(file);
					if (num_watchdogs == MAX_WATCHDOGS) {
						break;
					}
				}
			}
		}
		closedir(dp);
	}

	/* search for watchdog nodes in /dev */
	dp = opendir(WATCHDOG_NODEDIR);
	if (dp) {
		while ((entry = readdir(dp))) {
			if ((entry->d_type == DT_CHR) || (entry->d_type == DT_LNK)) {
				struct stat statbuf;

				snprintf(entry_name, sizeof(entry_name),
						WATCHDOG_NODEDIR "/%s", entry->d_name);
				if(!stat(entry_name, &statbuf) && S_ISCHR(statbuf.st_mode)) {
					int i;

					for (i=0; i<num_watchdogs; i++) {
						if (statbuf.st_rdev == watchdogs[i]) {
							int wdfd = watchdog_init_fd(entry_name, -1);
							struct watchdog_list_item *wdg =
									calloc(1, sizeof(struct watchdog_list_item));

							wdg->dev = watchdogs[i];
							wdg->dev_node = strdup(entry_name);
							wdg->next = watchdog_list;
							watchdog_list = wdg;
							watchdog_list_items++;

							if (wdfd >= 0) {
								struct watchdog_info ident;

								ident.identity[0] = '\0';
								ioctl(wdfd, WDIOC_GETSUPPORT, &ident);
								watchdog_close_fd(wdfd, entry_name, true);
								if (ident.identity[0]) {
									wdg->dev_ident = strdup((char *) ident.identity);
								}
							}

							snprintf(entry_name, sizeof(entry_name),
								SYS_CHAR_DEV_DIR "/%d:%d/device/driver",
								major(watchdogs[i]), minor(watchdogs[i]));
							if (readlink(entry_name, buf, sizeof(buf)) > 0) {
								wdg->dev_driver = strdup(basename(buf));
							} else if ((wdg->dev_ident) &&
										(strcmp(wdg->dev_ident,
												"Software Watchdog") == 0)) {
								wdg->dev_driver = strdup("softdog");
							}
							break;
						}
					}
				}
			}
		}
		closedir(dp);
	}
}

int watchdog_info(void)
{
	struct watchdog_list_item *wdg;
	int wdg_cnt = 0;

	watchdog_populate_list();
	printf("\nDiscovered %d watchdog devices:\n", watchdog_list_items);
	for (wdg = watchdog_list; wdg != NULL; wdg = wdg->next) {
		wdg_cnt++;
		printf("\n[%d] %s\nIdentity: %s\nDriver: %s\n",
				wdg_cnt, wdg->dev_node,
				wdg->dev_ident?wdg->dev_ident:"Error: Check if hogged by e.g. sbd-daemon!",
				wdg->dev_driver?wdg->dev_driver:"<unknown>");
		if ((wdg->dev_driver) && (strcmp(wdg->dev_driver, "softdog") == 0)) {
			printf("CAUTION: Not recommended for use with sbd.\n"); 
		}
	}

	return 0;
}

int watchdog_test(void)
{
	int i;

	if ((watchdog_set_timeout == 0) || !watchdog_use) {
		printf("\nWatchdog is disabled - aborting test!!!\n");
		return 0;
	}
	if (watchdogdev_is_default) {
		watchdog_populate_list();
		if (watchdog_list_items > 1) {
			printf("\nError: Multiple watchdog devices discovered.\n"
				   "       Use -w <watchdog> or SBD_WATCHDOG_DEV to specify\n"
				   "       which device to reset the system with\n");
			watchdog_info();
			return -1;
		}
	}
	if ((isatty(fileno(stdin)))) {
		char buffer[16];
		printf("\nWARNING: This operation is expected to force-reboot this system\n"
			   "         without following any shutdown procedures.\n\n"
			   "Proceed? [NO/Proceed] ");

		if ((fgets(buffer, 16, stdin) == NULL) ||
			strcmp(buffer, "Proceed\n")) {
			printf("\nAborting watchdog test!!!\n");
			return 0;
		}
		printf("\n");
	}
	printf("Initializing %s with a reset countdown of %d seconds ...\n",
		watchdogdev, (int) timeout_watchdog);
	if ((watchdog_init() < 0) || (watchdog_init_interval() < 0)) {
		printf("Failed to initialize watchdog!!!\n");
		return -1;
	}
	printf("\n");
	printf("NOTICE: The watchdog device is expected to reset the system\n"
		   "        in %d seconds.  If system remains active beyond that time,\n"
		   "        watchdog may not be functional.\n\n", (int) timeout_watchdog);
	for (i=timeout_watchdog; i>1; i--) {
		printf("Reset countdown ... %d seconds\n", i);
		sleep(1);
	}
	for (i=2; i>0; i--) {
		printf("System expected to reset any moment ...\n");
		sleep(1);
	}
	for (i=5; i>0; i--) {
		printf("System should have reset ...\n");
		sleep(1);
	}
	printf("Error: The watchdog device has failed to reboot the system,\n"
		   "       and it may not be suitable for usage with sbd.\n");

	/* test should trigger a reboot thus returning is actually bad */
	return -1;
}

/* This duplicates some code from linux/ioprio.h since these are not included
 * even in linux-kernel-headers. Sucks. See also
 * /usr/src/linux/Documentation/block/ioprio.txt and ioprio_set(2) */
extern int sys_ioprio_set(int, int, int);
int ioprio_set(int which, int who, int ioprio);
inline int ioprio_set(int which, int who, int ioprio)
{
        return syscall(__NR_ioprio_set, which, who, ioprio);
}

enum {
        IOPRIO_CLASS_NONE,
        IOPRIO_CLASS_RT,
        IOPRIO_CLASS_BE,
        IOPRIO_CLASS_IDLE,
};

enum {
        IOPRIO_WHO_PROCESS = 1,
        IOPRIO_WHO_PGRP,
        IOPRIO_WHO_USER,
};

#define IOPRIO_BITS             (16)
#define IOPRIO_CLASS_SHIFT      (13)
#define IOPRIO_PRIO_MASK        ((1UL << IOPRIO_CLASS_SHIFT) - 1)

#define IOPRIO_PRIO_CLASS(mask) ((mask) >> IOPRIO_CLASS_SHIFT)
#define IOPRIO_PRIO_DATA(mask)  ((mask) & IOPRIO_PRIO_MASK)
#define IOPRIO_PRIO_VALUE(class, data)  (((class) << IOPRIO_CLASS_SHIFT) | data)

static unsigned char
sbd_stack_hogger(unsigned char * inbuf, int kbytes)
{
    unsigned char buf[1024];

    if(kbytes <= 0) {
        return HOG_CHAR;
    }

    if (inbuf == NULL) {
        memset(buf, HOG_CHAR, sizeof(buf));
    } else {
        memcpy(buf, inbuf, sizeof(buf));
    }

    if (kbytes > 0) {
        return sbd_stack_hogger(buf, kbytes-1);
    } else {
        return buf[sizeof(buf)-1];
    }
}

static void
sbd_malloc_hogger(int kbytes)
{
    int	j;
    void**chunks;
    int	 chunksize = 1024;

    if(kbytes <= 0) {
        return;
    }

    /*
     * We could call mallopt(M_MMAP_MAX, 0) to disable it completely,
     * but we've already called mlockall()
     *
     * We could also call mallopt(M_TRIM_THRESHOLD, -1) to prevent malloc
     * from giving memory back to the system, but we've already called
     * mlockall(MCL_FUTURE), so there's no need.
     */

    chunks = malloc(kbytes * sizeof(void *));
    if (chunks == NULL) {
        cl_log(LOG_WARNING, "Could not preallocate chunk array");
        return;
    }

    for (j=0; j < kbytes; ++j) {
        chunks[j] = malloc(chunksize);
        if (chunks[j] == NULL) {
            cl_log(LOG_WARNING, "Could not preallocate block %d", j);

        } else {
            memset(chunks[j], 0, chunksize);
        }
    }

    for (j=0; j < kbytes; ++j) {
        free(chunks[j]);
    }

    free(chunks);
}

static void sbd_memlock(int stackgrowK, int heapgrowK) 
{

#ifdef _POSIX_MEMLOCK
    /*
     * We could call setrlimit(RLIMIT_MEMLOCK,...) with a large
     * number, but the mcp runs as root and mlock(2) says:
     *
     * Since Linux 2.6.9, no limits are placed on the amount of memory
     * that a privileged process may lock, and this limit instead
     * governs the amount of memory that an unprivileged process may
     * lock.
     */
    if (mlockall(MCL_CURRENT|MCL_FUTURE) >= 0) {
        cl_log(LOG_INFO, "Locked ourselves in memory");

        /* Now allocate some extra pages (MCL_FUTURE will ensure they stay around) */
        sbd_malloc_hogger(heapgrowK);
        sbd_stack_hogger(NULL, stackgrowK);

    } else {
        cl_perror("Unable to lock ourselves into memory");
    }

#else
    cl_log(LOG_ERR, "Unable to lock ourselves into memory");
#endif
}

void
sbd_make_realtime(int priority, int stackgrowK, int heapgrowK)
{
    if(priority < 0) {
        return;
    }

#ifdef SCHED_RR
    {
        int pcurrent = 0;
        int pmin = sched_get_priority_min(SCHED_RR);
        int pmax = sched_get_priority_max(SCHED_RR);

        if (priority == 0) {
            priority = pmax;
        } else if (priority < pmin) {
            priority = pmin;
        } else if (priority > pmax) {
            priority = pmax;
        }

        pcurrent = sched_getscheduler(0);
        if (pcurrent < 0) {
            cl_perror("Unable to get scheduler priority");

        } else if(pcurrent < priority) {
            struct sched_param sp;

            memset(&sp, 0, sizeof(sp));
            sp.sched_priority = priority;

            if (sched_setscheduler(0, SCHED_RR, &sp) < 0) {
                cl_perror("Unable to set scheduler priority to %d", priority);
            } else {
                cl_log(LOG_INFO, "Scheduler priority is now %d", priority);
            }
        }
    }
#else
    cl_log(LOG_ERR, "System does not support updating the scheduler priority");
#endif

    sbd_memlock(heapgrowK, stackgrowK);
}

void
maximize_priority(void)
{
	if (skip_rt) {
		cl_log(LOG_INFO, "Not elevating to realtime (-R specified).");
		return;
	}

        sbd_make_realtime(0, 256, 256);

	if (ioprio_set(IOPRIO_WHO_PROCESS, getpid(),
			IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 1)) != 0) {
		cl_perror("ioprio_set() call failed.");
	}
}

void
sysrq_init(void)
{
	FILE* procf;
	int c;
	procf = fopen("/proc/sys/kernel/sysrq", "r");
	if (!procf) {
		cl_perror("cannot open /proc/sys/kernel/sysrq for read.");
		return;
	}
	if (fscanf(procf, "%d", &c) != 1) {
		cl_perror("Parsing sysrq failed");
		c = 0;
	}
	fclose(procf);
	if (c == 1)
		return;
	/* 8 for debugging dumps of processes, 
	   128 for reboot/poweroff */
	c |= 136; 
	procf = fopen("/proc/sys/kernel/sysrq", "w");
	if (!procf) {
		cl_perror("cannot open /proc/sys/kernel/sysrq for writing");
		return;
	}
	fprintf(procf, "%d", c);
	fclose(procf);
	return;
}

void
sysrq_trigger(char t)
{
	FILE *procf;

	procf = fopen("/proc/sysrq-trigger", "a");
	if (!procf) {
		cl_perror("Opening sysrq-trigger failed.");
		return;
	}
	cl_log(LOG_INFO, "sysrq-trigger: %c\n", t);
	fprintf(procf, "%c\n", t);
	fclose(procf);
	return;
}


static void
do_exit(char kind) 
{
    /* TODO: Turn debug_mode into a bit field? Delay + kdump for example */
    const char *reason = NULL;

    if (kind == 'c') {
        cl_log(LOG_NOTICE, "Initiating kdump");

    } else if (debug_mode == 1) {
        cl_log(LOG_WARNING, "Initiating kdump instead of panicing the node (debug mode)");
        kind = 'c';
    }

    if (debug_mode == 2) {
        cl_log(LOG_WARNING, "Shutting down SBD instead of panicing the node (debug mode)");
        watchdog_close(true);
        exit(0);
    }

    if (debug_mode == 3) {
        /* Give the system some time to flush logs to disk before rebooting. */
        cl_log(LOG_WARNING, "Delaying node panic by 10s (debug mode)");

        watchdog_close(true);
        sync();

        sleep(10);
    }

    switch(kind) {
        case 'b':
            reason = "reboot";
            break;
        case 'c':
            reason = "crashdump";
            break;
        case 'o':
            reason = "off";
            break;
        default:
            reason = "unknown";
            break;
    }

    cl_log(LOG_EMERG, "Rebooting system: %s", reason);
    sync();

    if(kind == 'c') {
        watchdog_close(true);
        sysrq_trigger(kind);

    } else {
        watchdog_close(false);
        sysrq_trigger(kind);
        if (reboot((kind == 'o')?RB_POWER_OFF:RB_AUTOBOOT) < 0) {
            cl_perror("%s failed", (kind == 'o')?"Poweroff":"Reboot");
        }
    }

    exit(1);
}

void
do_crashdump(void)
{
    do_exit('c');
}

void
do_reset(void)
{
    do_exit('b');
}

void
do_off(void)
{
    do_exit('o');
}

/*
 * Change directory to the directory our core file needs to go in
 * Call after you establish the userid you're running under.
 */
int
sbd_cdtocoredir(void)
{
	int		rc;
	static const char *dir = NULL;

	if (dir == NULL) {
		dir = CRM_CORE_DIR;
	}
	if ((rc=chdir(dir)) < 0) {
		int errsave = errno;
		cl_perror("Cannot chdir to [%s]", dir);
		errno = errsave;
	}
	return rc;
}

pid_t
make_daemon(void)
{
	pid_t			pid;
	const char *		devnull = "/dev/null";

	pid = fork();
	if (pid < 0) {
		cl_log(LOG_ERR, "%s: could not start daemon\n",
				cmdname);
		cl_perror("fork");
		exit(1);
	}else if (pid > 0) {
		return pid;
	}

        qb_log_ctl(QB_LOG_STDERR, QB_LOG_CONF_ENABLED, QB_FALSE);

	/* This is the child; ensure privileges have not been lost. */
	maximize_priority();
	sysrq_init();

	umask(022);
	close(0);
	(void)open(devnull, O_RDONLY);
	close(1);
	(void)open(devnull, O_WRONLY);
	close(2);
	(void)open(devnull, O_WRONLY);
	sbd_cdtocoredir();
	return 0;
}

void
sbd_get_uname(void)
{
	struct utsname		uname_buf;
	int i;

	if (uname(&uname_buf) < 0) {
		cl_perror("uname() failed?");
		exit(1);
	}

	local_uname = strdup(uname_buf.nodename);

	for (i = 0; i < strlen(local_uname); i++)
		local_uname[i] = tolower(local_uname[i]);
}


#define FMT_MAX 256
void
sbd_set_format_string(int method, const char *daemon)
{
    int offset = 0;
    char fmt[FMT_MAX];
    struct utsname res;

    switch(method) {
        case QB_LOG_STDERR:
            break;

        case QB_LOG_SYSLOG:
            if(daemon && strcmp(daemon, "sbd") != 0) {
                offset += snprintf(fmt + offset, FMT_MAX - offset, "%10s: ", daemon);
            }
            break;

        default:
            /* When logging to a file */
            if (uname(&res) == 0) {
                offset +=
                    snprintf(fmt + offset, FMT_MAX - offset, "%%t [%d] %s %10s: ", getpid(),
                             res.nodename, daemon);
            } else {
                offset += snprintf(fmt + offset, FMT_MAX - offset, "%%t [%d] %10s: ", getpid(), daemon);
            }
    }

    if (debug && method >= QB_LOG_STDERR) {
        offset += snprintf(fmt + offset, FMT_MAX - offset, "(%%-12f:%%5l %%g) %%-7p: %%n: ");
    } else {
        offset += snprintf(fmt + offset, FMT_MAX - offset, "%%g %%-7p: %%n: ");
    }

    if (method == QB_LOG_SYSLOG) {
        offset += snprintf(fmt + offset, FMT_MAX - offset, "%%b");
    } else {
        offset += snprintf(fmt + offset, FMT_MAX - offset, "\t%%b");
    }

    if(offset > 0) {
        qb_log_format_set(method, fmt);
    }
}

void
notify_parent(void)
{
    pid_t		ppid;
    union sigval	signal_value;

    memset(&signal_value, 0, sizeof(signal_value));
    ppid = getppid();

    if (ppid == 1) {
        /* Our parent died unexpectedly. Triggering
         * self-fence. */
        cl_log(LOG_WARNING, "Our parent is dead.");
        do_reset();
    }

    switch (servant_health) {
        case pcmk_health_pending:
        case pcmk_health_shutdown:
        case pcmk_health_transient:
            DBGLOG(LOG_DEBUG, "Not notifying parent: state transient (%d)", servant_health);
            break;

        case pcmk_health_unknown:
        case pcmk_health_unclean:
        case pcmk_health_noquorum:
            DBGLOG(LOG_WARNING, "Notifying parent: UNHEALTHY (%d)", servant_health);
            sigqueue(ppid, SIG_PCMK_UNHEALTHY, signal_value);
            break;

        case pcmk_health_online:
            DBGLOG(LOG_DEBUG, "Notifying parent: healthy");
            sigqueue(ppid, SIG_LIVENESS, signal_value);
            break;

        default:
            DBGLOG(LOG_WARNING, "Notifying parent: UNHEALTHY %d", servant_health);
            sigqueue(ppid, SIG_PCMK_UNHEALTHY, signal_value);
            break;
    }
}

void
set_servant_health(enum pcmk_health state, int level, char const *format, ...)
{
    if (servant_health != state) {
        va_list ap;
        int len = 0;
        char *string = NULL;

        servant_health = state;

        va_start(ap, format);
        len = vasprintf (&string, format, ap);

        if(len > 0) {
            cl_log(level, "%s", string);
        }
        
        va_end(ap);
        free(string);
    }
}

bool
sbd_is_disk(struct servants_list_item *servant)
{
    if ((servant != NULL) &&
        (servant->devname != NULL) &&
        (servant->devname[0] == '/')) {
        return true;
    }
    return false;
}

bool
sbd_is_cluster(struct servants_list_item *servant)
{
    if ((servant != NULL) &&
        (servant->devname != NULL) &&
        (strcmp("cluster", servant->devname) == 0)) {
        return true;
    }
    return false;
}

bool
sbd_is_pcmk(struct servants_list_item *servant)
{
    if ((servant != NULL) &&
        (servant->devname != NULL) &&
        (strcmp("pcmk", servant->devname) == 0)) {
        return true;
    }
    return false;
}
