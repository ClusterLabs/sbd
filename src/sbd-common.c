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
#include <pwd.h>

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
"-d <devname>	Block device to use (mandatory; can be specified up to 3 times)\n"
"-h		Display this help.\n"
"-n <node>	Set local node name; defaults to uname -n (optional)\n"
"\n"
"-R		Do NOT enable realtime priority (debugging only)\n"
"-W		Use watchdog (recommended) (watch only)\n"
"-w <dev>	Specify watchdog device (optional) (watch only)\n"
"-T		Do NOT initialize the watchdog timeout (watch only)\n"
"-S <0|1>	Set start mode if the node was previously fenced (watch only)\n"
"-p <path>	Write pidfile to the specified path (watch only)\n"
"-v		Enable some verbose debug logging (optional)\n"
"\n"
"-1 <N>		Set watchdog timeout to N seconds (optional, create only)\n"
"-2 <N>		Set slot allocation timeout to N seconds (optional, create only)\n"
"-3 <N>		Set daemon loop timeout to N seconds (optional, create only)\n"
"-4 <N>		Set msgwait timeout to N seconds (optional, create only)\n"
"-5 <N>		Warn if loop latency exceeds threshold (optional, watch only)\n"
"			(default is 3, set to 0 to disable)\n"
"-C <N>		Watchdog timeout to set before crashdumping (def: 240s, optional)\n"
"-I <N>		Async IO read timeout (defaults to 3 * loop timeout, optional)\n"
"-s <N>		Timeout to wait for devices to become available (def: 120s)\n"
"-t <N>		Dampening delay before faulty servants are restarted (optional)\n"
"			(default is 5, set to 0 to disable)\n"
"-F <N>		# of failures before a servant is considered faulty (optional)\n"
"			(default is 1, set to 0 to disable)\n"
"-A		Enable start delay (wait for msgwait seconds at start) (optional)\n"
"-P		Check Pacemaker quorum and node health (optional, watch only)\n"
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
                , cmdname);
}

int
watchdog_init_interval(void)
{
	int     timeout = timeout_watchdog;

	if (watchdogfd < 0) {
		return 0;
	}


	if (watchdog_set_timeout == 0) {
		cl_log(LOG_INFO, "NOT setting watchdog timeout on explicit user request!");
		return 0;
	}

	if (ioctl(watchdogfd, WDIOC_SETTIMEOUT, &timeout) < 0) {
		cl_perror( "WDIOC_SETTIMEOUT"
				": Failed to set watchdog timer to %u seconds.",
				timeout);
		cl_log(LOG_CRIT, "Please validate your watchdog configuration!");
		cl_log(LOG_CRIT, "Choose a different watchdog driver or specify -T to skip this if you are completely sure.");
		return -1;
	} else {
		cl_log(LOG_INFO, "Set watchdog timeout to %u seconds.",
				timeout);
	}
	return 0;
}

int
watchdog_tickle(void)
{
	if (watchdogfd >= 0) {
		if (write(watchdogfd, "", 1) != 1) {
			cl_perror("Watchdog write failure: %s!",
					watchdogdev);
			return -1;
		}
	}
	return 0;
}

int
watchdog_init(void)
{
	if (watchdogfd < 0 && watchdogdev != NULL) {
		watchdogfd = open(watchdogdev, O_WRONLY);
		if (watchdogfd >= 0) {
			cl_log(LOG_NOTICE, "Using watchdog device '%s'", watchdogdev);
			if ((watchdog_init_interval() < 0)
					|| (watchdog_tickle() < 0)) {
				return -1;
			}
		}else{
			cl_perror("Cannot open watchdog device '%s'", watchdogdev);
			return -1;
		}
	}
	return 0;
}

void
watchdog_close(bool disarm)
{
    if (watchdogfd < 0) {
        return;
    }

    if (disarm) {
        int r;
        int flags = WDIOS_DISABLECARD;;

        /* Explicitly disarm it */
        r = ioctl(watchdogfd, WDIOC_SETOPTIONS, &flags);
        if (r < 0) {
            cl_perror("Failed to disable hardware watchdog %s", watchdogdev);
        }

        /* To be sure, use magic close logic, too */
        for (;;) {
            if (write(watchdogfd, "V", 1) > 0) {
                break;
            }
            cl_perror("Cannot disable watchdog device %s", watchdogdev);
        }
    }

    if (close(watchdogfd) < 0) {
        cl_perror("Watchdog close(%d) failed", watchdogfd);
    }

    watchdogfd = -1;
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
        if(reboot(RB_AUTOBOOT) < 0) {
            cl_perror("Reboot failed");
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
            DBGLOG(LOG_INFO, "Not notifying parent: state transient (%d)", servant_health);
            break;

        case pcmk_health_unknown:
        case pcmk_health_unclean:
        case pcmk_health_noquorum:
            DBGLOG(LOG_WARNING, "Notifying parent: UNHEALTHY (%d)", servant_health);
            sigqueue(ppid, SIG_PCMK_UNHEALTHY, signal_value);
            break;

        case pcmk_health_online:
            DBGLOG(LOG_INFO, "Notifying parent: healthy");
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
