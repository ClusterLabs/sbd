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
#include <sys/stat.h>
#include <pwd.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <limits.h>

#ifdef _POSIX_MEMLOCK
#  include <sys/mman.h>
#endif

/* Tunable defaults: */
int  timeout_watchdog           = SBD_WATCHDOG_TIMEOUT_DEFAULT;
int  timeout_msgwait            = 2 * SBD_WATCHDOG_TIMEOUT_DEFAULT;

int  timeout_allocate           = 2;
int  timeout_loop               = 1;
int  timeout_io                 = 3;
int  timeout_startup            = 120;

int  watchdog_use               = 1;
int  watchdog_set_timeout       = 1;
int  timeout_watchdog_crashdump = 0;
int  skip_rt                    = 0;
int  debug                      = 0;
int  debug_mode                 = 0;

/* Global, non-tunable variables: */
int  sector_size    = 0;
int  servant_health = 0;

const char *cmdname;
char *local_uname;

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
"-v|-vv|-vvv	Enable verbose|debug|debug-library logging (optional)\n"
"\n"
"-1 <N>		Set watchdog timeout to N seconds (optional, create only)\n"
"-2 <N>		Set slot allocation timeout to N seconds (optional, create only)\n"
"-3 <N>		Set daemon loop timeout to N seconds (optional, create only)\n"
"-4 <N>		Set msgwait timeout to N seconds (optional, create only)\n"
"-5 <N>		Warn if loop latency exceeds threshold (optional, watch only)\n"
"			(default is 3, set to 0 to disable)\n"
"-C <N>		Watchdog timeout to set before crashdumping\n"
"			(def: 0s = disable gracefully, optional)\n"
"-I <N>		Async IO read timeout (defaults to 3 * loop timeout, optional)\n"
"-s <N>		Timeout to wait for devices to become available (def: 120s)\n"
"-t <N>		Dampening delay before faulty servants are restarted (optional)\n"
"			(default is 5, set to 0 to disable)\n"
"-F <N>		# of failures before a servant is considered faulty (optional)\n"
"			(default is 1, set to 0 to disable)\n"
"-P		Check Pacemaker quorum and node health (optional, watch only)\n"
"-Z		Enable trace mode. WARNING: UNSAFE FOR PRODUCTION!\n"
"-r		Set timeout-action to comma-separated combination of\n"
"		noflush|flush plus reboot|crashdump|off (default is flush,reboot)\n"
"Commands:\n"
#if SUPPORT_SHARED_DISK
"create		initialize N slots on <dev> - OVERWRITES DEVICE!\n"
"list		List all allocated slots on device, and messages.\n"
"dump		Dump meta-data header from device.\n"
"allocate <node>\n"
"		Allocate a slot for node (optional)\n"
"message <node> (test|reset|off|crashdump|clear|exit)\n"
"		Writes the specified message to node's slot.\n"
#endif
"watch		Loop forever, monitoring own slot\n"
"query-watchdog	Check for available watchdog-devices and print some info\n"
"test-watchdog	Test the watchdog-device selected.\n"
"		Attention: This will arm the watchdog and have your system reset\n"
"		           in case your watchdog is working properly!\n"
                , cmdname);
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

static void
sbd_stack_hogger(unsigned char * inbuf, int kbytes)
{
    unsigned char buf[1024];

    if(kbytes <= 0) {
        return;
    }

    if (inbuf == NULL) {
        memset(buf, HOG_CHAR, sizeof(buf));
    } else {
        memcpy(buf, inbuf, sizeof(buf));
    }

    if (kbytes > 0) {
        sbd_stack_hogger(buf, kbytes-1);
    }

    return;
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

static int get_realtime_budget(void)
{
    FILE *f;
    char fname[PATH_MAX];
    int res = -1, lnum = 0, num;
    char *cgroup = NULL, *namespecs = NULL;

    snprintf(fname, PATH_MAX, "/proc/%jd/cgroup", (intmax_t)getpid());
    f = fopen(fname, "rt");
    if (f == NULL) {
        cl_log(LOG_WARNING, "Can't open cgroup file for pid=%jd",
                            (intmax_t)getpid());
        goto exit_res;
    }
    while( (num = fscanf(f, "%d:%m[^:]:%m[^\n]\n", &lnum,
                         &namespecs, &cgroup)) !=EOF ) {
        if (namespecs && strstr(namespecs, "cpuacct")) {
            free(namespecs);
            break;
        }
        if (cgroup) {
            free(cgroup);
            cgroup = NULL;
        }
        if (namespecs) {
            free(namespecs);
            namespecs = NULL;
        }
        /* not to get stuck if format changes */
        if ((num < 3) && ((fscanf(f, "%*[^\n]") == EOF) ||
            (fscanf(f, "\n") == EOF))) {
            break;
        }
    }
    fclose(f);
    if (cgroup == NULL) {
        cl_log(LOG_WARNING, "Failed getting cgroup for pid=%jd",
                            (intmax_t)getpid());
        goto exit_res;
    }
    snprintf(fname, PATH_MAX, "/sys/fs/cgroup/cpu%s/cpu.rt_runtime_us",
                              cgroup);
    f = fopen(fname, "rt");
    if (f == NULL) {
        cl_log(LOG_WARNING, "cpu.rt_runtime_us existed for root-slice but "
            "doesn't for '%s'", cgroup);
        goto exit_res;
    }
    if (fscanf(f, "%d", &res) != 1) {
        cl_log(LOG_WARNING, "failed reading rt-budget from %s", fname);
    } else {
        cl_log(LOG_INFO, "slice='%s' has rt-budget=%d", cgroup, res);
    }
    fclose(f);

exit_res:
    if (cgroup) {
        free(cgroup);
    }
    return res;
}

/* stolen from corosync */
static int sbd_move_to_root_cgroup(bool enforce_root_cgroup) {
    FILE *f;
    int res = -1;

    /*
     * /sys/fs/cgroup is hardcoded, because most of Linux distributions are now
     * using systemd and systemd uses hardcoded path of cgroup mount point.
     *
     * This feature is expected to be removed as soon as systemd gets support
     * for managing RT configuration.
     */
    f = fopen("/sys/fs/cgroup/cpu/cpu.rt_runtime_us", "rt");
    if (f == NULL) {
        cl_log(LOG_DEBUG, "cpu.rt_runtime_us doesn't exist -> "
            "system without cgroup or with disabled CONFIG_RT_GROUP_SCHED");
        res = 0;
        goto exit_res;
    }
    fclose(f);

    if ((!enforce_root_cgroup) && (get_realtime_budget() > 0)) {
        cl_log(LOG_DEBUG, "looks as if we have rt-budget in the slice we are "
                          "-> skip moving to root-slice");
        res = 0;
        goto exit_res;
    }

    f = fopen("/sys/fs/cgroup/cpu/tasks", "w");
    if (f == NULL) {
        cl_log(LOG_WARNING, "Can't open cgroups tasks file for writing");

        goto exit_res;
    }

    if (fprintf(f, "%jd\n", (intmax_t)getpid()) <= 0) {
        cl_log(LOG_WARNING, "Can't write sbd pid into cgroups tasks file");
        goto close_and_exit_res;
    }

close_and_exit_res:
    if (fclose(f) != 0) {
        cl_log(LOG_WARNING, "Can't close cgroups tasks file");
        goto exit_res;
    }

exit_res:
    return (res);
}

void
sbd_make_realtime(int priority, int stackgrowK, int heapgrowK)
{
    if(priority < 0) {
        return;
    }

do {
#ifdef SCHED_RR
    if (move_to_root_cgroup) {
        sbd_move_to_root_cgroup(enforce_moving_to_root_cgroup);
    }

    {
        int pmin = sched_get_priority_min(SCHED_RR);
        int pmax = sched_get_priority_max(SCHED_RR);
        struct sched_param sp;
        int pcurrent;

        if (priority == 0) {
            priority = pmax;
        } else if (priority < pmin) {
            priority = pmin;
        } else if (priority > pmax) {
            priority = pmax;
        }

        if (sched_getparam(0, &sp) < 0) {
            cl_perror("Unable to get scheduler priority");

        } else if ((pcurrent = sched_getscheduler(0)) < 0) {
            cl_perror("Unable to get scheduler policy");

        } else if ((pcurrent == SCHED_RR) &&
                   (sp.sched_priority >= priority)) {
                cl_log(LOG_INFO,
                       "Stay with priority (%d) for policy SCHED_RR",
                       sp.sched_priority);
                break;
        } else {
            memset(&sp, 0, sizeof(sp));
            sp.sched_priority = priority;

            if (sched_setscheduler(0, SCHED_RR, &sp) < 0) {
                cl_perror(
                    "Unable to set scheduler policy to SCHED_RR priority %d",
                    priority);
            } else {
                cl_log(LOG_INFO,
                       "Scheduler policy is now SCHED_RR priority %d",
                       priority);
                break;
            }
        }
    }
#else
    cl_log(LOG_ERR, "System does not support updating the scheduler policy");
#endif
#ifdef PRIO_PGRP
    if (setpriority(PRIO_PGRP, 0, INT_MIN) < 0) {
        cl_perror("Unable to raise the scheduler priority");
    } else {
        cl_log(LOG_INFO, "Scheduler priority raised to the maximum");
	}
#else
    cl_perror("System does not support setting the scheduler priority");
#endif
} while (0);

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
do_exit(char kind, bool do_flush)
{
    /* TODO: Turn debug_mode into a bit field? Delay + kdump for example */
    const char *reason = NULL;

    if (kind == 'c') {
        cl_log(LOG_NOTICE, "Initiating kdump");

    } else if (debug_mode == 1) {
        cl_log(LOG_WARNING, "Initiating kdump instead of panicking the node (debug mode)");
        kind = 'c';
    }

    if (debug_mode == 2) {
        cl_log(LOG_WARNING, "Shutting down SBD instead of panicking the node (debug mode)");
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
    if (do_flush) {
        sync();
    }

    if (kind == 'c') {
        if (timeout_watchdog_crashdump) {
            if (timeout_watchdog != timeout_watchdog_crashdump) {
                timeout_watchdog = timeout_watchdog_crashdump;
                watchdog_init_interval();
            }
            watchdog_close(false);
        } else {
            watchdog_close(true);
        }
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
    do_exit('c', true);
}

void
do_reset(void)
{
    do_exit('b', true);
}

void
do_off(void)
{
    do_exit('o', true);
}

void
do_timeout_action(void)
{
	do_exit(timeout_sysrq_char, do_flush);
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

void
sbd_detach(void)
{
    const char *devnull = "/dev/null";

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
}

pid_t
make_daemon(void)
{
	pid_t			pid;

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
	sbd_detach();

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

int sigqueue_zero(pid_t pid, int sig)
{
union sigval signal_value;

    memset(&signal_value, 0, sizeof(signal_value));

    return sigqueue(pid, sig, signal_value);
}

void
notify_parent(void)
{
    pid_t		ppid;

    ppid = getppid();

    if (ppid == 1) {
        /* Our parent died unexpectedly. Triggering
         * self-fence. */
        cl_log(LOG_WARNING, "Our parent is dead.");
        do_timeout_action();
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
            sigqueue_zero(ppid, SIG_PCMK_UNHEALTHY);
            break;

        case pcmk_health_online:
            DBGLOG(LOG_DEBUG, "Notifying parent: healthy");
            sigqueue_zero(ppid, SIG_LIVENESS);
            break;

        default:
            DBGLOG(LOG_WARNING, "Notifying parent: UNHEALTHY %d", servant_health);
            sigqueue_zero(ppid, SIG_PCMK_UNHEALTHY);
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

#define MAX_LEGITIMATE_AGE 3600 /* 1h should be plenty */

int
seconds_diff_time_t(time_t a, time_t b)
{
    long long diff;

    diff = a - b;

    if ((diff > -MAX_LEGITIMATE_AGE) && (diff < MAX_LEGITIMATE_AGE)) {
        return (int) diff;
    }

    DBGLOG(LOG_WARNING, "Detected unreasonable age (%lld)", diff);
    return MAX_LEGITIMATE_AGE; /* something is fishy - provoke timeout */
}

int
seconds_diff_timespec(struct timespec *a, struct timespec *b)
{
    struct timeval diff;
    struct timeval a_tv;
    struct timeval b_tv;

    TIMESPEC_TO_TIMEVAL(&a_tv, a);
    TIMESPEC_TO_TIMEVAL(&b_tv, b);

    timersub(&a_tv, &b_tv, &diff);

    return seconds_diff_time_t(diff.tv_sec, 0);
}
