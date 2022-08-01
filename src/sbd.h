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

#include <arpa/inet.h>
#include <asm/unistd.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <libaio.h>
#include <linux/fs.h>
#include <linux/types.h>
#include <linux/watchdog.h>
#include <malloc.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/ptrace.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <syslog.h>
#include <time.h>
#include <unistd.h>
#include <uuid/uuid.h>
#include <qb/qblog.h>
#include <crm_config.h>
#include <config.h>
#include <crm/common/mainloop.h>

/* signals reserved for multi-disk sbd */
#define SIG_LIVENESS (SIGRTMIN + 1)	/* report liveness of the disk */
#define SIG_EXITREQ  (SIGRTMIN + 2)	/* exit request to inquisitor */
#define SIG_TEST     (SIGRTMIN + 3)	/* trigger self test */
#define SIG_RESTART  (SIGRTMIN + 4)	/* trigger restart of all failed disk */
#define SIG_PCMK_UNHEALTHY  (SIGRTMIN + 5)
/* FIXME: should add dynamic check of SIG_XX >= SIGRTMAX */

/* exit status for disk-servant */
#define EXIT_MD_SERVANT_IO_FAIL             20
#define EXIT_MD_SERVANT_REQUEST_RESET       21
#define EXIT_MD_SERVANT_REQUEST_SHUTOFF     22
#define EXIT_MD_SERVANT_REQUEST_CRASHDUMP   23

/* exit status for pcmk-servant */
#define EXIT_PCMK_SERVANT_GRACEFUL_SHUTDOWN 30

#define HOG_CHAR	0xff
#define SECTOR_NAME_MAX 63

/* Sector data types */
struct sector_header_s {
	char	magic[8];
	unsigned char	version;
	unsigned char	slots;
	/* Caveat: stored in network byte-order */
	uint32_t	sector_size;
	uint32_t	timeout_watchdog;
	uint32_t	timeout_allocate;
	uint32_t	timeout_loop;
	uint32_t	timeout_msgwait;
	/* Minor version for extensions to the core data set:
	 * compatible and optional values. */
	unsigned char	minor_version;
	uuid_t		uuid; /* 16 bytes */
};

struct sector_mbox_s {
	signed char	cmd;
	char		from[SECTOR_NAME_MAX+1];
};

struct sector_node_s {
	/* slots will be created with in_use == 0 */
	char	in_use;
	char 	name[SECTOR_NAME_MAX+1];
};

struct servants_list_item {
	const char* devname;
	pid_t pid;
	int restarts;
	int restart_blocked;
	int outdated;
	int first_start;
	struct timespec t_last, t_started;
	struct servants_list_item *next;

	const char *command;
	int timeout;
	int rc;
	int synchronous;

	char *stdout_data;
	char *stderr_data;

	int stdout_fd;
	int stderr_fd;
	mainloop_io_t *stdout_gsource;
	mainloop_io_t *stderr_gsource;
};

struct sbd_context {
	int	devfd;
	io_context_t	ioctx;
	struct iocb	io;
	void *buffer;
};

enum pcmk_health 
{
    pcmk_health_unknown,
    pcmk_health_pending,
    pcmk_health_transient,
    pcmk_health_unclean,
    pcmk_health_shutdown,
    pcmk_health_online,
    pcmk_health_noquorum,
};

void usage(void);
int watchdog_init_interval(void);
int watchdog_tickle(void);
int watchdog_init(void);
void sysrq_init(void);
void watchdog_close(bool disarm);
int watchdog_info(void);
int watchdog_test(void);
void sysrq_trigger(char t);
void do_crashdump(void);
void do_reset(void);
void do_off(void);
void do_timeout_action(void);
pid_t make_daemon(void);
void maximize_priority(void);
void sbd_get_uname(void);
void sbd_set_format_string(int method, const char *daemon);
void notify_parent(void);

/* Tunable defaults: */
extern unsigned long    timeout_watchdog;
extern unsigned long    timeout_watchdog_warn;
extern bool             do_calculate_timeout_watchdog_warn;
extern unsigned long    timeout_watchdog_crashdump;
extern int      timeout_allocate;
extern int      timeout_loop;
extern int      timeout_msgwait;
extern int      timeout_io;
extern int      timeout_startup;
extern int  watchdog_use;
extern int  watchdog_set_timeout;
extern int  skip_rt;
extern int  debug;
extern int  debug_mode;
extern char *watchdogdev;
extern bool watchdogdev_is_default;
extern char*  local_uname;
extern bool do_flush;
extern char timeout_sysrq_char;
extern bool move_to_root_cgroup;
extern bool enforce_moving_to_root_cgroup;
extern bool sync_resource_startup;

/* Global, non-tunable variables: */
extern int  sector_size;
extern int  watchdogfd;
extern const char* cmdname;

typedef int (*functionp_t)(const char* devname, int mode, const void* argp);

int assign_servant(const char* devname, functionp_t functionp, int mode, const void* argp);
int assign_servant_with_pipes(struct servants_list_item *servant,
                              functionp_t functionp, int mode, const void *argp);

#if SUPPORT_SHARED_DISK
void open_any_device(struct servants_list_item *servants);
int init_devices(struct servants_list_item *servants);
int allocate_slots(const char *name, struct servants_list_item *servants);
int list_slots(struct servants_list_item *servants);
int ping_via_slots(const char *name, struct servants_list_item *servants);
int query_devices(struct servants_list_item *servants, const char *command);
unsigned long get_first_msgwait(struct servants_list_item *servants);
int messenger(const char *name, const char *msg, struct servants_list_item *servants);
int servant_md(const char *diskname, int mode, const void* argp);
#endif

int servant_pcmk(const char *diskname, int mode, const void* argp);
int servant_cluster(const char *diskname, int mode, const void* argp);

struct servants_list_item *lookup_servant_by_dev(const char *devname);
struct servants_list_item *lookup_servant_by_pid(pid_t pid);

int init_set_proc_title(int argc, char *argv[], char *envp[]);
void set_proc_title(const char *fmt,...);

#define cl_log(level, fmt, args...) qb_log_from_external_source( __func__, __FILE__, fmt, level, __LINE__, 0, ##args)

#  define cl_perror(fmt, args...) do {                                  \
	const char *err = strerror(errno);				\
	cl_log(LOG_ERR, fmt ": %s (%d)", ##args, err, errno);		\
    } while(0)

#define DBGLOG(lvl, fmt, args...) do {           \
	if (debug > 0) cl_log(lvl, fmt, ##args); \
	} while(0)

extern int servant_health;
void set_servant_health(enum pcmk_health state, int level, char const *format, ...) __attribute__ ((__format__ (__printf__, 3, 4)));

bool sbd_is_disk(struct servants_list_item *servant);
bool sbd_is_pcmk(struct servants_list_item *servant);
bool sbd_is_cluster(struct servants_list_item *servant);

#define calculate_timeout_watchdog_warn(timeout) \
	(timeout < 5 ? 2 : \
	(timeout < (ULONG_MAX / 3) ? \
	(((unsigned long) timeout) * 3 / 5) : (((unsigned long) timeout) / 5 * 3)))
