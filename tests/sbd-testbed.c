#define _GNU_SOURCE
#include <stdlib.h>
#include <dlfcn.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/reboot.h>
#include <stdarg.h>
#include <stddef.h>
#include <fcntl.h>
#include <libaio.h>
#include <linux/watchdog.h>
#include <linux/fs.h>
#include <stdio.h>
#include <signal.h>
#include <unistd.h>
#include <glib.h>
#include <errno.h>

#if __GLIBC_PREREQ(2,36)
#include <glib-unix.h>
#else
#include <glib/giochannel.h>

typedef gboolean (*GUnixFDSourceFunc) (gint         fd,
                                       GIOCondition condition,
                                       gpointer     user_data);

static gboolean
GIOFunc2GUnixFDSourceFunc(GIOChannel *source,
            GIOCondition condition,
            gpointer data)
{
    return ((GUnixFDSourceFunc) data) (
        g_io_channel_unix_get_fd(source),
        condition, NULL);
}

static guint
g_unix_fd_add(gint fd,
               GIOCondition condition,
               GUnixFDSourceFunc function,
               gpointer user_data)
{
    GIOChannel *chan = g_io_channel_unix_new (fd);

    if (chan == NULL) {
        return 0;
    } else {
        return g_io_add_watch(chan,
                   condition,
                   GIOFunc2GUnixFDSourceFunc,
                   (gpointer) function);
    }
}
#endif

#define LIBAIO_DOQUOTE(name) #name
#define LIBAIO_QUOTE(name) LIBAIO_DOQUOTE(name)

#define LIBAIO_DEFAULT LIBAIO_QUOTE(libaio.so)

#ifndef LIBAIO_NAME
  #define LIBAIO_QUOTED LIBAIO_DEFAULT
#else
  #define LIBAIO_QUOTED LIBAIO_QUOTE(LIBAIO_NAME)
#endif

typedef int (*orig_open_f_type)(const char *pathname, int flags, ...);
typedef int (*orig_ioctl_f_type)(int fd, unsigned long int request, ...);
typedef ssize_t (*orig_write_f_type)(int fd, const void *buf, size_t count);
typedef int (*orig_close_f_type)(int fd);
typedef FILE *(*orig_fopen_f_type)(const char *pathname, const char *mode);
typedef int (*orig_fclose_f_type)(FILE *fp);
typedef int (*orig_io_setup_f_type)(int nr_events, io_context_t *ctx_idp);
typedef int (*orig_io_destroy_f_type)(io_context_t ctx_id);
typedef int (*orig_io_submit_f_type)(io_context_t ctx_id, long nr, struct iocb *ios[]);
typedef int (*orig_io_getevents_f_type)(io_context_t ctx_id, long min_nr, long nr,
                struct io_event *events, struct timespec *timeout);
typedef int (*orig_io_cancel_f_type)(io_context_t ctx_id, struct iocb *iocb,
                struct io_event *result);

static int is_init = 0;
static FILE *log_fp = NULL;

static char *sbd_device[3] = {NULL, NULL, NULL};
static int sbd_device_fd[3] = {-1, -1, -1};

static FILE *sysrq_fp = NULL;
static FILE *sysrq_trigger_fp = NULL;

static char *watchdog_device = NULL;
static int watchdog_device_fd = -1;
static int watchdog_timeout = -1;
static pid_t watchdog_pid = -1;
static int watchdog_pipe[2] = {-1, -1};
static guint watchdog_source_id = 0;
static int watchdog_timer_id = 0;

static orig_open_f_type orig_open = NULL;
static orig_ioctl_f_type orig_ioctl = NULL;
static orig_write_f_type orig_write = NULL;
static orig_close_f_type orig_close = NULL;
static orig_fopen_f_type orig_fopen = NULL;
static orig_fclose_f_type orig_fclose = NULL;
static orig_io_setup_f_type orig_io_setup = NULL;
static orig_io_destroy_f_type orig_io_destroy = NULL;
static orig_io_submit_f_type orig_io_submit = NULL;
static orig_io_getevents_f_type orig_io_getevents = NULL;
static orig_io_cancel_f_type orig_io_cancel = NULL;

/* fprintf is inlined as __fprintf_chk or
 * we have vfprintf.
 * For fscanf we have vfscanf.
 * For reboot we anyway don't want that to be
 * called in any case.
 */

static struct iocb *pending_iocb = NULL;
struct io_context { int context_num; };
static struct io_context our_io_context = {.context_num = 1};
static int translate_aio = 0;

static GMainLoop *mainloop = NULL;

#if 0
static void
watchdog_shutdown(int nsig)
{
    if (watchdog_timer_id > 0) {
        fprintf(log_fp, "exiting with watchdog-timer armed\n");
    }
}
#endif

static void*
dlsym_fatal(void *handle, const char *symbol)
{
    void *rv = dlsym(handle, symbol);

    if (!rv) {
        fprintf(stderr, "Failed looking up symbol %s\n", symbol);
        exit(1);
    }
    return rv;
}

static void
init (void)
{
    void *handle;

    if (!is_init) {
        const char *value;
        int i;
        char *token, *str, *str_orig;
        const char *libaio = LIBAIO_QUOTED;

        is_init = 1;

        orig_open         = (orig_open_f_type)dlsym_fatal(RTLD_NEXT,"open");
        orig_ioctl        = (orig_ioctl_f_type)dlsym_fatal(RTLD_NEXT,"ioctl");
        orig_close        = (orig_close_f_type)dlsym_fatal(RTLD_NEXT,"close");
        orig_write        = (orig_write_f_type)dlsym_fatal(RTLD_NEXT,"write");
        orig_fopen        = (orig_fopen_f_type)dlsym_fatal(RTLD_NEXT,"fopen");
        orig_fclose       = (orig_fclose_f_type)dlsym_fatal(RTLD_NEXT,"fclose");

        if (libaio == NULL || libaio[0] == '\0') {
            libaio = LIBAIO_DEFAULT;
        }

        handle = dlopen(libaio, RTLD_NOW);
        if (!handle) {
            fprintf(stderr, "Failed opening %s (%s)\n", libaio, dlerror());
            exit(1);
        }
        orig_io_setup     = (orig_io_setup_f_type)dlsym_fatal(handle,"io_setup");
        orig_io_destroy   = (orig_io_destroy_f_type)dlsym_fatal(handle,"io_destroy");
        orig_io_submit    = (orig_io_submit_f_type)dlsym_fatal(handle,"io_submit");
        orig_io_getevents = (orig_io_getevents_f_type)dlsym_fatal(handle,"io_getevents");
        orig_io_cancel    = (orig_io_cancel_f_type)dlsym_fatal(handle,"io_cancel");
        dlclose(handle);

        value = getenv("SBD_PRELOAD_LOG");
        if (value) {
            log_fp = fopen(value, "a");
        } else {
            int fd = dup(fileno(stderr));
            if (fd >= 0) {
                log_fp = fdopen(fd, "w");
            }
        }
        if (log_fp == NULL) {
            fprintf(stderr, "couldn't open log-file\n");
        }

        value = getenv("SBD_WATCHDOG_DEV");
        if (value) {
            watchdog_device = strdup(value);
        }

        value = getenv("SBD_DEVICE");
        if ((value) && (str = str_orig = strdup(value))) {
            for (i = 0; i < 3; i++, str = NULL) {
                token = strtok(str, ";");
                if (token == NULL) {
                    break;
                }
                sbd_device[i] = strdup(token);
            }
            free(str_orig);
        }

        value = getenv("SBD_TRANSLATE_AIO");
        if ((value) && !strcmp(value, "yes")) {
            translate_aio = 1;
        }
    }
}

// ***** end - handling of watchdog & block-devices ****

static gboolean
watchdog_timeout_notify(gpointer data)
{
    fprintf(log_fp, "watchdog fired after %ds - killing process group\n",
            watchdog_timeout);
    fclose(log_fp);
    log_fp = NULL;
    killpg(0, SIGKILL);
    exit(1);
}

static gboolean
watchdog_dispatch_callback (gint fd,
                            GIOCondition condition,
                            gpointer user_data)
{
    char buf[256];
    int i = 0;

    if (condition & G_IO_HUP) {
        return FALSE;
    }
    if (watchdog_timer_id > 0) {
        g_source_remove(watchdog_timer_id);
    }
    watchdog_timer_id = 0;
    for (i = 0; i < sizeof(buf)-1; i++) {
        ssize_t len;

        do {
            len = read(watchdog_pipe[0], &buf[i], 1);
        } while ((len == -1) && (errno == EINTR));
        if (len <= 0) {
            if (len == -1) {
                fprintf(log_fp, "Couldn't read from watchdog-pipe\n");
            }
            buf[i] = '\0';
            break;
        }
        if (buf[i] == '\n') {
            buf[i] = '\0';
            break;
        }
    }
    buf[sizeof(buf)-1] = '\0';
    if (sscanf(buf, "trigger %ds", &watchdog_timeout) == 1) {
        watchdog_timer_id = g_timeout_add(watchdog_timeout * 1000, watchdog_timeout_notify, NULL);
    } else if (strcmp(buf, "disarm") == 0) {
        // timer is stopped already
    } else {
        fprintf(log_fp, "unknown watchdog command\n");
    }
    return TRUE;
}

static void
watchdog_arm (void) {
    char buf[256];

    if ((watchdog_timeout > 0) && (watchdog_pipe[1] >= 0)) {
        sprintf(buf, "trigger %ds\n", watchdog_timeout);
        if (write(watchdog_pipe[1], buf, strlen(buf)) != strlen(buf)) {
            fprintf(log_fp, "Failed tickling watchdog via pipe\n");
        }
    }
}

static void
watchdog_disarm (void) {
    char buf[256];

    watchdog_timeout = -1;
    if (watchdog_pipe[1] >= 0) {
        sprintf(buf, "disarm\n");
        if (write(watchdog_pipe[1], buf, strlen(buf)) != strlen(buf)) {
            fprintf(log_fp, "Failed disarming watchdog via pipe\n");
        }
    }
}

int
open(const char *pathname, int flags, ...)
{
    int i, fd;
    int devnum = -1;
    int is_wd_dev = 0;
    va_list ap;

    init();

    for (i=0; i < 3; i++) {
        if (sbd_device[i]) {
            if (strcmp(sbd_device[i], pathname) == 0) {
                devnum = i;
                flags &= ~O_DIRECT;
                break;
            }
        }
    }
    if (watchdog_device) {
        if (strcmp(watchdog_device, pathname) == 0) {
            is_wd_dev = 1;
            if (watchdog_pipe[1] == -1) {
                if (pipe(watchdog_pipe) == -1) {
                    fprintf(log_fp, "Creating pipe for watchdog failed\n");
                } else {
                    int i;

                    watchdog_pid = fork();
                    switch (watchdog_pid) {
                        case -1:
                            fprintf(log_fp, "Forking watchdog-child failed\n");
                            break;
                        case 0:
                            free(watchdog_device);
                            watchdog_device = NULL;
                            for (i = 0; i < 3; i++) {
                                free(sbd_device[i]);
                                sbd_device[i] = NULL;
                            }
                            close(watchdog_pipe[1]);
                            if (fcntl(watchdog_pipe[0], F_SETFL, O_NONBLOCK) == -1) {
                                // don't block on read for timer to be handled
                                fprintf(log_fp,
                                        "Failed setting watchdog-pipe-read to non-blocking");
                            }
                            mainloop = g_main_loop_new(NULL, FALSE);
                            // mainloop_add_signal(SIGTERM, watchdog_shutdown);
                            // mainloop_add_signal(SIGINT, watchdog_shutdown);
                            watchdog_source_id = g_unix_fd_add(watchdog_pipe[0],
                                                    G_IO_IN,
                                                    watchdog_dispatch_callback,
                                                    NULL);
                            if (watchdog_source_id == 0) {
                                fprintf(log_fp, "Failed creating source for watchdog-pipe\n");
                                exit(1);
                            }
                            g_main_loop_run(mainloop);
                            g_main_loop_unref(mainloop);
                            exit(0);
                        default:
                            close(watchdog_pipe[0]);
                            if (fcntl(watchdog_pipe[1], F_SETFL, O_NONBLOCK) == -1) {
                                fprintf(log_fp,
                                        "Failed setting watchdog-pipe-write to non-blocking");
                            }
                    }
                }
            }
            pathname = "/dev/null";
        }
    }

    va_start (ap, flags);
    fd = (flags & (O_CREAT
#ifdef O_TMPFILE
                   | O_TMPFILE
#endif
                  ))?
             orig_open(pathname, flags, va_arg(ap, mode_t)):
             orig_open(pathname, flags);
    va_end (ap);

    if (devnum >= 0) {
        sbd_device_fd[devnum] = fd;
    } else if (is_wd_dev) {
        watchdog_device_fd = fd;
    }

    return fd;
}

ssize_t
write(int fd, const void *buf, size_t count)
{
    init();

    if ((fd == watchdog_device_fd) && (count >= 1)) {
        if (*(const char *)buf == 'V') {
            watchdog_disarm();
        } else {
            watchdog_arm();
        }
    }

    return orig_write(fd, buf, count);
}

int
ioctl(int fd, unsigned long int request, ...)
{
    int rv = -1;
    va_list ap;
    int i;

    init();

    va_start(ap, request);
    switch (request) {
        case BLKSSZGET:
            for (i=0; i < 3; i++) {
                if (sbd_device_fd[i] == fd) {
                    rv = 0;
                    *(va_arg(ap, int *)) = 512;
                    break;
                }
                if (i == 2) {
                    rv = orig_ioctl(fd, request, va_arg(ap, int *));
                }
            }
            break;
        case WDIOC_SETTIMEOUT:
            if (fd == watchdog_device_fd) {
                watchdog_timeout = *va_arg(ap, int *);

                watchdog_arm();
                rv = 0;
                break;
            }
            rv = orig_ioctl(fd, request, va_arg(ap, int *));
            break;
        case WDIOC_SETOPTIONS:
            if (fd == watchdog_device_fd) {
                int flags = *va_arg(ap, int *);

                if (flags & WDIOS_DISABLECARD) {
                    watchdog_disarm();
                }
                rv = 0;
                break;
            }
            rv = orig_ioctl(fd, request, va_arg(ap, int *));
            break;
        case WDIOC_GETSUPPORT:
            rv = orig_ioctl(fd, request, va_arg(ap, struct watchdog_info *));
            break;
        default:
            fprintf(log_fp, "ioctl using unknown request = 0x%08lx", request);
            rv = orig_ioctl(fd, request, va_arg(ap, void *));
    }
    va_end(ap);

    return rv;
}

int
close(int fd)
{
    int i;

    init();

    if (fd == watchdog_device_fd) {
        watchdog_device_fd = -1;
    } else {
        for (i = 0; i < 3; i++) {
            if (sbd_device_fd[i] == fd) {
                sbd_device_fd[i] = -1;
                break;
            }
        }
    }
    return orig_close(fd);
}

// ***** end - handling of watchdog & block-devices ****

// ***** handling of sysrq, sysrq-trigger & reboot ****

FILE *
fopen(const char *pathname, const char *mode)
{
    int is_sysrq = 0;
    int is_sysrq_trigger = 0;
    FILE *fp;

    init();

    if ((strcmp("/proc/sys/kernel/sysrq", pathname) == 0) &&
        strcmp("w", mode)) {
        pathname = "/dev/null";
        is_sysrq = 1;
    } else if (strcmp("/proc/sysrq-trigger", pathname) == 0) {
        pathname = "/dev/null";
        is_sysrq_trigger = 1;
    }
    fp = orig_fopen(pathname, mode);
    if (is_sysrq) {
        sysrq_fp = fp;
    } else if (is_sysrq_trigger) {
        sysrq_trigger_fp = fp;
    }
    return fp;
}

int
fclose(FILE *fp)
{
    init();

    if (fp == sysrq_fp) {
        sysrq_fp = NULL;
    } else if (fp == sysrq_trigger_fp) {
        sysrq_trigger_fp = NULL;
    }
    return orig_fclose(fp);
}

#if defined(__USE_FORTIFY_LEVEL) && (__USE_FORTIFY_LEVEL > 1)
int
__fprintf_chk(FILE *stream, int flag, const char *format, ...)
#else
int
fprintf(FILE *stream, const char *format, ...)
#endif
{
    va_list ap;
    int rv;

    init();
    va_start (ap, format);
    if (stream == sysrq_trigger_fp) {
        char buf[256];

        rv = vsnprintf(buf, sizeof(buf), format, ap);
        if (rv >= 1) {
            fprintf(log_fp, "sysrq-trigger ('%c') - %s\n", buf[0],
                    (buf[0] == 'c')?"killing process group":"don't kill but wait for reboot-call");
            if (buf[0] == 'c') {
                fclose(log_fp);
                log_fp = NULL;
                killpg(0, SIGKILL);
                exit(1);
            }
        }
    } else {
        rv = vfprintf(stream, format, ap);
    }
    va_end (ap);
    return rv;
}

int
fscanf(FILE *stream, const char *format, ...)
{
    va_list ap;
    int rv;

    init();
    va_start (ap, format);
    rv = vfscanf(stream, format, ap);
    va_end (ap);
    return rv;
}

int
reboot (int __howto)
{
    fprintf(log_fp, "reboot (%s) - exiting inquisitor process\n",
            (__howto == RB_POWER_OFF)?"poweroff":"reboot");
    fclose(log_fp);
    log_fp = NULL;
    killpg(0, SIGKILL);
    exit(1);
}

// ***** end - handling of sysrq, sysrq-trigger & reboot ****

// ***** aio translate ****

#if 0
struct iocb {
    void *data;
    unsigned key;
    short aio_lio_opcode;
    short aio_reqprio;
    int aio_fildes;
};

static inline void io_prep_pread(struct iocb *iocb, int fd, void *buf, size_t count, long long offset)
{
	memset(iocb, 0, sizeof(*iocb));
	iocb->aio_fildes = fd;
	iocb->aio_lio_opcode = IO_CMD_PREAD;
	iocb->aio_reqprio = 0;
	iocb->u.c.buf = buf;
	iocb->u.c.nbytes = count;
	iocb->u.c.offset = offset;
}

static inline void io_prep_pwrite(struct iocb *iocb, int fd, void *buf, size_t count, long long offset)
{
	memset(iocb, 0, sizeof(*iocb));
	iocb->aio_fildes = fd;
	iocb->aio_lio_opcode = IO_CMD_PWRITE;
	iocb->aio_reqprio = 0;
	iocb->u.c.buf = buf;
	iocb->u.c.nbytes = count;
	iocb->u.c.offset = offset;
}
#endif

int io_setup(int nr_events, io_context_t *ctx_idp)
{
    init();

    if (!translate_aio) {
        return orig_io_setup(nr_events, ctx_idp);
    }

    if (nr_events == 0) {
        return EINVAL;
    }
    if (nr_events > 1) {
        return EAGAIN;
    }
    if (ctx_idp == NULL) {
        return EFAULT;
    }
    *ctx_idp = &our_io_context;
    return 0;
}

int io_destroy(io_context_t ctx_id)
{
    init();

    if (!translate_aio) {
        return orig_io_destroy(ctx_id);
    }

    if (ctx_id != &our_io_context) {
        return EINVAL;
    }
    return 0;
}

int io_submit(io_context_t ctx_id, long nr, struct iocb *ios[])
{
    init();

    if (!translate_aio) {
        return orig_io_submit(ctx_id, nr, ios);
    }

    if ((pending_iocb != NULL) ||
        (nr > 1)) {
        return EAGAIN;
    }
    if ((nr == 1) && ((ios == NULL) || (ios[0] == NULL))) {
        return EFAULT;
    }
    if ((ctx_id != &our_io_context) ||
        (nr < 0) ||
        ((nr == 1) &&
         (ios[0]->aio_lio_opcode != IO_CMD_PREAD) &&
         (ios[0]->aio_lio_opcode != IO_CMD_PWRITE))) {
        return EINVAL;
    }
    if ((fcntl(ios[0]->aio_fildes, F_GETFD) == -1) && (errno == EBADF)) {
        return EBADF;
    }
    if (nr == 1) {
        pending_iocb = ios[0];
    }
    return nr;
}

int io_getevents(io_context_t ctx_id, long min_nr, long nr,
                        struct io_event *events, struct timespec *timeout)
{
    init();

    if (!translate_aio) {
        return orig_io_getevents(ctx_id, min_nr, nr, events, timeout);
    }

    if ((ctx_id != &our_io_context) ||
        (min_nr != 1) ||
        (nr != 1)) {
        return EINVAL;
    }
    if (pending_iocb == NULL) {
        return 0;
    }

	switch (pending_iocb->aio_lio_opcode) {
		case IO_CMD_PWRITE:
			events->res = pwrite(pending_iocb->aio_fildes,
								pending_iocb->u.c.buf,
								pending_iocb->u.c.nbytes,
								pending_iocb->u.c.offset);
			break;
		case IO_CMD_PREAD:
			events->res = pread(pending_iocb->aio_fildes,
								pending_iocb->u.c.buf,
								pending_iocb->u.c.nbytes,
								pending_iocb->u.c.offset);
			break;
		default:
			events->res = 0;
	}

    events->data = pending_iocb->data;
    events->obj  = pending_iocb;

    events->res2  = 0;
    pending_iocb = NULL;
    return 1;
}

int io_cancel(io_context_t ctx_id, struct iocb *iocb,
                     struct io_event *result)
{
    init();

    if (!translate_aio) {
        return orig_io_cancel(ctx_id, iocb, result);
    }

    if (ctx_id != &our_io_context) {
        return EINVAL;
    }
    if ((iocb == NULL) || (result == NULL)) {
        return EFAULT;
    }
    if (pending_iocb != iocb) {
        return EAGAIN;
    }
    result->data = iocb->data;
    result->obj  = iocb;
    result->res  = 0;
    result->res2  = 0;
    pending_iocb = NULL;
    return 0;
}

// ***** end - aio translate ****
