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
#ifdef __linux__
#include <sys/sysmacros.h>
#endif
/* Musl-specific: basename is in libgen.h, and musl lacks __GLIBC__ */
#ifndef __GLIBC__
#include <libgen.h>
#endif
#include <dirent.h>
#include <limits.h>

/* possibly tunable defaults regarding watchdog operation
   are found in sbd-common.c
 */

/* Global, non-tunable variables: */
int  watchdogfd                         = -1;
char *watchdogdev                       = NULL;
bool watchdogdev_is_default             = false;
bool do_calculate_timeout_watchdog_warn = true;
int  timeout_watchdog_warn =
        calculate_timeout_watchdog_warn(SBD_WATCHDOG_TIMEOUT_DEFAULT);

#define MAX_WATCHDOGS 64
#define SYS_CLASS_WATCHDOG "/sys/class/watchdog"
#define SYS_CHAR_DEV_DIR "/sys/dev/char"
#define WATCHDOG_NODEDIR "/dev/"

static bool
is_watchdog(dev_t device)
{
    static int num_watchdog_devs = 0;
    static dev_t watchdog_devs[MAX_WATCHDOGS];
    struct dirent *entry;
    int i;

    /* populate on first call */
    if (num_watchdog_devs == 0) {
        DIR *dp;

        watchdog_devs[0] = makedev(10,130);
        num_watchdog_devs = 1;

        /* get additional devices from /sys/class/watchdog */
        dp = opendir(SYS_CLASS_WATCHDOG);
        if (dp) {
            while ((entry = readdir(dp))) {
                if (entry->d_type == DT_LNK) {
                    FILE *file;
                    char entry_name[NAME_MAX+sizeof(SYS_CLASS_WATCHDOG)+5];

                    snprintf(entry_name, sizeof(entry_name),
                             SYS_CLASS_WATCHDOG "/%s/dev", entry->d_name);
                    file = fopen(entry_name, "r");
                    if (file) {
                        int major, minor;

                        if (fscanf(file, "%d:%d", &major, &minor) == 2) {
                            watchdog_devs[num_watchdog_devs++] =
                                makedev(major, minor);
                        }
                        fclose(file);
                        if (num_watchdog_devs == MAX_WATCHDOGS) {
                            break;
                        }
                    }
                }
            }
            closedir(dp);
        }
    }

    for (i=0; i < num_watchdog_devs; i++) {
        if (device == watchdog_devs[i]) {
            return true;
        }
    }
    return false;
}

static int
watchdog_init_interval_fd(int wdfd, int timeout)
{
    if (ioctl(wdfd, WDIOC_SETTIMEOUT, &timeout) < 0) {
        cl_perror( "WDIOC_SETTIMEOUT"
                   ": Failed to set watchdog timer to %d seconds.",
                   timeout);
        cl_log(LOG_CRIT, "Please validate your watchdog configuration!");
        cl_log(LOG_CRIT, "Choose a different watchdog driver or specify "
                         "-T to skip this if you are completely sure.");
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
        cl_log(LOG_INFO,
               "NOT setting watchdog timeout on explicit user request!");
        return 0;
    }

    if (watchdog_init_interval_fd(watchdogfd, timeout_watchdog) < 0) {
        return -1;
    }
    cl_log(LOG_INFO, "Set watchdog timeout to %d seconds.", timeout_watchdog);
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
        if (((timeout >= 0) &&
             (watchdog_init_interval_fd(wdfd, timeout) < 0)) ||
            (watchdog_tickle_fd(wdfd, wddev) < 0)) {
            close(wdfd);
            return -1;
        }
    } else {
        struct stat statbuf;

        if(!stat(wddev, &statbuf) && S_ISCHR(statbuf.st_mode) &&
           is_watchdog(statbuf.st_rdev)) {
            cl_perror("Cannot open watchdog device '%s'", wddev);
        } else {
            cl_perror("Seems as if '%s' isn't a valid watchdog-device", wddev);
        }
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
            cl_log(LOG_INFO,
                   "NOT setting watchdog timeout on explicit user request!");
            timeout = -1;
        }
        watchdogfd = watchdog_init_fd(watchdogdev, timeout);
        if (watchdogfd >= 0) {
            cl_log(LOG_NOTICE, "Using watchdog device '%s'", watchdogdev);
            if (watchdog_set_timeout) {
                cl_log(LOG_INFO, "Set watchdog timeout to %d seconds.",
                       timeout_watchdog);
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

struct watchdog_list_item {
    dev_t dev;
    char *dev_node;
    char *dev_ident;
    char *dev_driver;
    pid_t busy_pid;
    char *busy_name;
    struct watchdog_list_item *next;
};

struct link_list_item {
    char *dev_node;
    char *link_name;
    struct link_list_item *next;
};

static struct watchdog_list_item *watchdog_list = NULL;
static int watchdog_list_items = 0;

static void
watchdog_populate_list(void)
{
    struct dirent *entry;
    char entry_name[sizeof(WATCHDOG_NODEDIR)+NAME_MAX];
    DIR *dp;
    char buf[NAME_MAX+sizeof(WATCHDOG_NODEDIR)] = "";
    struct link_list_item *link_list = NULL;

    if (watchdog_list != NULL) {
        return;
    }

    /* search for watchdog nodes in /dev */
    dp = opendir(WATCHDOG_NODEDIR);
    if (dp) {
        /* first go for links and memorize them */
        while ((entry = readdir(dp))) {
            if (entry->d_type == DT_LNK) {
                int len;

                snprintf(entry_name, sizeof(entry_name),
                         WATCHDOG_NODEDIR "%s", entry->d_name);

                /* realpath(entry_name, buf) unfortunately does a stat on
                 * target so we can't really use it to check if links stay
                 * within /dev without triggering e.g. AVC-logs (with
                 * SELinux policy that just allows stat within /dev).
                 * Without canonicalization that doesn't actually touch the
                 * filesystem easily available introduce some limitations
                 * for simplicity:
                 * - just simple path without '..'
                 * - just one level of symlinks (avoid e.g. loop-checking)
                 */
                len = readlink(entry_name, buf, sizeof(buf) - 1);
                if ((len < 1) ||
                    (len > sizeof(buf) - sizeof(WATCHDOG_NODEDIR) -1 - 1)) {
                    continue;
                }
                buf[len] = '\0';
                if (buf[0] != '/') {
                    memmove(&buf[sizeof(WATCHDOG_NODEDIR)-1], buf, len+1);
                    memcpy(buf, WATCHDOG_NODEDIR, sizeof(WATCHDOG_NODEDIR)-1);
                    len += sizeof(WATCHDOG_NODEDIR)-1;
                }
                if (strstr(buf, "/../") ||
                    strncmp(WATCHDOG_NODEDIR, buf,
                            sizeof(WATCHDOG_NODEDIR)-1)) {
                    continue;
                } else {
                    /* just memorize to avoid statting the target - SELinux */
                    struct link_list_item *lli =
                        calloc(1, sizeof(struct link_list_item));

                    if (lli == NULL) {
                        break;
                    }
                    lli->dev_node = strdup(buf);
                    lli->link_name = strdup(entry_name);
                    if ((lli->dev_node == NULL) || (lli->link_name == NULL)) {
                        free(lli->dev_node);
                        free(lli->link_name);
                        free(lli);
                        break;
                    }
                    lli->next = link_list;
                    link_list = lli;
                }
            }
        }

        rewinddir(dp);

        while ((entry = readdir(dp))) {
            if (entry->d_type == DT_CHR) {
                struct stat statbuf;

                snprintf(entry_name, sizeof(entry_name),
                            WATCHDOG_NODEDIR "%s", entry->d_name);
                if(!stat(entry_name, &statbuf) && S_ISCHR(statbuf.st_mode) &&
                   is_watchdog(statbuf.st_rdev)) {

                    int wdfd;
                    struct watchdog_list_item *wdg =
                        calloc(1, sizeof(struct watchdog_list_item));
                    int len;
                    struct link_list_item *tmp_list = NULL;

                    if (wdg == NULL) {
                        break;
                    }

                    wdg->dev = statbuf.st_rdev;
                    wdg->dev_node = strdup(entry_name);
                    if (wdg->dev_node == NULL) {
                        free(wdg);
                        break;
                    }
                    wdg->next = watchdog_list;
                    watchdog_list = wdg;
                    watchdog_list_items++;

                    wdfd = watchdog_init_fd(entry_name, -1);
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
                                major(wdg->dev), minor(wdg->dev));
                    len = readlink(entry_name, buf, sizeof(buf) - 1);
                    if (len > 0) {
                        buf[len] = '\0';
                        wdg->dev_driver = strdup(basename(buf));
                    } else if ((wdg->dev_ident) &&
                               (strcmp(wdg->dev_ident,
                                       "Software Watchdog") == 0)) {
                        wdg->dev_driver = strdup("softdog");
                    }

                    /* create dupes if we have memorized links
                     * to this node
                     */
                    for (tmp_list = link_list; tmp_list;
                            tmp_list = tmp_list->next) {
                        if (!strcmp(tmp_list->dev_node,
                                    wdg->dev_node)) {
                            struct watchdog_list_item *dupe_wdg =
                                calloc(1, sizeof(struct watchdog_list_item));

                            if (dupe_wdg == NULL) {
                                break;
                            }
                            /* as long as we never purge watchdog_list
                             * there is no need to dupe strings
                             */
                            *dupe_wdg = *wdg;
                            dupe_wdg->dev_node = strdup(tmp_list->link_name);
                            if (dupe_wdg->dev_node == NULL) {
                                free(dupe_wdg);
                                break;
                            }
                            dupe_wdg->next = watchdog_list;
                            watchdog_list = dupe_wdg;
                            watchdog_list_items++;
                        }
                        /* for performance reasons we could remove
                         * the link_list entry
                         */
                    }
                }
            }
        }

        closedir(dp);
    }

    /* cleanup link list */
    while (link_list) {
        struct link_list_item *tmp_list = link_list;

        link_list = link_list->next;
        free(tmp_list->dev_node);
        free(tmp_list->link_name);
        free(tmp_list);
    }
}

static void
watchdog_checkbusy()
{
    DIR *dproc;
    struct dirent *entry;

    dproc = opendir("/proc");
    if (!dproc) {
        /* no proc directory to search through */
        return;
    }

    while ((entry = readdir(dproc)) != NULL) {
        pid_t local_pid;
        char *leftover;
        DIR *dpid;
        char procpath[NAME_MAX+10] = { 0 };

        if (entry->d_name[0] == '.') {
            continue;
        }

        local_pid = strtol(entry->d_name, &leftover, 10);
        if (leftover[0] != '\0')
            continue;

        snprintf(procpath, sizeof(procpath), "/proc/%s/fd", entry->d_name);
        dpid = opendir(procpath);
        if (!dpid) {
            /* silently continue - might be just a race */
            continue;
        }
        while ((entry = readdir(dpid)) != NULL) {
            struct watchdog_list_item *wdg;
            char entry_name[sizeof(procpath)+NAME_MAX+1] = { 0 };
            char buf[NAME_MAX+1] = { 0 };
            int len;

            if (entry->d_type != DT_LNK) {
                continue;
            }
            snprintf(entry_name, sizeof(entry_name),
                     "%s/%s", procpath, entry->d_name);
            len = readlink(entry_name, buf, sizeof(buf) - 1);
            if (len < 1) {
                continue;
            }
            buf[len] = '\0';
            for (wdg = watchdog_list; wdg != NULL; wdg = wdg->next) {
                if (!strcmp(buf, wdg->dev_node)) {
                    char name[16];
                    FILE *file;

                    wdg->busy_pid = local_pid;
                    snprintf(procpath, sizeof(procpath), "/proc/%d/status",
                             local_pid);
                    file = fopen(procpath, "r");
                    if (file) {
                        if (fscanf(file, "Name:\t%15[a-zA-Z0-9 _-]",
                                   name) == 1) {
                            wdg->busy_name = strdup(name);
                        }
                        fclose(file);
                    }
                }
            }
        }
        closedir(dpid);
    }

    closedir(dproc);

    return;
}

int watchdog_info(void)
{
    struct watchdog_list_item *wdg;
    int wdg_cnt = 0;

    watchdog_populate_list();
    watchdog_checkbusy();
    printf("\nDiscovered %d watchdog devices:\n", watchdog_list_items);
    for (wdg = watchdog_list; wdg != NULL; wdg = wdg->next) {
        wdg_cnt++;
        if (wdg->busy_pid) {
            printf("\n[%d] %s\nIdentity: Busy: PID %d (%s)\nDriver: %s\n",
                wdg_cnt, wdg->dev_node,
                wdg->busy_pid,
                wdg->busy_name?wdg->busy_name:"<unknown>",
                wdg->dev_driver?wdg->dev_driver:"<unknown>");
        } else {
            printf("\n[%d] %s\nIdentity: %s\nDriver: %s\n",
                wdg_cnt, wdg->dev_node,
                wdg->dev_ident?wdg->dev_ident:
                    "Error: device hogged via alias major/minor?",
                wdg->dev_driver?wdg->dev_driver:"<unknown>");
        }
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
            printf("\nError: Multiple watchdog devices discovered."
                   "\n       Use -w <watchdog> or SBD_WATCHDOG_DEV to specify"
                   "\n       which device to reset the system with\n");
            watchdog_info();
            return -1;
        }
    }
    if ((isatty(fileno(stdin)))) {
        char buffer[16];
        printf("\n");
        printf(
            "WARNING: This operation is expected to force-reboot this system\n"
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
        watchdog_info();
        return -1;
    }
    printf("\n");
    printf(
        "NOTICE: The watchdog device is expected to reset the system\n"
        "        in %d seconds.  If system remains active beyond that time,\n"
        "        watchdog may not be functional.\n\n", timeout_watchdog);
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
