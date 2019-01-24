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

#include <assert.h>

#include "sbd.h"

#define SBD_MSG_EMPTY	0x00
#define SBD_MSG_TEST	0x01
#define SBD_MSG_RESET	0x02
#define SBD_MSG_OFF	0x03
#define SBD_MSG_EXIT	0x04
#define SBD_MSG_CRASHDUMP	0x05

#define SLOT_TO_SECTOR(slot) (1+slot*2)
#define MBOX_TO_SECTOR(mbox) (2+mbox*2)

extern int disk_count;

/* These have to match the values in the header of the partition */
static char		sbd_magic[8] = "SBD_SBD_";
static char		sbd_version  = 0x02;

struct slot_msg_arg_t {
	const char* name;
	const char* msg;
};

static signed char
cmd2char(const char *cmd)
{
	if (strcmp("clear", cmd) == 0) {
		return SBD_MSG_EMPTY;
	} else if (strcmp("test", cmd) == 0) {
		return SBD_MSG_TEST;
	} else if (strcmp("reset", cmd) == 0) {
		return SBD_MSG_RESET;
	} else if (strcmp("off", cmd) == 0) {
		return SBD_MSG_OFF;
	} else if (strcmp("exit", cmd) == 0) {
		return SBD_MSG_EXIT;
	} else if (strcmp("crashdump", cmd) == 0) {
		return SBD_MSG_CRASHDUMP;
	}
	return -1;
}

static const char*
char2cmd(const char cmd)
{
	switch (cmd) {
		case SBD_MSG_EMPTY:
			return "clear";
			break;
		case SBD_MSG_TEST:
			return "test";
			break;
		case SBD_MSG_RESET:
			return "reset";
			break;
		case SBD_MSG_OFF:
			return "off";
			break;
		case SBD_MSG_EXIT:
			return "exit";
			break;
		case SBD_MSG_CRASHDUMP:
			return "crashdump";
			break;
		default:
			return "undefined";
			break;
	}
}

static void
close_device(struct sbd_context *st)
{
	close(st->devfd);
	free(st);
}

static struct sbd_context *
open_device(const char* devname, int loglevel)
{
	struct sbd_context *st;

	if (!devname)
		return NULL;

	st = malloc(sizeof(struct sbd_context));
	if (!st)
		return NULL;
	memset(st, 0, sizeof(struct sbd_context));

	if (io_setup(1, &st->ioctx) != 0) {
		cl_perror("io_setup failed");
		free(st);
		return NULL;
	}
	
	st->devfd = open(devname, O_SYNC|O_RDWR|O_DIRECT);

	if (st->devfd == -1) {
		if (loglevel == LOG_DEBUG) {
			DBGLOG(loglevel, "Opening device %s failed.", devname);
		} else {
			cl_log(loglevel, "Opening device %s failed.", devname);
		}
		free(st);
		return NULL;
	}

	ioctl(st->devfd, BLKSSZGET, &sector_size);

	if (sector_size == 0) {
		cl_perror("Get sector size failed.\n");
		close_device(st);
		return NULL;
	}

	return st;
}

static void *
sector_alloc(void)
{
	void *x;

	x = valloc(sector_size);
	if (!x) {
		exit(1);
	}
	memset(x, 0, sector_size);

	return x;
}

static int
sector_io(struct sbd_context *st, int sector, void *data, int rw)
{
	struct timespec	timeout;
	struct io_event event;
	struct iocb	*ios[1] = { &st->io };
	long		r;

	timeout.tv_sec  = timeout_io;
	timeout.tv_nsec = 0;

	memset(&st->io, 0, sizeof(struct iocb));
	if (rw) {
		io_prep_pwrite(&st->io, st->devfd, data, sector_size, sector_size * sector);
	} else {
		io_prep_pread(&st->io, st->devfd, data, sector_size, sector_size * sector);
	}

	if (io_submit(st->ioctx, 1, ios) != 1) {
		cl_log(LOG_ERR, "Failed to submit IO request! (rw=%d)", rw);
		return -1;
	}

	errno = 0;
	r = io_getevents(st->ioctx, 1L, 1L, &event, &timeout);

	if (r < 0 ) {
		cl_log(LOG_ERR, "Failed to retrieve IO events (rw=%d)", rw);
		return -1;
	} else if (r < 1L) {
		cl_log(LOG_INFO, "Cancelling IO request due to timeout (rw=%d)", rw);
		r = io_cancel(st->ioctx, ios[0], &event);
		if (r) {
			DBGLOG(LOG_INFO, "Could not cancel IO request (rw=%d)", rw);
			/* Doesn't really matter, debugging information.
			 */
		}
		return -1;
	} else if (r > 1L) {
		cl_log(LOG_ERR, "More than one IO was returned (r=%ld)", r);
		return -1;
	}

	
	/* IO is happy */
	if (event.res == sector_size) {
		return 0;
	} else {
		cl_log(LOG_ERR, "Short IO (rw=%d, res=%lu, sector_size=%d)",
				rw, event.res, sector_size);
		return -1;
	}
}

static int
sector_write(struct sbd_context *st, int sector, void *data)
{
	return sector_io(st, sector, data, 1);
}

static int
sector_read(struct sbd_context *st, int sector, void *data)
{
	return sector_io(st, sector, data, 0);
}

static int
slot_read(struct sbd_context *st, int slot, struct sector_node_s *s_node)
{
	return sector_read(st, SLOT_TO_SECTOR(slot), s_node);
}

static int
slot_write(struct sbd_context *st, int slot, struct sector_node_s *s_node)
{
	return sector_write(st, SLOT_TO_SECTOR(slot), s_node);
}

static int
mbox_write(struct sbd_context *st, int mbox, struct sector_mbox_s *s_mbox)
{
	return sector_write(st, MBOX_TO_SECTOR(mbox), s_mbox);
}

static int
mbox_read(struct sbd_context *st, int mbox, struct sector_mbox_s *s_mbox)
{
	return sector_read(st, MBOX_TO_SECTOR(mbox), s_mbox);
}

static int
mbox_write_verify(struct sbd_context *st, int mbox, struct sector_mbox_s *s_mbox)
{
	void *data;
	int rc = 0;

	if (sector_write(st, MBOX_TO_SECTOR(mbox), s_mbox) < 0)
		return -1;

	data = sector_alloc();
	if (sector_read(st, MBOX_TO_SECTOR(mbox), data) < 0) {
		rc = -1;
		goto out;
	}


	if (memcmp(s_mbox, data, sector_size) != 0) {
		cl_log(LOG_ERR, "Write verification failed!");
		rc = -1;
		goto out;
	}
	rc = 0;
out:
	free(data);
	return rc;
}

static int header_write(struct sbd_context *st, struct sector_header_s *s_header)
{
	s_header->sector_size = htonl(s_header->sector_size);
	s_header->timeout_watchdog = htonl(s_header->timeout_watchdog);
	s_header->timeout_allocate = htonl(s_header->timeout_allocate);
	s_header->timeout_loop = htonl(s_header->timeout_loop);
	s_header->timeout_msgwait = htonl(s_header->timeout_msgwait);
	return sector_write(st, 0, s_header);
}

static int
header_read(struct sbd_context *st, struct sector_header_s *s_header)
{
	if (sector_read(st, 0, s_header) < 0)
		return -1;

	s_header->sector_size = ntohl(s_header->sector_size);
	s_header->timeout_watchdog = ntohl(s_header->timeout_watchdog);
	s_header->timeout_allocate = ntohl(s_header->timeout_allocate);
	s_header->timeout_loop = ntohl(s_header->timeout_loop);
	s_header->timeout_msgwait = ntohl(s_header->timeout_msgwait);
	/* This sets the global defaults: */
	timeout_watchdog = s_header->timeout_watchdog;
	timeout_allocate = s_header->timeout_allocate;
	timeout_loop     = s_header->timeout_loop;
	timeout_msgwait  = s_header->timeout_msgwait;

	return 0;
}

static int
valid_header(const struct sector_header_s *s_header)
{
	if (memcmp(s_header->magic, sbd_magic, sizeof(s_header->magic)) != 0) {
		cl_log(LOG_ERR, "Header magic does not match.");
		return -1;
	}
	if (s_header->version != sbd_version) {
		cl_log(LOG_ERR, "Header version does not match.");
		return -1;
	}
	if (s_header->sector_size != sector_size) {
		cl_log(LOG_ERR, "Header sector size does not match.");
		return -1;
	}
	return 0;
}

static struct sector_header_s *
header_get(struct sbd_context *st)
{
	struct sector_header_s *s_header;
	s_header = sector_alloc();

	if (header_read(st, s_header) < 0) {
		cl_log(LOG_ERR, "Unable to read header from device %d", st->devfd);
		return NULL;
	}

	if (valid_header(s_header) < 0) {
		cl_log(LOG_ERR, "header on device %d is not valid.", st->devfd);
		return NULL;
	}

	/* cl_log(LOG_INFO, "Found version %d header with %d slots",
			s_header->version, s_header->slots); */

	return s_header;
}

static int
header_dump(struct sbd_context *st)
{
	struct sector_header_s *s_header;
	char uuid[37];

	s_header = header_get(st);
	if (s_header == NULL)
		return -1;

	printf("Header version     : %u.%u\n", s_header->version,
			s_header->minor_version);
	if (s_header->minor_version > 0) {
		uuid_unparse_lower(s_header->uuid, uuid);
		printf("UUID               : %s\n", uuid);
	}

	printf("Number of slots    : %u\n", s_header->slots);
	printf("Sector size        : %lu\n",
			(unsigned long)s_header->sector_size);
	printf("Timeout (watchdog) : %lu\n",
			(unsigned long)s_header->timeout_watchdog);
	printf("Timeout (allocate) : %lu\n",
			(unsigned long)s_header->timeout_allocate);
	printf("Timeout (loop)     : %lu\n",
			(unsigned long)s_header->timeout_loop);
	printf("Timeout (msgwait)  : %lu\n",
			(unsigned long)s_header->timeout_msgwait);
	return 0;
}

static int
init_device(struct sbd_context *st)
{
	struct sector_header_s	*s_header;
	struct sector_node_s	*s_node;
	struct sector_mbox_s	*s_mbox;
	struct stat 		s;
	char			uuid[37];
	int			i;
	int			rc = 0;

	s_header = sector_alloc();
	s_node = sector_alloc();
	s_mbox = sector_alloc();
	memcpy(s_header->magic, sbd_magic, sizeof(s_header->magic));
	s_header->version = sbd_version;
	s_header->slots = 255;
	s_header->sector_size = sector_size;
	s_header->timeout_watchdog = timeout_watchdog;
	s_header->timeout_allocate = timeout_allocate;
	s_header->timeout_loop = timeout_loop;
	s_header->timeout_msgwait = timeout_msgwait;

	s_header->minor_version = 1;
	uuid_generate(s_header->uuid);
	uuid_unparse_lower(s_header->uuid, uuid);

	fstat(st->devfd, &s);
	/* printf("st_size = %ld, st_blksize = %ld, st_blocks = %ld\n",
			s.st_size, s.st_blksize, s.st_blocks); */

	cl_log(LOG_INFO, "Creating version %d.%d header on device %d (uuid: %s)",
			s_header->version, s_header->minor_version,
			st->devfd, uuid);
	fprintf(stdout, "Creating version %d.%d header on device %d (uuid: %s)\n",
			s_header->version, s_header->minor_version,
			st->devfd, uuid);
	if (header_write(st, s_header) < 0) {
		rc = -1; goto out;
	}
	cl_log(LOG_INFO, "Initializing %d slots on device %d",
			s_header->slots,
			st->devfd);
	fprintf(stdout, "Initializing %d slots on device %d\n",
			s_header->slots,
			st->devfd);
	for (i=0;i < s_header->slots;i++) {
		if (slot_write(st, i, s_node) < 0) {
			rc = -1; goto out;
		}
		if (mbox_write(st, i, s_mbox) < 0) {
			rc = -1; goto out;
		}
	}

out:	free(s_node);
	free(s_header);
	free(s_mbox);
	return(rc);
}

/* Check if there already is a slot allocated to said name; returns the
 * slot number. If not found, returns -1.
 * This is necessary because slots might not be continuous. */
static int
slot_lookup(struct sbd_context *st, const struct sector_header_s *s_header, const char *name)
{
	struct sector_node_s	*s_node = NULL;
	int 			i;
	int			rc = -1;

	if (!name) {
		cl_log(LOG_ERR, "slot_lookup(): No name specified.\n");
		goto out;
	}

	s_node = sector_alloc();

	for (i=0; i < s_header->slots; i++) {
		if (slot_read(st, i, s_node) < 0) {
			rc = -2; goto out;
		}
		if (s_node->in_use != 0) {
			if (strncasecmp(s_node->name, name,
						SECTOR_NAME_MAX) == 0) {
				DBGLOG(LOG_INFO, "%s owns slot %d", name, i);
				rc = i; goto out;
			}
		}
	}

out:	free(s_node);
	return rc;
}

static int
slot_unused(struct sbd_context *st, const struct sector_header_s *s_header)
{
	struct sector_node_s	*s_node;
	int 			i;
	int			rc = -1;

	s_node = sector_alloc();

	for (i=0; i < s_header->slots; i++) {
		if (slot_read(st, i, s_node) < 0) {
			rc = -1; goto out;
		}
		if (s_node->in_use == 0) {
			rc = i; goto out;
		}
	}

out:	free(s_node);
	return rc;
}


static int
slot_allocate(struct sbd_context *st, const char *name)
{
	struct sector_header_s	*s_header = NULL;
	struct sector_node_s	*s_node = NULL;
	struct sector_mbox_s	*s_mbox = NULL;
	int			i;
	int			rc = 0;

	if (!name) {
		cl_log(LOG_ERR, "slot_allocate(): No name specified.\n");
		fprintf(stderr, "slot_allocate(): No name specified.\n");
		rc = -1; goto out;
	}

	s_header = header_get(st);
	if (!s_header) {
		rc = -1; goto out;
	}

	s_node = sector_alloc();
	s_mbox = sector_alloc();

	while (1) {
		i = slot_lookup(st, s_header, name);
		if ((i >= 0) || (i == -2)) {
			/* -1 is "no slot found", in which case we
			 * proceed to allocate a new one.
			 * -2 is "read error during lookup", in which
			 * case we error out too
			 * >= 0 is "slot already allocated" */
			rc = i; goto out;
		}

		i = slot_unused(st, s_header);
		if (i >= 0) {
			cl_log(LOG_INFO, "slot %d is unused - trying to own", i);
			fprintf(stdout, "slot %d is unused - trying to own\n", i);
			memset(s_node, 0, sizeof(*s_node));
			s_node->in_use = 1;
			strncpy(s_node->name, name, SECTOR_NAME_MAX);
			if (slot_write(st, i, s_node) < 0) {
				rc = -1; goto out;
			}
			sleep(timeout_allocate);
		} else {
			cl_log(LOG_ERR, "No more free slots.");
			fprintf(stderr, "No more free slots.\n");
			rc = -1; goto out;
		}
	}

out:	free(s_node);
	free(s_header);
	free(s_mbox);
	return(rc);
}

static int
slot_list(struct sbd_context *st)
{
	struct sector_header_s	*s_header = NULL;
	struct sector_node_s	*s_node = NULL;
	struct sector_mbox_s	*s_mbox = NULL;
	int 			i;
	int			rc = 0;

	s_header = header_get(st);
	if (!s_header) {
		rc = -1; goto out;
	}

	s_node = sector_alloc();
	s_mbox = sector_alloc();

	for (i=0; i < s_header->slots; i++) {
		if (slot_read(st, i, s_node) < 0) {
			rc = -1; goto out;
		}
		if (s_node->in_use > 0) {
			if (mbox_read(st, i, s_mbox) < 0) {
				rc = -1; goto out;
			}
			printf("%d\t%s\t%s\t%s\n",
				i, s_node->name, char2cmd(s_mbox->cmd),
				s_mbox->from);
		}
	}

out:	free(s_node);
	free(s_header);
	free(s_mbox);
	return rc;
}

static int
slot_msg(struct sbd_context *st, const char *name, const char *cmd)
{
	struct sector_header_s	*s_header = NULL;
	struct sector_mbox_s	*s_mbox = NULL;
	int			mbox;
	int			rc = 0;
	char			uuid[37];

	if (!name || !cmd) {
		cl_log(LOG_ERR, "slot_msg(): No recipient / cmd specified.\n");
		rc = -1; goto out;
	}

	s_header = header_get(st);
	if (!s_header) {
		rc = -1; goto out;
	}

	if (strcmp(name, "LOCAL") == 0) {
		name = local_uname;
	}
	
	if (s_header->minor_version > 0) {
		uuid_unparse_lower(s_header->uuid, uuid);
		cl_log(LOG_INFO, "Device UUID: %s", uuid);
	}

	mbox = slot_lookup(st, s_header, name);
	if (mbox < 0) {
		cl_log(LOG_ERR, "slot_msg(): No slot found for %s.", name);
		rc = -1; goto out;
	}

	s_mbox = sector_alloc();

	s_mbox->cmd = cmd2char(cmd);
	if (s_mbox->cmd < 0) {
		cl_log(LOG_ERR, "slot_msg(): Invalid command %s.", cmd);
		rc = -1; goto out;
	}

	strncpy(s_mbox->from, local_uname, SECTOR_NAME_MAX);

	cl_log(LOG_INFO, "Writing %s to node slot %s",
			cmd, name);
	if (mbox_write_verify(st, mbox, s_mbox) < -1) {
		rc = -1; goto out;
	}
	if (strcasecmp(cmd, "exit") != 0) {
		cl_log(LOG_INFO, "Messaging delay: %d",
				(int)timeout_msgwait);
		sleep(timeout_msgwait);
	}
	cl_log(LOG_INFO, "%s successfully delivered to %s",
			cmd, name);

out:	free(s_mbox);
	free(s_header);
	return rc;
}

static int
slot_ping(struct sbd_context *st, const char *name)
{
	struct sector_header_s	*s_header = NULL;
	struct sector_mbox_s	*s_mbox = NULL;
	int			mbox;
	int			waited = 0;
	int			rc = 0;

	if (!name) {
		cl_log(LOG_ERR, "slot_ping(): No recipient specified.\n");
		rc = -1; goto out;
	}

	s_header = header_get(st);
	if (!s_header) {
		rc = -1; goto out;
	}

	if (strcmp(name, "LOCAL") == 0) {
		name = local_uname;
	}

	mbox = slot_lookup(st, s_header, name);
	if (mbox < 0) {
		cl_log(LOG_ERR, "slot_msg(): No slot found for %s.", name);
		rc = -1; goto out;
	}

	s_mbox = sector_alloc();
	s_mbox->cmd = SBD_MSG_TEST;

	strncpy(s_mbox->from, local_uname, SECTOR_NAME_MAX);

	DBGLOG(LOG_DEBUG, "Pinging node %s", name);
	if (mbox_write(st, mbox, s_mbox) < -1) {
		rc = -1; goto out;
	}

	rc = -1;
	while (waited <= timeout_msgwait) {
		if (mbox_read(st, mbox, s_mbox) < 0)
			break;
		if (s_mbox->cmd != SBD_MSG_TEST) {
			rc = 0;
			break;
		}
		sleep(1);
		waited++;
	}

	if (rc == 0) {
		cl_log(LOG_DEBUG, "%s successfully pinged.", name);
	} else {
		cl_log(LOG_ERR, "%s failed to ping.", name);
	}

out:	free(s_mbox);
	free(s_header);
	return rc;
}

int init_devices(struct servants_list_item *servants)
{
	int rc = 0;
	struct sbd_context *st;
	struct servants_list_item *s;

	for (s = servants; s; s = s->next) {
		fprintf(stdout, "Initializing device %s\n",
				s->devname);
		st = open_device(s->devname, LOG_ERR);
		if (!st) {
			return -1;
		}
		rc = init_device(st);
		close_device(st);
		if (rc == -1) {
			fprintf(stderr, "Failed to init device %s\n", s->devname);
			return rc;
		}
		fprintf(stdout, "Device %s is initialized.\n", s->devname);
	}
	return 0;
}

static int slot_msg_wrapper(const char* devname, int mode, const void* argp)
{
	int rc = 0;
	struct sbd_context *st;
	const struct slot_msg_arg_t* arg = (const struct slot_msg_arg_t*)argp;

        st = open_device(devname, LOG_WARNING);
        if (!st) 
		return -1;
	cl_log(LOG_INFO, "Delivery process handling %s",
			devname);
	rc = slot_msg(st, arg->name, arg->msg);
	close_device(st);
	return rc;
}

static int slot_ping_wrapper(const char* devname, int mode, const void* argp)
{
	int rc = 0;
	const char* name = (const char*)argp;
	struct sbd_context *st;

	st = open_device(devname, LOG_WARNING);
	if (!st)
		return -1;
	rc = slot_ping(st, name);
	close_device(st);
	return rc;
}

int allocate_slots(const char *name, struct servants_list_item *servants)
{
	int rc = 0;
	struct sbd_context *st;
	struct servants_list_item *s;

	for (s = servants; s; s = s->next) {
		fprintf(stdout, "Trying to allocate slot for %s on device %s.\n", 
				name,
				s->devname);
		st = open_device(s->devname, LOG_WARNING);
		if (!st) {
			return -1;
		}
		rc = slot_allocate(st, name);
		close_device(st);
		if (rc < 0)
			return rc;
		fprintf(stdout, "Slot for %s has been allocated on %s.\n",
				name,
				s->devname);
	}
	return 0;
}

int list_slots(struct servants_list_item *servants)
{
	int rc = 0;
	struct servants_list_item *s;
	struct sbd_context *st;

	for (s = servants; s; s = s->next) {
		int rv  = 0;

		st = open_device(s->devname, LOG_WARNING);
		if (!st) {
			rc = -1;
			fprintf(stdout, "== disk %s unreadable!\n", s->devname);
			continue;
		}
		rv = slot_list(st);
		close_device(st);
		if (rv == -1) {
			rc = -1;
			fprintf(stdout, "== Slots on disk %s NOT dumped\n", s->devname);
		}
	}
	return rc;
}

int ping_via_slots(const char *name, struct servants_list_item *servants)
{
	int sig = 0;
	pid_t pid = 0;
	int status = 0;
	int servants_finished = 0;
	sigset_t procmask;
	siginfo_t sinfo;
	struct servants_list_item *s;

	sigemptyset(&procmask);
	sigaddset(&procmask, SIGCHLD);
	sigprocmask(SIG_BLOCK, &procmask, NULL);

	for (s = servants; s; s = s->next) {
            if(sbd_is_disk(s)) {
                s->pid = assign_servant(s->devname, &slot_ping_wrapper, 0, (const void*)name);
            }
        }

	while (servants_finished < disk_count) {
		sig = sigwaitinfo(&procmask, &sinfo);
		if (sig == SIGCHLD) {
			while ((pid = wait(&status))) {
				if (pid == -1 && errno == ECHILD) {
					break;
				} else {
					s = lookup_servant_by_pid(pid);
					if (sbd_is_disk(s)) {
						servants_finished++;
					}
				}
			}
		}
	}
	return 0;
}

int quorum_write(int good_servants)
{
	return (good_servants > disk_count/2);
}

int messenger(const char *name, const char *msg, struct servants_list_item *servants)
{
	int sig = 0;
	pid_t pid = 0;
	int status = 0;
	int servants_finished = 0;
	int successful_delivery = 0;
	sigset_t procmask;
	siginfo_t sinfo;
	struct servants_list_item *s;
	struct slot_msg_arg_t slot_msg_arg = {name, msg};

	sigemptyset(&procmask);
	sigaddset(&procmask, SIGCHLD);
	sigprocmask(SIG_BLOCK, &procmask, NULL);

	for (s = servants; s; s = s->next) {
            s->pid = assign_servant(s->devname, &slot_msg_wrapper, 0, &slot_msg_arg);
	}
	
	while (!(quorum_write(successful_delivery) || 
		(servants_finished == disk_count))) {
		sig = sigwaitinfo(&procmask, &sinfo);
		if (sig == SIGCHLD) {
			while ((pid = waitpid(-1, &status, WNOHANG))) {
				if (pid == -1 && errno == ECHILD) {
					break;
				} else {
					servants_finished++;
					if (WIFEXITED(status)
						&& WEXITSTATUS(status) == 0) {
						DBGLOG(LOG_INFO, "Process %d succeeded.",
								(int)pid);
						successful_delivery++;
					} else {
						cl_log(LOG_WARNING, "Process %d failed to deliver!",
								(int)pid);
					}
				}
			}
		}
	}
	if (quorum_write(successful_delivery)) {
		cl_log(LOG_INFO, "Message successfully delivered.");
		return 0;
	} else {
		cl_log(LOG_ERR, "Message is not delivered via more then a half of devices");
		return -1;
	}
}

unsigned long
get_first_msgwait(struct servants_list_item *servants) 
{
    unsigned long msgwait = 0;
    struct servants_list_item *s = servants;

    for (s = servants; s; s = s->next) {
        struct sbd_context *st;
        struct sector_header_s *s_header;
        st = open_device(s->devname, LOG_WARNING);
        if (!st) {
            continue;
        }

        s_header = header_get(st);
        if (s_header != NULL) {
            msgwait = (unsigned long)s_header->timeout_msgwait;
            close_device(st);
            return msgwait;
        }

        close_device(st);
    }
    return msgwait;
}

int dump_headers(struct servants_list_item *servants)
{
	int rc = 0;
	struct servants_list_item *s = servants;
	struct sbd_context *st;

	for (s = servants; s; s = s->next) {
		int rv;

		fprintf(stdout, "==Dumping header on disk %s\n", s->devname);
		st = open_device(s->devname, LOG_WARNING);
		if (st) {
			rv = header_dump(st);
			close_device(st);
		} else {
			fprintf(stdout, "== disk %s unreadable!\n", s->devname);
			rv = -1;
		}

		if (rv == -1) {
			rc = -1;
			fprintf(stdout, "==Header on disk %s NOT dumped\n", s->devname);
		} else {
			fprintf(stdout, "==Header on disk %s is dumped\n", s->devname);
		}
	}
	return rc;
}

void open_any_device(struct servants_list_item *servants)
{
	struct sector_header_s *hdr_cur = NULL;
	struct timespec t_0;
	int t_wait = 0;

	clock_gettime(CLOCK_MONOTONIC, &t_0);

	while (!hdr_cur && t_wait < timeout_startup) {
		struct timespec t_now;
		struct servants_list_item* s;

		for (s = servants; s; s = s->next) {
			struct sbd_context *st = open_device(s->devname, LOG_DEBUG);
			if (!st)
				continue;
			hdr_cur = header_get(st);
			close_device(st);
			if (hdr_cur)
				break;
		}
		clock_gettime(CLOCK_MONOTONIC, &t_now);
		t_wait = t_now.tv_sec - t_0.tv_sec;
		if (!hdr_cur) {
			sleep(timeout_loop);
		}
	}

	if (hdr_cur) {
		timeout_watchdog = hdr_cur->timeout_watchdog;
		timeout_allocate = hdr_cur->timeout_allocate;
		timeout_loop = hdr_cur->timeout_loop;
		timeout_msgwait = hdr_cur->timeout_msgwait;
	} else { 
		cl_log(LOG_ERR, "No devices were available at start-up within %i seconds.",
				timeout_startup);
		exit(1);
	}

	free(hdr_cur);
	return;
}

/*
 ::-::-::-::-::-::-::-::-::-::-::-::-::
   Begin disk based servant code
 ::-::-::-::-::-::-::-::-::-::-::-::-::
*/

static int servant_check_timeout_inconsistent(struct sector_header_s *hdr)
{
	if (timeout_watchdog != hdr->timeout_watchdog) {
		cl_log(LOG_WARNING, "watchdog timeout: %d versus %d on this device",
				(int)timeout_watchdog, (int)hdr->timeout_watchdog);
		return -1;
	}
	if (timeout_allocate != hdr->timeout_allocate) {
		cl_log(LOG_WARNING, "allocate timeout: %d versus %d on this device",
				(int)timeout_allocate, (int)hdr->timeout_allocate);
		return -1;
	}
	if (timeout_loop != hdr->timeout_loop) {
		cl_log(LOG_WARNING, "loop timeout: %d versus %d on this device",
				(int)timeout_loop, (int)hdr->timeout_loop);
		return -1;
	}
	if (timeout_msgwait != hdr->timeout_msgwait) {
		cl_log(LOG_WARNING, "msgwait timeout: %d versus %d on this device",
				(int)timeout_msgwait, (int)hdr->timeout_msgwait);
		return -1;
	}
	return 0;
}

int servant(const char *diskname, int mode, const void* argp)
{
	struct sector_mbox_s *s_mbox = NULL;
	struct sector_node_s *s_node = NULL;
	struct sector_header_s	*s_header = NULL;
	int mbox;
	int rc = 0;
	time_t t0, t1, latency;
	union sigval signal_value;
	sigset_t servant_masks;
	struct sbd_context *st;
	pid_t ppid;
	char uuid[37];
	const struct servants_list_item *s = argp;

	assert(diskname != NULL);
	cl_log(LOG_INFO, "Servant starting for device %s", diskname);

	/* Block most of the signals */
	sigfillset(&servant_masks);
	sigdelset(&servant_masks, SIGKILL);
	sigdelset(&servant_masks, SIGFPE);
	sigdelset(&servant_masks, SIGILL);
	sigdelset(&servant_masks, SIGSEGV);
	sigdelset(&servant_masks, SIGBUS);
	sigdelset(&servant_masks, SIGALRM);
	/* FIXME: check error */
	sigprocmask(SIG_SETMASK, &servant_masks, NULL);

	st = open_device(diskname, LOG_WARNING);
	if (!st) {
		exit(EXIT_MD_IO_FAIL);
	}

	s_header = header_get(st);
	if (!s_header) {
		cl_log(LOG_ERR, "Not a valid header on %s", diskname);
		exit(EXIT_MD_IO_FAIL);
	}

	if (servant_check_timeout_inconsistent(s_header) < 0) {
		cl_log(LOG_ERR, "Timeouts on %s do not match first device",
				diskname);
		exit(EXIT_MD_IO_FAIL);
	}

	if (s_header->minor_version > 0) {
		uuid_unparse_lower(s_header->uuid, uuid);
		cl_log(LOG_INFO, "Device %s uuid: %s", diskname, uuid);
	}

	mbox = slot_allocate(st, local_uname);
	if (mbox < 0) {
		cl_log(LOG_ERR,
		       "No slot allocated, and automatic allocation failed for disk %s.",
		       diskname);
		rc = EXIT_MD_IO_FAIL;
		goto out;
	}
	s_node = sector_alloc();
	if (slot_read(st, mbox, s_node) < 0) {
		cl_log(LOG_ERR, "Unable to read node entry on %s",
				diskname);
		exit(EXIT_MD_IO_FAIL);
	}

	cl_log(LOG_NOTICE, "Monitoring slot %d on disk %s", mbox, diskname);
	if (s_header->minor_version == 0) {
		set_proc_title("sbd: watcher: %s - slot: %d", diskname, mbox);
	} else {
		set_proc_title("sbd: watcher: %s - slot: %d - uuid: %s",
				diskname, mbox, uuid);
	}

	s_mbox = sector_alloc();
	if (s->first_start) {
		if (mode > 0) {
			if (mbox_read(st, mbox, s_mbox) < 0) {
				cl_log(LOG_ERR, "mbox read failed during start-up in servant.");
				rc = EXIT_MD_IO_FAIL;
				goto out;
			}
			if (s_mbox->cmd != SBD_MSG_EXIT &&
					s_mbox->cmd != SBD_MSG_EMPTY) {
				/* Not a clean stop. Abort start-up */
				cl_log(LOG_WARNING, "Found fencing message - aborting start-up. Manual intervention required!");
				ppid = getppid();
				sigqueue(ppid, SIG_EXITREQ, signal_value);
				rc = 0;
				goto out;
			}
		}
		DBGLOG(LOG_INFO, "First servant start - zeroing inbox");
		memset(s_mbox, 0, sizeof(*s_mbox));
		if (mbox_write(st, mbox, s_mbox) < 0) {
			rc = EXIT_MD_IO_FAIL;
			goto out;
		}
	}

	memset(&signal_value, 0, sizeof(signal_value));

	while (1) {
		struct sector_header_s	*s_header_retry = NULL;
		struct sector_node_s	*s_node_retry = NULL;

		t0 = time(NULL);
		sleep(timeout_loop);

		ppid = getppid();

		if (ppid == 1) {
			/* Our parent died unexpectedly. Triggering
			 * self-fence. */
			do_timeout_action();
		}

		/* These attempts are, by definition, somewhat racy. If
		 * the device is wiped out or corrupted between here and
		 * us reading our mbox, there is nothing we can do about
		 * that. But at least we tried. */
		s_header_retry = header_get(st);
		if (!s_header_retry) {
			cl_log(LOG_ERR, "No longer found a valid header on %s", diskname);
			exit(EXIT_MD_IO_FAIL);
		}
		if (memcmp(s_header, s_header_retry, sizeof(*s_header)) != 0) {
			cl_log(LOG_ERR, "Header on %s changed since start-up!", diskname);
			exit(EXIT_MD_IO_FAIL);
		}
		free(s_header_retry);

		s_node_retry = sector_alloc();
		if (slot_read(st, mbox, s_node_retry) < 0) {
			cl_log(LOG_ERR, "slot read failed in servant.");
			exit(EXIT_MD_IO_FAIL);
		}
		if (memcmp(s_node, s_node_retry, sizeof(*s_node)) != 0) {
			cl_log(LOG_ERR, "Node entry on %s changed since start-up!", diskname);
			exit(EXIT_MD_IO_FAIL);
		}
		free(s_node_retry);

		if (mbox_read(st, mbox, s_mbox) < 0) {
			cl_log(LOG_ERR, "mbox read failed in servant.");
			exit(EXIT_MD_IO_FAIL);
		}

		if (s_mbox->cmd > 0) {
			cl_log(LOG_NOTICE,
			       "Received command %s from %s on disk %s",
			       char2cmd(s_mbox->cmd), s_mbox->from, diskname);

			switch (s_mbox->cmd) {
			case SBD_MSG_TEST:
				memset(s_mbox, 0, sizeof(*s_mbox));
				mbox_write(st, mbox, s_mbox);
				sigqueue(ppid, SIG_TEST, signal_value);
				break;
			case SBD_MSG_RESET:
				exit(EXIT_MD_REQUEST_RESET);
			case SBD_MSG_OFF:
				exit(EXIT_MD_REQUEST_SHUTOFF);
			case SBD_MSG_EXIT:
				sigqueue(ppid, SIG_EXITREQ, signal_value);
				break;
			case SBD_MSG_CRASHDUMP:
				exit(EXIT_MD_REQUEST_CRASHDUMP);
			default:
				/* FIXME:
				   An "unknown" message might result
				   from a partial write.
				   log it and clear the slot.
				 */
				cl_log(LOG_ERR, "Unknown message on disk %s",
				       diskname);
				memset(s_mbox, 0, sizeof(*s_mbox));
				mbox_write(st, mbox, s_mbox);
				break;
			}
		}
		sigqueue(ppid, SIG_LIVENESS, signal_value);

		t1 = time(NULL);
		latency = t1 - t0;
		if (timeout_watchdog_warn && (latency > timeout_watchdog_warn)) {
			cl_log(LOG_WARNING,
			       "Latency: %d exceeded threshold %d on disk %s",
			       (int)latency, (int)timeout_watchdog_warn,
			       diskname);
		} else if (debug) {
			DBGLOG(LOG_DEBUG, "Latency: %d on disk %s", (int)latency,
			       diskname);
		}
	}
 out:
	free(s_mbox);
	close_device(st);
	exit(rc);
}


