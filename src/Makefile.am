AM_CFLAGS = -D_GNU_SOURCE -DCHECK_AIS -DSBINDIR=\"$(sbindir)\"
AM_CPPFLAGS =  -I$(includedir)/pacemaker  \
	       -I$(includedir)/heartbeat  \
		$(glib_CFLAGS)

sbin_PROGRAMS = sbd

sbd_SOURCES = sbd-common.c sbd-inquisitor.c sbd-pacemaker.c sbd-cluster.c setproctitle.c sbd.h sbd.sysconfig

if SUPPORT_SHARED_DISK
sbd_SOURCES += sbd-md.c
endif

sbd_LDADD = $(glib_LIBS) $(libcoroipcc_LIBS)

sbddir = $(datadir)/$(PACKAGE)
sbd_SCRIPTS = sbd.service.sh

install-exec-hook:
	$(MKDIR_P) -- $(DESTDIR)/$(sbddir)
	ln -s -f sbd.service.sh $(DESTDIR)/$(sbddir)/sbd_remote.service.sh

uninstall-hook:
	rm -f $(DESTDIR)/$(sbddir)/sbd_remote.service.sh
	rmdir $(DESTDIR)/$(sbddir)
