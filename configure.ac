dnl
dnl autoconf for Agents
dnl
dnl License: GNU General Public License (GPL)

dnl ===============================================
dnl Bootstrap 
dnl ===============================================
AC_PREREQ(2.63)

dnl Suggested structure:
dnl     information on the package
dnl     checks for programs
dnl     checks for libraries
dnl     checks for header files
dnl     checks for types
dnl     checks for structures
dnl     checks for compiler characteristics
dnl     checks for library functions
dnl     checks for system services

AC_INIT([sbd], 
	[1.4.0],
	[lmb@suse.com])
AC_CANONICAL_HOST
AC_CONFIG_AUX_DIR(.)
AC_CONFIG_HEADERS(config.h)
m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([no])])
AM_INIT_AUTOMAKE
AM_PROG_CC_C_O

PKG_CHECK_MODULES(glib, [glib-2.0])
dnl PKG_CHECK_MODULES(libcoroipcc, [libcoroipcc])

PKG_CHECK_MODULES(cmap, [libcmap], HAVE_cmap=1, HAVE_cmap=0)
PKG_CHECK_MODULES(votequorum, [libvotequorum], HAVE_votequorum=1, HAVE_votequorum=0)

dnl pacemaker > 1.1.8
PKG_CHECK_MODULES(pacemaker, [pacemaker, pacemaker-cib], HAVE_pacemaker=1, HAVE_pacemaker=0)

dnl pacemaker <= 1.1.8
PKG_CHECK_MODULES(pcmk, [pcmk, pcmk-cib], HAVE_pcmk=1, HAVE_pcmk=0)
PKG_CHECK_MODULES(libqb, [libqb])

CPPFLAGS="$CPPFLAGS -Werror"
if test $HAVE_pacemaker = 0 -a $HAVE_pcmk = 0; then
    AC_MSG_ERROR(No package 'pacemaker' found)
elif test $HAVE_pacemaker = 1; then
    CPPFLAGS="$CPPFLAGS $glib_CFLAGS $pacemaker_CFLAGS"
    if test $HAVE_cmap = 0; then
        AC_MSG_NOTICE(No library 'cmap' found)
    else
        CPPFLAGS="$CPPFLAGS $cmap_CFLAGS"
        LIBS="$LIBS $cmap_LIBS"
    fi
    if test $HAVE_votequorum = 0; then
        AC_MSG_NOTICE(No library 'votequorum' found)
    else
        CPPFLAGS="$CPPFLAGS $votequorum_CFLAGS"
        LIBS="$LIBS $votequorum_LIBS"
    fi
fi

PKG_CHECK_MODULES(libxml, [libxml-2.0])
CPPFLAGS="$CPPFLAGS $libxml_CFLAGS $libqb_CFLAGS $pacemaker_CFLAGS $pcmk_CFLAGS"
LIBS="$LIBS $libxml_LIBS $libqb_LIBS $pacemaker_LIBS $pcmk_LIBS"

dnl     checks for libraries
AC_CHECK_LIB(aio, io_setup, , missing="yes")
AC_CHECK_LIB(qb, qb_ipcs_connection_auth_set, , missing="yes")
AC_CHECK_LIB(cib, cib_new, , missing="yes")
AC_CHECK_LIB(crmcommon, set_crm_log_level, , missing="yes")
AC_CHECK_LIB(pe_status, pe_find_node, , missing="yes")
AC_CHECK_LIB(pe_rules, test_rule, , missing="yes")
AC_CHECK_LIB(crmcluster, crm_peer_init, , missing="yes")
AC_CHECK_LIB(uuid, uuid_unparse, , missing="yes")
AC_CHECK_LIB(cmap, cmap_initialize, , HAVE_cmap=0)
AC_CHECK_LIB(votequorum, votequorum_getinfo, , HAVE_votequorum=0)

dnl pacemaker >= 1.1.8
AC_CHECK_HEADERS(crm/cluster.h)
AC_CHECK_LIB(crmcommon, pcmk_strerror, , missing="yes")
AC_CHECK_LIB(cib, cib_apply_patch_event, , missing="yes")

dnl pacemaker-2.0 removed support for corosync 1 cluster layer
AC_CHECK_DECLS([pcmk_cluster_classic_ais, pcmk_cluster_cman],,,
	       [#include <pacemaker/crm/cluster.h>])

dnl check for new pe-API
AC_CHECK_FUNCS(pe_new_working_set)

if test "$missing" = "yes"; then
   AC_MSG_ERROR([Missing required libraries or functions.])
fi

AC_PATH_PROGS(POD2MAN, pod2man, pod2man)

AC_ARG_ENABLE([shared-disk],
[  --enable-shared-disk Turn on functionality that requires shared disk
     [default=yes]])

DISK=0
if test "x${enable_shared_disk}" != xno ; then
   DISK=1
fi

AC_DEFINE_UNQUOTED(SUPPORT_SHARED_DISK, $DISK, Turn on functionality that requires shared disk)
AM_CONDITIONAL(SUPPORT_SHARED_DISK, test "$DISK" = "1")

if
	test -e /proc/$$
then
	echo "/proc/{pid} is supported" 
	AC_DEFINE_UNQUOTED(HAVE_PROC_PID, 1, Define to 1 if /proc/{pid} is supported.)
fi

AC_DEFINE_UNQUOTED(CHECK_TWO_NODE, $HAVE_cmap, Turn on checking for 2-node cluster)
AM_CONDITIONAL(CHECK_TWO_NODE, test "$HAVE_cmap" = "1")

AC_DEFINE_UNQUOTED(CHECK_VOTEQUORUM_HANDLE, $HAVE_votequorum, Turn on periodic checking of votequorum-handle)
AM_CONDITIONAL(CHECK_VOTEQUORUM_HANDLE, test "$HAVE_votequorum" = "1")

CONFIGDIR=""
AC_ARG_WITH(configdir,
    [  --with-configdir=DIR
       Directory for SBD configuration file [${CONFIGDIR}]],
    [ CONFIGDIR="$withval" ]
)

dnl **********************************************************************
dnl Check for various argv[] replacing functions on various OSs
dnl
dnl Borrowed from Proftpd
dnl Proftpd is Licenced under the terms of the GNU General Public Licence
dnl and is available from http://www.proftpd.org/
dnl

AC_CHECK_FUNCS(setproctitle)
AC_CHECK_HEADERS(libutil.h)
AC_CHECK_LIB(util, setproctitle,
        [AC_DEFINE(HAVE_SETPROCTITLE,1,[ ])
                ac_cv_func_setproctitle="yes" ; LIBS="$LIBS -lutil"])

if test "$ac_cv_func_setproctitle" = "yes"; then
  pf_argv_set="PF_ARGV_NONE"
fi

if test "$pf_argv_set" = ""; then
  AC_CHECK_HEADERS(sys/pstat.h)
  if test "$ac_cv_header_pstat_h" = "yes"; then
    AC_CHECK_FUNCS(pstat)

    if test "$ac_cv_func_pstat" = "yes"; then
        pf_argv_set="PF_ARGV_PSTAT"
    else
        pf_argv_set="PF_ARGV_WRITEABLE"
    fi
  fi

  if test "$pf_argv_set" = ""; then
    AC_EGREP_HEADER([#define.*PS_STRINGS.*],sys/exec.h,
                        have_psstrings="yes",have_psstrings="no")
    if test "$have_psstrings" = "yes"; then
        pf_argv_set="PF_ARGV_PSSTRINGS"
    fi
  fi

  if test "$pf_argv_set" = ""; then
    AC_CACHE_CHECK(whether __progname and __progname_full are available,
                    pf_cv_var_progname,
                    AC_TRY_LINK([extern char *__progname, *__progname_full;],
                        [__progname = "foo"; __progname_full = "foo bar";],
                        pf_cv_var_progname="yes", pf_cv_var_progname="no"))

    if test "$pf_cv_var_progname" = "yes"; then
        AC_DEFINE(HAVE___PROGNAME,1,[ ])
    fi

    AC_CACHE_CHECK(which argv replacement method to use,
                    pf_cv_argv_type,
                    AC_EGREP_CPP(yes,[
#if defined(__GNU_HURD__)
  yes
#endif
  ],pf_cv_argv_type="new", pf_cv_argv_type="writeable"))

    if test "$pf_cv_argv_type" = "new"; then
        pf_argv_set="PF_ARGV_NEW"
    fi

    if test "$pf_argv_set" = ""; then
        pf_argv_set="PF_ARGV_WRITEABLE"
    fi
  fi
fi
AC_DEFINE_UNQUOTED(PF_ARGV_TYPE, $pf_argv_set,
        mechanism to pretty-print ps output: setproctitle-equivalent)

dnl End of tests borrowed from Proftpd

AC_MSG_NOTICE(Sanitizing prefix: ${prefix})
case $prefix in
  NONE)
	prefix=/usr
	dnl Fix default variables - "prefix" variable if not specified
	if test "$localstatedir" = "\${prefix}/var"; then
		localstatedir="/var"
	fi
	if test "$sysconfdir" = "\${prefix}/etc"; then
		sysconfdir="/etc"
	fi
	;;
esac

AC_MSG_NOTICE(Sanitizing exec_prefix: ${exec_prefix})
case $exec_prefix in
  dnl For consistency with Heartbeat, map NONE->$prefix
  NONE)	  exec_prefix=$prefix;;
  prefix) exec_prefix=$prefix;;
esac

dnl Expand autoconf variables so that we dont end up with '${prefix}'
dnl in #defines and python scripts
dnl NOTE: Autoconf deliberately leaves them unexpanded to allow
dnl    make exec_prefix=/foo install
dnl No longer being able to do this seems like no great loss to me...

eval prefix="`eval echo ${prefix}`"
eval exec_prefix="`eval echo ${exec_prefix}`"
eval bindir="`eval echo ${bindir}`"
eval sbindir="`eval echo ${sbindir}`"
eval libexecdir="`eval echo ${libexecdir}`"
eval datadir="`eval echo ${datadir}`"
eval sysconfdir="`eval echo ${sysconfdir}`"
eval sharedstatedir="`eval echo ${sharedstatedir}`"
eval localstatedir="`eval echo ${localstatedir}`"
eval libdir="`eval echo ${libdir}`"
eval includedir="`eval echo ${includedir}`"
eval oldincludedir="`eval echo ${oldincludedir}`"
eval infodir="`eval echo ${infodir}`"
eval mandir="`eval echo ${mandir}`"

if test x"${CONFIGDIR}" = x""; then
    CONFIGDIR="${sysconfdir}/sysconfig"
fi
AC_SUBST(CONFIGDIR)

dnl The Makefiles and shell scripts we output
AC_CONFIG_FILES([Makefile src/Makefile agent/Makefile man/Makefile agent/sbd src/sbd.service src/sbd_remote.service src/sbd.sh src/sbd.service.sh], [chmod +x src/sbd.service.sh])

dnl Now process the entire list of files added by previous 
dnl  calls to AC_CONFIG_FILES()
AC_OUTPUT()
