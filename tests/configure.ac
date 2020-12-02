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
	[1.4.2],
	[lmb@suse.com])
m4_include([../tests-opt.m4])
AC_CANONICAL_HOST
AC_CONFIG_AUX_DIR(.)
AC_CONFIG_HEADERS(config.h)
m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([no])])
AM_INIT_AUTOMAKE(1.11.1 foreign TESTS_OPTION)
LT_INIT([dlopen],[disable-static])
AM_PROG_CC_C_O

PKG_CHECK_MODULES(glib, [glib-2.0])

CPPFLAGS="$CPPFLAGS -Werror $glib_CFLAGS"
LIBS="$LIBS $glib_LIBS"

dnl     checks for libraries
AC_CHECK_LIB(c, dlopen)                         dnl if dlopen is in libc...
AC_CHECK_LIB(dl, dlopen)                        dnl -ldl (for Linux)


CONFIGDIR=""
AC_ARG_WITH(configdir,
    [  --with-configdir=DIR
       Directory for SBD configuration file [${CONFIGDIR}]],
    [ CONFIGDIR="$withval" ]
)

#
# Where is dlopen?
#
if test "$ac_cv_lib_c_dlopen" = yes; then
    LIBADD_DL=""
elif test "$ac_cv_lib_dl_dlopen" = yes; then
    LIBADD_DL=-ldl
else
    LIBADD_DL=${lt_cv_dlopen_libs}
fi


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

AC_SUBST(LIBADD_DL)        dnl extra flags for dynamic linking libraries

dnl The Makefiles and shell scripts we output
AC_CONFIG_FILES([Makefile])

dnl Now process the entire list of files added by previous
dnl  calls to AC_CONFIG_FILES()
AC_OUTPUT()
