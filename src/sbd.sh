#!/bin/bash
#
# Copyright (C) 2013 Lars Marowsky-Bree <lmb@suse.com>
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public
# License as published by the Free Software Foundation; either
# version 2 of the License, or (at your option) any later version.
#
# This software is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License along
# with this program; if not, write to the Free Software Foundation, Inc.,
# 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
#

SBD_CONFIG=/etc/sysconfig/sbd
SBD_BIN="/usr/sbin/sbd"

test -x $SBD_BIN || exit 1
test -f $SBD_CONFIG || exit 1

. $SBD_CONFIG

unset LC_ALL; export LC_ALL
unset LANGUAGE; export LANGUAGE

: ${OCF_ROOT:=/usr/lib/ocf}
: ${OCF_FUNCTIONS_DIR=${OCF_ROOT}/lib/heartbeat}
. ${OCF_FUNCTIONS_DIR}/ocf-shellfuncs

# Construct commandline for some common options
if [ -z "$SBD_DEVICE" ]; then
	echo "No sbd devices defined"
	exit 1
fi
SBD_DEVS=${SBD_DEVICE%;}
SBD_DEVICE=${SBD_DEVS//;/ -d }

: ${SBD_PIDFILE:=/var/run/sbd.pid}
SBD_OPTS+=" -p $SBD_PIDFILE"
: ${SBD_PACEMAKER:="true"}
if ocf_is_true "$SBD_PACEMAKER" ; then
	SBD_OPTS+=" -P"
fi
: ${SBD_WATCHDOG:="true"}
if ! ocf_is_true "$SBD_WATCHDOG" ; then
	SBD_OPTS+=" -W -W"
fi
if [ -n "$SBD_WATCHDOG_DEV" ]; then
	SBD_OPTS+=" -w $SBD_WATCHDOG_DEV"
fi
: ${SBD_STARTMODE:="always"}
case "$SBD_STARTMODE" in
always) SBD_OPTS+=" -S 0" ;;
clean) SBD_OPTS+=" -S 1" ;;
esac
: ${SBD_DELAY_START:="no"}
if ocf_is_true "$SBD_DELAY_START" ; then
	SBD_OPTS+=" -A"
fi

start() {
	if ! pidofproc -p $SBD_PIDFILE $SBD_BIN >/dev/null 2>&1 ; then
		if ! $SBD_BIN -d $SBD_DEVICE $SBD_OPTS watch ; then
			echo "SBD failed to start; aborting."
			exit 1
		fi
	else
		return 0
	fi
}

stop() {
	if ! $SBD_BIN -d $SBD_DEVICE -D $SBD_OPTS message LOCAL exit ; then
		echo "SBD failed to stop; aborting."
		exit 1
	fi
        while pidofproc -p $SBD_PIDFILE $SBD_BIN >/dev/null 2>&1 ; do
                sleep 1
        done
}

case "$1" in
start|stop)
	$1 ;;
*)
	echo "Usage: $0 (start|stop)"
	exit 1
	;;
esac
	
# TODO:
# - Make openais init script call out to this script too
# - How to handle the former "force-start" option?
#     force-start)
#        SBD_OPTS="$SBD_OPTS -S 0"
#        start
#        ;;

