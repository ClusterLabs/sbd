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

# TODO:
# - More tests
# - Handle optional, long-running tests better
# - Support for explicitly running a single test
# - Verify output from commands
#   - Normalize uuids and device names so they are diffable
#   - Log to file, instead of syslog is needed
# - How to test watch mode?
# - Can the unit/service file be tested? or at least the wrapper?

: ${SBD_BINARY:="/usr/sbin/sbd"}
: ${SBD_PRELOAD:="libsbdtestbed.so"}
: ${SBD_USE_DM:="yes"}
: ${SBD_TRANSLATE_AIO:= "no"}

sbd() {
	LD_BIND_NOW=yes LD_PRELOAD=${SBD_PRELOAD} SBD_DEVICE="${SBD_DEVICE}" SBD_PRELOAD_LOG=${SBD_PRELOAD_LOG} SBD_WATCHDOG_DEV=/dev/watchdog setsid ${SBD_BINARY} -p ${SBD_PIDFILE} "$@"
}

sbd_sleep() {
	TIME="delay %es" time sleep $1
}

sbd_wipe_disk() {
	dd if=/dev/zero of=$1 count=2048 2>/dev/null
}

sbd_setup() {
	trap 'sbd_teardown $?' EXIT
	trap 'sbd_teardown 134' ABRT
	trap 'sbd_teardown 131' QUIT
	trap 'sbd_teardown 143' TERM
	trap 'sbd_teardown 130' INT
	trap "sbd_teardown 1" ERR
	if [[ -d /dev/shm ]]; then
		SBD_IMGPATH=/dev/shm
	else
		SBD_IMGPATH=/tmp
	fi
	for N in $(seq 3) ; do
		F[$N]=$(mktemp ${SBD_IMGPATH}/sbd.device.$N.XXXXXX)
		sbd_wipe_disk ${F[$N]}
		if [[ "${SBD_USE_DM}" == "yes" ]]; then
			R[$N]=$(echo ${F[$N]}|cut -f4 -d.)
			L[$N]=$(losetup -f)
			losetup ${L[$N]} ${F[$N]}
			D[$N]="/dev/mapper/sbd_${N}_${R[$N]}"
			dmsetup create sbd_${N}_${R[$N]} --table "0 2048 linear ${L[$N]} 0"
			dmsetup mknodes sbd_${N}_${R[$N]}
		else
			D[$N]=${F[$N]}
		fi
	done
	if [[ "${SBD_USE_DM}" != "yes" ]]; then
		SBD_DEVICE="${F[1]};${F[2]};${F[3]}"
	fi
	SBD_PIDFILE=$(mktemp /tmp/sbd.pidfile.XXXXXX)
	SBD_PRELOAD_LOG=$(mktemp /tmp/sbd.logfile.XXXXXX)
	sbd -d ${D[1]} create
	WATCHDOG_TIMEOUT=$(LD_PRELOAD=${SBD_PRELOAD} SBD_DEVICE="${D[1]}" ${SBD_BINARY} dump |grep watchdog|cut -f2 -d:)
	MSGWAIT_TIMEOUT=$(LD_PRELOAD=${SBD_PRELOAD} SBD_DEVICE="${D[1]}" ${SBD_BINARY} dump |grep msgwait|cut -f2 -d:)
}

sbd_teardown() {
	# disable traps prior to cleanup to avoid loops
	trap '' EXIT ABRT QUIT TERM INT ERR
	for N in $(seq 3) ; do
		if [[ "${SBD_USE_DM}" == "yes" ]]; then
			dmsetup remove sbd_${N}_${R[$N]}
			losetup -d ${L[$N]}
		fi
		rm -f ${F[$N]}
		sbd_daemon_cleanup
		rm -f ${SBD_PIDFILE}
		rm -f ${SBD_PRELOAD_LOG}
	done
	# now that everything should be clean
	# return to original handlers to terminate
	# as requested
	trap - EXIT ABRT QUIT TERM INT ERR
	if [[ $1 -eq 134 ]]; then
		echo "Received SIGABRT!!!"
		kill -ABRT $$
	elif [[ $1 -eq 131 ]]; then
		echo "Received SIGQUIT!!!"
		kill -QUIT $$
	elif [[ $1 -eq 143 ]]; then
		echo "Received SIGTERM!!!"
		kill -TERM $$
	elif [[ $1 -eq 130 ]]; then
		echo "Received SIGINT!!!"
		kill -INT $$
	else
		exit $1
	fi
}

sbd_dev_fail() {
	if [[ "${SBD_USE_DM}" == "yes" ]]; then
		dmsetup wipe_table sbd_${1}_${R[$1]}
	else
		D[$1]=/tmp/fail123456789
	fi
}

sbd_dev_resume() {
	if [[ "${SBD_USE_DM}" == "yes" ]]; then
		dmsetup suspend sbd_${1}_${R[$1]}
		dmsetup load sbd_${1}_${R[$1]} --table "0 2048 linear ${L[$1]} 0"
		dmsetup resume sbd_${1}_${R[$1]}
	else
		D[$1]=${F[$1]}
	fi
}

sbd_daemon_cleanup() {
	if [[ "${SBD_PRELOAD_LOG}" != "" ]]; then
		echo > ${SBD_PRELOAD_LOG}
	fi
	if [[ "${SBD_PIDFILE}" != "" ]]; then
		pkill -TERM --pidfile ${SBD_PIDFILE} 2>/dev/null
		sbd_sleep 5
		pkill -KILL --pidfile ${SBD_PIDFILE} 2>/dev/null
		pkill -KILL --parent "$(cat ${SBD_PIDFILE} 2>/dev/null)" 2>/dev/null
		echo > ${SBD_PIDFILE}
	fi
}

_ok() {
	echo "-- $*"
	"$@"
	rc=$?
	if [ $rc -ne 0 ]; then
		echo "$* failed with $rc"
		exit $rc
	fi
}

_no() {
	echo "-- $*"
	"$@"
	rc=$?
	if [ $rc -eq 0 ]; then
		echo "$* did NOT fail ($rc)"
		exit $rc
	fi
	return 0
}

_in_log() {
	grep "$@" ${SBD_PRELOAD_LOG} >/dev/null
	if [ $? -ne 0 ]; then
		echo "didn't find '$*' in log:"
		cat ${SBD_PRELOAD_LOG}
		sbd_daemon_cleanup
		exit 1
	fi
}

test_1() {
	echo "Creating three devices"
	_ok sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} create
	_ok sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} dump
}

test_2() {
	echo "Basic functionality"
	for S in `seq 2` ; do
		_ok sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} allocate "test-$S"
	done
	_ok sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} -n test-1 message test-2 reset
	_ok sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} list
}

test_3() {
	echo "Start mode (expected not to start, because reset was written in test_2)"
	_no sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} -n test-2 -Z -Z -Z -S 1 watch
}

test_4() {
	echo "Deliver message with 1 failure"
	sbd_dev_fail 1
	_no sbd -d ${D[1]} -n test-1 message test-2 exit
	_no sbd -d ${D[1]} -d ${D[2]} -n test-1 message test-2 exit
	_ok sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} -n test-1 message test-2 exit
	sbd_dev_resume 1

}

test_5() {
	echo "Deliver message with 2 failures"
	sbd_dev_fail 1
	sbd_dev_fail 2
	_no sbd -d ${D[1]} -d ${D[2]} -n test-1 message test-2 exit
	_no sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} -n test-1 message test-2 exit
	sbd_dev_resume 1
	sbd_dev_resume 2

}

test_6() {
	echo "Deliver message with 3 failures"
	sbd_dev_fail 1
	sbd_dev_fail 2
	sbd_dev_fail 3
	_no sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} -n test-1 message test-2 exit
	sbd_dev_resume 1
	sbd_dev_resume 2
	sbd_dev_resume 3
}

test_101() {
	echo "Creating one device"
	_ok sbd -d ${D[1]} create
}

test_102() {
	echo "Creating two devices"
	_ok sbd -d ${D[1]} -d ${D[2]} create
}

test_7() {
	echo "Allocate all slots plus 1"
	_ok sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} -2 0 create
	for S in `seq 255` ; do
		_ok sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} allocate "test-$S"
	done
	_no sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} allocate "test-256"
}

test_8() {
	echo "Non-existent device path"
	_no sbd -d /dev/kfdifdifdfdlfd -create 2>/dev/null
}

test_9() {
	echo "Basic sbd invocation"
	_no sbd
	_ok sbd -h
}

test_watchdog() {
	echo "Basic watchdog test"
	echo > ${SBD_PRELOAD_LOG}
	sbd test-watchdog < /dev/null
	_in_log "watchdog fired"
}

test_stall_inquisitor() {
	echo "Stall inquisitor test"
	sbd_daemon_cleanup
	sbd -d ${D[1]} -d ${D[2]} -d ${D[3]} -n test-1 watch
	sbd_sleep 10
	_ok kill -0 "$(cat ${SBD_PIDFILE})"
	kill -STOP "$(cat ${SBD_PIDFILE})"
	sbd_sleep $((${WATCHDOG_TIMEOUT} * 2))
	kill -CONT "$(cat ${SBD_PIDFILE})" 2>/dev/null
	_in_log "watchdog fired"
}

test_wipe_slots1() {
	echo "Wipe slots test (with watchdog)"
	sbd_daemon_cleanup
	sbd -d ${D[1]} -n test-1 watch
	sbd_sleep 2
	sbd_wipe_disk ${D[1]}
	sbd_sleep $((${MSGWAIT_TIMEOUT} + ${WATCHDOG_TIMEOUT} * 2))
	_in_log "watchdog fired"
}

test_wipe_slots2() {
	echo "Wipe slots test (without watchdog)"
	sbd_daemon_cleanup
	sbd -d ${D[1]} create
	sbd -d ${D[1]} -w /dev/null -n test-1 watch
	sbd_sleep 2
	sbd_wipe_disk ${D[1]}
	sbd_sleep $((${MSGWAIT_TIMEOUT} + ${WATCHDOG_TIMEOUT} * 2))
	_in_log "sysrq-trigger ('b')"
	_in_log "reboot (reboot)"
}

test_message1() {
	echo "Message test (reset)"
	sbd_daemon_cleanup
	sbd -d ${D[1]} create
	sbd -d ${D[1]} -w /dev/null -n test-1 watch
	sbd_sleep 2
	sbd -d ${D[1]} message test-1 reset
	sbd_sleep 2
	_in_log "sysrq-trigger ('b')"
	_in_log "reboot (reboot)"
}

test_message2() {
	echo "Message test (off)"
	sbd_daemon_cleanup
	sbd -d ${D[1]} create
	sbd -d ${D[1]} -w /dev/null -n test-1 watch
	sbd_sleep 2
	sbd -d ${D[1]} message test-1 off
	sbd_sleep 2
	_in_log "sysrq-trigger ('o')"
	_in_log "reboot (poweroff)"
}

test_message3() {
	echo "Message test (crashdump)"
	sbd_daemon_cleanup
	sbd -d ${D[1]} create
	sbd -d ${D[1]} -w /dev/null -n test-1 watch
	sbd_sleep 2
	sbd -d ${D[1]} message test-1 crashdump
	sbd_sleep 2
	_in_log "sysrq-trigger ('c')"
}

test_timeout_action1() {
	echo "Timeout action test (off)"
	sbd_daemon_cleanup
	sbd -d ${D[1]} create
	SBD_TIMEOUT_ACTION=off sbd -d ${D[1]} -w /dev/null -n test-1 watch
	sbd_sleep 2
	sbd_wipe_disk ${D[1]}
	sbd_sleep $((${MSGWAIT_TIMEOUT} + ${WATCHDOG_TIMEOUT} * 2))
	_in_log "sysrq-trigger ('o')"
	_in_log "reboot (poweroff)"
}

test_timeout_action2() {
	echo "Timeout action test (crashdump)"
	sbd_daemon_cleanup
	sbd -d ${D[1]} create
	SBD_TIMEOUT_ACTION=crashdump sbd -d ${D[1]} -w /dev/null -n test-1 watch
	sbd_sleep 2
	sbd_wipe_disk ${D[1]}
	sbd_sleep $((${MSGWAIT_TIMEOUT} + ${WATCHDOG_TIMEOUT} * 2))
	_in_log "sysrq-trigger ('c')"
}

echo "SBD_BINARY = \"${SBD_BINARY}\""
echo "SBD_PRELOAD = \"${SBD_PRELOAD}\""
echo "SBD_USE_DM = \"${SBD_USE_DM}\""
echo "SBD_TRANSLATE_AIO = \"${SBD_TRANSLATE_AIO}"\"

sbd_setup

MOUNTPOINT=$((mount|grep ${SBD_IMGPATH} || echo unknown)|cut -f1 -d" ")
_ok test "${WATCHDOG_TIMEOUT}" -eq "${WATCHDOG_TIMEOUT}"
_ok test "${MSGWAIT_TIMEOUT}" -eq "${MSGWAIT_TIMEOUT}"
echo "running sbd-tests with WATCHDOG_TIMEOUT=${WATCHDOG_TIMEOUT}s MSGWAIT_TIMEOUT=${MSGWAIT_TIMEOUT}s"
echo "on randomly named images in SBD_IMGPATH=\"${SBD_IMGPATH}\" on ${MOUNTPOINT} filesystem"

if [[ "${SBD_PRELOAD}" != "" ]]; then
	SBD_DAEMON_TESTS="watchdog stall_inquisitor wipe_slots1 wipe_slots2 message1 message2 message3 timeout_action1 timeout_action2"
fi

for T in 101 102 $(seq 9) ${SBD_DAEMON_TESTS}; do
	if ! test_$T ; then
		echo "FAILURE: Test $T"
		break
	fi
	echo "SUCCESS: Test $T"
done

echo "SUCCESS: All tests completed"

