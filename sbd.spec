#
# spec file for package sbd
#
# Copyright (c) 2014 SUSE LINUX Products GmbH, Nuernberg, Germany.
# Copyright (c) 2013 Lars Marowsky-Bree
#
# All modifications and additions to the file contributed by third parties
# remain the property of their copyright owners, unless otherwise agreed
# upon. The license for this file, and modifications and additions to the
# file, is the same license as for the pristine package itself (unless the
# license for the pristine package is not an Open Source License, in which
# case the license is the MIT License). An "Open Source License" is a
# license that conforms to the Open Source Definition (Version 1.9)
# published by the Open Source Initiative.

# Please submit bugfixes or comments via http://bugs.opensuse.org/
#
%global longcommit 7bcdf69597042c31ea0b4a523e732d4bbb99b3a0
%global shortcommit %(echo %{longcommit}|cut -c1-8)
%global modified %(echo %{longcommit}-|cut -f2 -d-)
%global github_owner Clusterlabs
%global commit_counter 0
%global build_counter 0
%global buildnum %(expr %{commit_counter} + %{build_counter})

%ifarch s390x s390
# minimum timeout on LPAR diag288 watchdog is 15s
%global watchdog_timeout_default 15
%else
%global watchdog_timeout_default 5
%endif

# Be careful with sync_resource_startup_default
# being enabled. This configuration has
# to be in sync with configuration in pacemaker
# where it is called sbd_sync - assure by e.g.
# mutual rpm dependencies.
%bcond_without sync_resource_startup_default
# Syncing enabled per default will lead to
# syncing enabled on upgrade without adaption
# of the config.
# Setting can still be overruled via sysconfig.
# The setting in the config-template packaged
# will follow the default if below is is left
# empty. But it is possible to have the setting
# in the config-template deviate from the default
# by setting below to an explicit 'yes' or 'no'.
%global sync_resource_startup_sysconfig ""

# Try finding and using libaio.so.x library name i.e. the one with the major
# version number such as libaio.so.1
%global libaio_name %(readlink -f %{_libdir}/libaio.so | xargs basename | cut -d "." -f 1-3)

%if "%{libaio_name}" != "" && "%{libaio_name}" != "libaio.so"
%global specify_libaio 1
%endif

Name:           sbd
Summary:        Storage-based death
License:        GPL-2.0-or-later
Group:          System Environment/Daemons
Version:        1.5.2
Release:        99.%{buildnum}.%{shortcommit}.%{modified}git%{?dist}
Url:            https://github.com/%{github_owner}/%{name}
Source0:        https://github.com/%{github_owner}/%{name}/archive/%{longcommit}/%{name}-%{longcommit}.tar.gz
BuildRoot:      %{_tmppath}/%{name}-%{version}-build
BuildRequires:  autoconf
BuildRequires:  automake
BuildRequires:  libuuid-devel
BuildRequires:  glib2-devel
BuildRequires:  libaio-devel
BuildRequires:  corosync-devel
%if 0%{?suse_version}
%if 0%{?suse_version} > 1500
BuildRequires:  libpacemaker3-devel
%else
BuildRequires:  libpacemaker-devel
%endif
%else
BuildRequires:  pacemaker-libs-devel
%endif
BuildRequires:  libtool
BuildRequires:  libuuid-devel
BuildRequires:  libxml2-devel
BuildRequires:  pkgconfig
BuildRequires:  make
Conflicts:      fence-agents-sbd < 4.5.0

%if 0%{?rhel} > 0
ExclusiveArch: i686 x86_64 s390x aarch64 ppc64le
%endif

%if %{defined systemd_requires}
%systemd_requires
%endif

%description

This package contains the storage-based death functionality.

Available rpmbuild rebuild options:
  --with(out) : sync_resource_startup_default

%package tests
Summary:        Storage-based death environment for regression tests
License:        GPL-2.0-or-later
Group:          System Environment/Daemons
%if ! 0%{?specify_libaio}
# Requires libaio-devel for the generic symbolic link libaio.so
Requires:       libaio-devel
%endif

%description tests
This package provides an environment + testscripts for
regression-testing sbd.

%prep
###########################################################
%setup -q -n %{name}-%{longcommit}
###########################################################

%build
./autogen.sh
export CFLAGS="$RPM_OPT_FLAGS -Wall -Werror"

%if 0%{?specify_libaio}
export CFLAGS="${CFLAGS} -DLIBAIO_NAME=%{libaio_name}"
%endif

%configure --with-watchdog-timeout-default=%{watchdog_timeout_default} \
           --with-sync-resource-startup-default=%{?with_sync_resource_startup_default:yes}%{!?with_sync_resource_startup_default:no}  \
           --with-sync-resource-startup-sysconfig=%{sync_resource_startup_sysconfig} \
           --with-runstatedir=%{_rundir}
make %{?_smp_mflags}
###########################################################

%install
###########################################################

make DESTDIR=$RPM_BUILD_ROOT LIBDIR=%{_libdir} install
rm -rf ${RPM_BUILD_ROOT}%{_libdir}/stonith

install -D -m 0755 src/sbd.sh $RPM_BUILD_ROOT/usr/share/sbd/sbd.sh
install -D -m 0755 tests/regressions.sh $RPM_BUILD_ROOT/usr/share/sbd/regressions.sh
%if %{defined _unitdir}
install -D -m 0644 src/sbd.service $RPM_BUILD_ROOT/%{_unitdir}/sbd.service
install -D -m 0644 src/sbd_remote.service $RPM_BUILD_ROOT/%{_unitdir}/sbd_remote.service
%endif

mkdir -p ${RPM_BUILD_ROOT}%{_sysconfdir}/sysconfig
install -m 644 src/sbd.sysconfig ${RPM_BUILD_ROOT}%{_sysconfdir}/sysconfig/sbd

# Don't package static libs
find %{buildroot} -name '*.a' -type f -print0 | xargs -0 rm -f
find %{buildroot} -name '*.la' -type f -print0 | xargs -0 rm -f

%clean
rm -rf %{buildroot}

%if %{defined _unitdir}
%post
%systemd_post sbd.service
%systemd_post sbd_remote.service

%preun
%systemd_preun sbd.service
%systemd_preun sbd_remote.service

%postun
%systemd_postun sbd.service
%systemd_postun sbd_remote.service
%endif

%files
###########################################################
%defattr(-,root,root)
%config(noreplace) %{_sysconfdir}/sysconfig/sbd
%{_sbindir}/sbd
%{_datadir}/sbd
%{_datadir}/pkgconfig/sbd.pc
%exclude %{_datadir}/sbd/regressions.sh
%doc %{_mandir}/man8/sbd*
%if %{defined _unitdir}
%{_unitdir}/sbd.service
%{_unitdir}/sbd_remote.service
%endif
%doc COPYING

%files tests
%defattr(-,root,root)
%dir %{_datadir}/sbd
%{_datadir}/sbd/regressions.sh
%{_libdir}/libsbdtestbed*

%changelog
* Sun Jun 2 2024 <klaus.wenninger@aon.at> - 1.5.2-99.0.7a3cd78b.git
- remove commented setup-macro (applied in f41)

* Thu Jan 5 2023 <klaus.wenninger@aon.at> - 1.5.2-99.0.8ec8e011.git
- fail startup if pacemaker integration is disabled while
  SBD_SYNC_RESOURCE_STARTUP is conflicting (+ hint to overcome)
- improve logs
  - when logging state of SBD_PACEMAKER tell it is just that as
    this might still be overridden via cmdline options
  - log a warning if SBD_PACEMAKER is overridden by -P or -PP option
  - do not warn about startup syncing with pacemaker integration disabled
  - when watchdog-device is busy give a hint on who is hogging it
- improve build environment
  - have --with-runstatedir overrule --runstatedir
  - use new package name for pacemaker devel on opensuse
  - make config location configurable for man-page-creation
  - reverse alloc/de-alloc order to make gcc-12 static analysis happy
- improve test environment
  - have image-files in /dev/shm to assure they are in memory and
    sbd opening the files with O_SYNC doesn't trigger unnecessary
    syncs on a heavily loaded test-machine
    fallback to /tmp if /dev/shm doesn't exist
  - wrapping away libaio and usage of device-mapper for block-device
    simulation can now be passed into make via
    SBD_USE_DM & SBD_TRANSLATE_AIO
  - have variables that configure test-environment be printed
    out prior to running tests
  - finally assure we clean environment when interrupted by a
    signal (bash should have done it with just setting EXIT handler -
    but avoiding bashism might come handy one day)

* Mon Nov 15 2021 <klaus.wenninger@aon.at> - 1.5.1-99.0.7bcdf695.git
- improve/fix cmdline handling
  - tell the actual watchdog device specified with -w
  - tolerate and strip any leading spaces of commandline option values
  - Sanitize numeric arguments
- if start-delay enabled, not explicitly given and msgwait can't be
  read from disk (diskless) use 2 * watchdog-timeout
- avoid using deprecated valloc for disk-io-buffers
- avoid frequent alloc/free of aligned buffers to prevent fragmentation
- fix memory-leak in one-time-allocations of sector-buffers
- fix AIO-API usage: properly destroy io-context
- improve/fix build environment
  - validate configure options for paths
  - remove unneeded complexity of configure.ac hierarchy
  - correctly derive package version from git (regression since 1.5.0)
  - make runstatedir configurable and derive from distribution

* Tue Jun 8 2021 <klaus.wenninger@aon.at> - 1.5.0-99.0.2a00ac70.git
- default to resource-syncing with pacemaker in spec-file and configure.ac
  This default has to match between sbd and pacemaker and
  thus qualifies this release for a minor-version-bump
- fix some regressions introduced by adding configurability previously
- adapt description of startup/shutdown sync with pacemaker
- make watchdog warning messages more understandable

* Wed Dec 2 2020 <klaus.wenninger@aon.at> - 1.4.2-99.1.bfeee963.git
- improve build/CI-friendlyness
- * travis: switch to F32 as build-host
-           switch to F32 & leap-15.2
-           changes for mock-2.0
-           turn off loop-devices & device-mapper on x86_64 targets because
-           of changes in GCE
- * regressions.sh: get timeouts from disk-header to go with proper defaults
-                   for architecture
- * use configure for watchdog-default-timeout & others
- * ship sbd.pc with basic sbd build information for downstream packages
-   to use
- * add number of commits since version-tag to build-counter

- add robustness against misconfiguration / improve documentation
- * add environment section to man-page previously just available in
-   template-config
- * inform the user to restart the sbd service after disk-initialization
- * refuse to start if any of the configured device names is invalid
- * add handshake to sync startup/shutdown with pacemakerd
-   Previously sbd just waited for the cib-connnection to show up/go away
-   which isn't robust at all.
-   The new feature needs new pacemakerd-api as counterpart.
-   Thus build checks for presence of pacemakerd-api.
-   To simplify downstream adoption behavior is configurable at runtime
-   via configure-file with a build-time-configurable default.
- * refuse to start if qdevice-sync_timeout doesn't match watchdog-timeout
-   Needed in particular as qdevice-sync_timeout delays quorum-state-update
-   and has a default of 30s that doesn't match the 5s watchdog-timeout
-   default.

- Fix: sbd-pacemaker: handle new no_quorum_demote + robustness against new
-                     policies added
- Fix: agent: correctly compare string values when calculating timeout
- Fix: scheduling: overhaul the whole thing
- * prevent possible lockup when format in proc changes
- * properly get and handle scheduler policy & prio
- * on SCHED_RR failing push to the max with SCHED_OTHER

* Tue Nov 19 2019 <klaus.wenninger@aon.at> - 1.4.1-99.1.aca7907c.git
- improvements/clarifications in documentation
- properly finalize cmap connection when disconnected from cluster
- make handling of cib-connection loss more robust
- silence some coverity findings
- overhaul log for reasonable prios and details
- if current slice doesn't have rt-budget move to root-slice
- periodically ping corosync daemon for liveness
- actually use crashdump timeout if configured
- avoid deprecated names for g_main-loop-funcitons
- conflict with fence-agents-sbd < 4.5.0
- rather require corosync-devel provided by most distributions
- make devices on cmdline overrule those coming via SBD_DEVICE
- make 15s timeout on s390 be used consistently
- improve build/test for CI-friendlyness
-   * add autogen.sh
-   * enable/improve out-of-tree-building
-   * make tar generation smarter
-   * don't modify sbd.spec
-   * make distcheck-target work
-   * Add tests/regressions.sh to check-target
-   * use unique devmapper names for multiple tests in parallel
-   * consistently use serial test-harness for visible progress
-   * package tests into separate package (not packaged before)
-   * add preload-library to intercept reboots while testing
-   * add tests for sbd in daemon-mode & watchdog-dev-handling
-   * make tests work in non-privileged containers

* Mon Jan 14 2019 <klaus.wenninger@aon.at> - 1.4.0-0.1.2d595fdd.git
- updated travis-CI (ppc64le-build, fedora29, remove need for
  alectolytic-build-container)
- make watchdog-device-query easier to be handled by an SELinux-policy
- configurable delay value for SBD_DELAY_START
- use pacemaker's new pe api with constructors/destructors
- make timeout-action executed by sbd configurable
- init script for sysv systems
- version bump to v1.4.0 to denote Pacemaker 2.0.0 compatibility

* Fri Jun 29 2018 <klaus.wenninger@aon.at> - 1.3.1-0.1.e102d9ed.git
- removed unneeded python-devel build-requirement
- changed legacy corosync-devel to corosynclib-devel

* Fri Nov  3 2017 <klaus.wenninger@aon.at> - 1.3.1-0.1.a180176c.git
- Add commands to test/query watchdogs
- Allow 2-node-operation with a single shared-disk
- Overhaul of the command-line options & config-file
- Proper handling of off instead of reboot
- Refactored disk-servant for more robust communication with parent
- Fix config for Debian + configurable location of config
- Fixes in sbd.sh - multiple SBD devices and others

* Sun Mar 27 2016 <klaus.wenninger@aon.at> - 1.3.0-0.1.4ee36fa3.git
- Changes since v1.2.0 like adding the possibility to have a
  watchdog-only setup without shared-block-devices
  legitimate a bump to v1.3.0.

* Mon Oct 13 2014 <andrew@beekhof.net> - 1.2.1-0.4.3de531ed.git
- Fixes for suitability to the el7 environment

* Tue Sep 30 2014 <andrew@beekhof.net> - 1.2.1-0.3.8f912945.git
- Only build on archs supported by the HA Add-on

* Fri Aug 29 2014 <andrew@beekhof.net> - 1.2.1-0.2.8f912945.git
- Remove some additional SUSE-isms

* Fri Aug 29 2014 <andrew@beekhof.net> - 1.2.1-0.1.8f912945.git
- Prepare for package review
  Resolves: rhbz#1134245
