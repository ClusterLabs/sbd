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
%global commit 2d595fdde4f62278b96db1b7fb79aae5e990bb0b
%global shortcommit %(c=%{commit}; echo ${c:0:7})
%global github_owner beekhof
%global buildnum 1

Name:           sbd
Summary:        Storage-based death
License:        GPLv2+
Group:          System Environment/Daemons
Version:        1.4.0
Release:        0.%{buildnum}.%{shortcommit}.git%{?dist}
Url:            https://github.com/%{github_owner}/%{name}
Source0:        https://github.com/%{github_owner}/%{name}/archive/%{commit}/%{name}-%{commit}.tar.gz
BuildRoot:      %{_tmppath}/%{name}-%{version}-build
BuildRequires:  autoconf
BuildRequires:  automake
BuildRequires:  libuuid-devel
BuildRequires:  glib2-devel
BuildRequires:  libaio-devel
BuildRequires:  corosynclib-devel
BuildRequires:  pacemaker-libs-devel
BuildRequires:  libtool
BuildRequires:  libuuid-devel
BuildRequires:  libxml2-devel
BuildRequires:  pkgconfig
BuildRequires:  make

%if 0%{?rhel} > 0
ExclusiveArch: i686 x86_64 s390x aarch64 ppc64le
%endif

%if %{defined systemd_requires}
%systemd_requires
%endif

%description

This package contains the storage-based death functionality.

%prep
###########################################################
# %setup -n sbd-%{version} -q
%setup -q -n %{name}-%{commit}
###########################################################

%build
autoreconf -i
export CFLAGS="$RPM_OPT_FLAGS -Wall -Werror"
%configure
make %{?_smp_mflags}
###########################################################

%install
###########################################################

make DESTDIR=$RPM_BUILD_ROOT LIBDIR=%{_libdir} install
rm -rf ${RPM_BUILD_ROOT}%{_libdir}/stonith

install -D -m 0755 src/sbd.sh $RPM_BUILD_ROOT/usr/share/sbd/sbd.sh
%if %{defined _unitdir}
install -D -m 0644 src/sbd.service $RPM_BUILD_ROOT/%{_unitdir}/sbd.service
install -D -m 0644 src/sbd_remote.service $RPM_BUILD_ROOT/%{_unitdir}/sbd_remote.service
%endif

mkdir -p ${RPM_BUILD_ROOT}%{_sysconfdir}/sysconfig
install -m 644 src/sbd.sysconfig ${RPM_BUILD_ROOT}%{_sysconfdir}/sysconfig/sbd

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
%doc %{_mandir}/man8/sbd*
%if %{defined _unitdir}
%{_unitdir}/sbd.service
%{_unitdir}/sbd_remote.service
%endif
%doc COPYING

%changelog
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
