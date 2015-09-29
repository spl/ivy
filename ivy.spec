Summary: Ivy C Compiler
Name: ivy
Version: 1.0
Release: 1
License: BSD and BSD-like
Group: Development/System
URL: http://ivy.cs.berkeley.edu/
BuildRoot: %{_tmppath}/%{name}-root
Provides: perl(CilConfig)
Requires: gcc
Conflicts: deputy, deputy-tinyos
Source0: %{name}-linux-%{version}.tar.gz

%description
Ivy is a compiler and runtime library for an extended dialect of C
that checks type, memory and concurrency safety. Ivy relies on a small
number of lightweight annotations in the source code to keep time and
space overheads reasonable. Ivy is implemented as a C-to-C compiler
using gcc as its backend.
For more information and documentation, please see http://ivy.cs.berkeley.edu

%prep
%setup -q -n %{name}-%{version}

%build
./configure --prefix=/usr
make

%install
rm -rf %{buildroot}
make install prefix=%{buildroot}/usr
install -d %{buildroot}/usr/share/doc/ivy-%{version}
install -m 644 debian/copyright %{buildroot}/usr/share/doc/ivy-%{version}

%clean
rm -rf $RPM_BUILD_DIR/%{name}-%{version}
rm -rf $RPM_SOURCE_DIR/%{name}-%{version}

%files
%defattr(-,root,root,-)
/usr/

%post
touch /usr/lib/ivy/bin/ivy.asm.exe

%changelog
* Mon Aug 25 2008 root <david.e.gay@intel.com> 1.0-1
- Initial release.
