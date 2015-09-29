# configure.in for Ivy           -*- sh -*-
AC_INIT(src/main.ml)
AC_PREREQ(2.50)

AC_PROG_CC
AC_PROG_INSTALL

AC_CANONICAL_SYSTEM

IVYHOME=`pwd`
DEFAULT_CIL_MODE=GNUCC
IVY_VERSION=1.0

CVCLLIB=/usr/local/lib
CVCLINC=/usr/local/include

YICESLIB=/usr/local/lib
YICESINC=/usr/local/include

OCAMLINC=/usr/lib/ocaml

# make sure I haven't forgotten to run autoconf
if test configure -ot configure.ac; then
  AC_MSG_ERROR(configure is older than configure.ac; you forgot to run autoconf)
fi

ECC=$CC
AC_SUBST(ECC)

case "$target" in
  # Linux
  *86*linux*|*86*openbsd*)
    AC_MSG_RESULT(configuring for $target)
    ARCHOS=x86_LINUX
    ;;

  # FreeBSD
  *i386*freebsd*|*amd64*freebsd*)
    if test x"${ARCH}" = x""; then
       ARCH=`uname -p`
    fi

    AC_MSG_RESULT(configuring for $target)
    ARCHOS=${ARCH}_FREEBSD
    ;;

  # Mac OS X
  *86*darwin*)
    AC_MSG_RESULT(configuring for $target)
    ARCHOS=x86_DARWIN
    ;;

  # Cygwin
  *86*cygwin*)
    AC_MSG_RESULT(configuring for $target)
    ARCHOS=x86_WIN32

    # override IVYHOME; even on cygwin we want forward slashes
    # sm: I folded this into what I hope will be the only
    # case-analysis of machine type
    # IVYHOME=`cygpath -wa "$IVYHOME"  | sed -e "s/\\\\\/\\//g"`
    # Try to use the Unix paths even on cygwin. The newest versions of make
    #  do not like colons in file names
    IVYHOME=`cygpath -u "$IVYHOME"`
    CC=`which $CC`
    CC=`cygpath -wa "$CC"  | sed -e "s/\\\\\/\\//g"`
    ;;

  *)
    AC_MSG_ERROR([
      Unsupported platform $target -- sorry.
      ./configure supports these platforms:
         on x86:     Linux, Cygwin, FreeBSD, OpenBSD, Darwin
    ])
    ;;
esac

AC_CHECK_FILE(obj/$ARCHOS,, AC_MSG_RESULT(creating obj/$ARCHOS);
                            mkdir -p obj/$ARCHOS)


LINUX_MSG="n/a"
USE_LINUX="no"
AC_ARG_WITH(linux,
  [  --with-linux[[=PATH]]     enable Linux kernel support],
  [ if test "x$withval" = "x" ; then
      AC_MSG_ERROR([No Linux kernel path provided])
    else
      if test "x$withval" != "xno" ; then
        USE_LINUX="yes"
        LINUX_MSG="$withval"
        LINUX_DIR="$withval"
        AC_SUBST(LINUX_DIR)
      fi
    fi ])
AC_SUBST(USE_LINUX)

USE_MINE_OCT="no"
AC_ARG_WITH(mine-oct,
  [  --with-mine-oct   use Mine's Octagon library],
  [ USE_MINE_OCT="yes"])
AC_SUBST(USE_MINE_OCT)

USE_CVCL="no"
AC_ARG_WITH(cvcl,
  [  --with-cvcl       use the CVCL solver],
  [ USE_CVCL="yes"])
AC_SUBST(USE_CVCL)

USE_YICES="no"
AC_ARG_WITH(yices,
  [  --with-yices      use the Yices solver],
  [ USE_YICES="yes"])
AC_SUBST(USE_YICES)

USE_SATURN="no"
AC_ARG_WITH(saturn,
  [  --with-saturn[[=PATH]]   enable use of Saturn analysis],
  [  if test "x$withval" = "x" ; then
       AC_MSG_ERROR([No Saturn path provided])
     else
       if test "x$withval" != "xno" ; then
         USE_SATURN="yes"
         SATURNHOME="$withval"
         AC_SUBST(SATURNHOME)
       fi
     fi ])
AC_SUBST(USE_SATURN)

#We can't use AC_CONFIG_SUBDIRS because it doesn't support adding new
#flags (--with-zrapp):
# AC_CONFIG_SUBDIRS(cil)
if test -f cil/configure; then
    AC_MSG_NOTICE(Configuring CIL:);
    cd cil; ./configure --with-zrapp; cd ..
else  
    AC_MSG_ERROR(Missing the CIL directory)
fi


AC_SUBST(ARCHOS)
AC_SUBST(IVYHOME)
AC_SUBST(DEFAULT_CIL_MODE)
AC_SUBST(IVY_VERSION)
AC_SUBST(CVCLLIB)
AC_SUBST(CVCLINC)
AC_SUBST(OCAMLINC)

# finish the configure script and generate various files; ./configure
# will apply variable substitutions to <filename>.in to generate <filename>;
# I find it useful to mark generated files as read-only so I don't
# accidentally edit them (and them lose my changes when ./configure
# runs again); I had originally done the chmod after AC_OUTPUT, but
# the problem is then the chmod doesn't run inside ./config.status

# MY_AC_CONFIG_FILES(filename)
# do AC_CONFIG_FILES(filename, chmod a-w filename)
define([MY_AC_CONFIG_FILES],
[{
  if test -f [$1].in; then
    AC_CONFIG_FILES([$1], chmod a-w [$1])
  else
    true
    #echo "skipping [$1] because it's not in this distribution"
  fi
}])
define([MY_AC_CONFIG_EXE_FILES],
[{
  if test -f [$1].in; then
    AC_CONFIG_FILES([$1], [chmod a-w,a+x $1])
  else
    true
    #echo "skipping [$1] because it's not in this distribution"
  fi
}])

MY_AC_CONFIG_FILES(Makefile)
MY_AC_CONFIG_FILES(deputy-lib/Makefile)
MY_AC_CONFIG_FILES(heapsafe-lib/Makefile)
MY_AC_CONFIG_FILES(sharC-lib/Makefile)
MY_AC_CONFIG_FILES(test/Makefile)
MY_AC_CONFIG_FILES(test/Makefile.ivy)

AC_OUTPUT()

cat <<EOF

Ivy configuration:
  Ivy home:                   $IVYHOME
  Ivy version:                $IVY_VERSION
  Linux path:                 $LINUX_MSG
EOF
