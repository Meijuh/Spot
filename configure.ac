# -*- coding: utf-8 -*-
# Copyright (C) 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016,
# 2017 Laboratoire de Recherche et Développement de l'Epita (LRDE).
# Copyright (C) 2003, 2004, 2005, 2006, 2007 Laboratoire
# d'Informatique de Paris 6 (LIP6), département Systèmes Répartis
# Coopératifs (SRC), Université Pierre et Marie Curie.
#
# This file is part of Spot, a model checking library.
#
# Spot is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# Spot is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

AC_PREREQ([2.61])
AC_INIT([spot], [2.3.0.dev], [spot@lrde.epita.fr])
AC_CONFIG_AUX_DIR([tools])
AC_CONFIG_MACRO_DIR([m4])
AM_INIT_AUTOMAKE([1.11 gnu tar-ustar color-tests parallel-tests])
AC_CONFIG_HEADERS([config.h])dnl Private config, not to be used in .hh files.
AX_PREFIX_CONFIG_H([spot/misc/_config.h])dnl Public config, for .hh files.

# If the user didn't supply a CFLAGS value,
# set an empty one to prevent autoconf to stick -O2 -g here.
test -z "$CFLAGS" && CFLAGS=
test -z "$CXXFLAGS" && CXXFLAGS=

adl_ENABLE_DEVEL

AC_PROG_CC
gl_EARLY

AM_PROG_CC_C_O
AC_PROG_CXX

AM_PROG_LEX
adl_CHECK_BISON

# Decrease verbosity when passing argument V=0
AM_SILENT_RULES([no])

# Option to activate C/C++14
AC_ARG_ENABLE([c++14],
              [AC_HELP_STRING([--enable-c++14],
                              [Use C++14.])],
              [enable_14=yes], [enable_14=no])

# Activate at C11 for gnulib tests
if test x"${enable_14}" = xyes; then
  AX_CHECK_COMPILE_FLAG([-std=c14], [CFLAGS="$CFLAGS -std=c14"])
else
  AX_CHECK_COMPILE_FLAG([-std=c11], [CFLAGS="$CFLAGS -std=c11"])
fi

gl_INIT

# Use -Werror since using -fvisibility under MinGW is only a warning.
# (The option is ignored anyway since this does not make sense under windows).
AX_CHECK_COMPILE_FLAG([-Werror -fvisibility=hidden],
  [CFLAGS="$CFLAGS -fvisibility=hidden"])
AC_LANG(C++)
AX_CHECK_COMPILE_FLAG([-Werror -fvisibility=hidden],
  [CXXFLAGS="$CXXFLAGS -fvisibility=hidden"
  AX_CHECK_COMPILE_FLAG([-fvisibility-inlines-hidden],
    [CXXFLAGS="$CXXFLAGS -fvisibility-inlines-hidden"])])
CXXFLAGS="$CXXFLAGS -DSPOT_BUILD"

# Turn on C++11 support
m4_define([_AX_CXX_COMPILE_STDCXX_11_testbody],
[AC_LANG_SOURCE([#include <memory>
#include <string>
#include <chrono>  // fails with some installation of clang
#include <map>

    template <typename T>
    struct check
    {
      static_assert(sizeof(int) <= sizeof(T), "not big enough");
    };

    typedef check<check<bool>> right_angle_brackets;

    auto f = std::make_shared<std::string>("shared_ptr");

    int a;
    decltype(a) b;

    typedef check<int> check_type;
    check_type c;
    check_type&& cr = static_cast<check_type&&>(c);

    auto d = a;

    void test_emplace()
    {
       std::map<int, int> m;
       m.emplace(1, 2); // fails with g++ 4.6
    }
])])

# Turn on C++14 support
# This is currently a copy of the above code for C++11, feel free to add
# further tests here when necessary.
m4_define([_AX_CXX_COMPILE_STDCXX_14_testbody],
[AC_LANG_SOURCE([#include <memory>
#include <string>
#include <chrono>  // fails with some installation of clang
#include <map>

    template <typename T>
    struct check
    {
      static_assert(sizeof(int) <= sizeof(T), "not big enough");
    };

    typedef check<check<bool>> right_angle_brackets;

    auto f = std::make_shared<std::string>("shared_ptr");

    int a;
    decltype(a) b;

    typedef check<int> check_type;
    check_type c;
    check_type&& cr = static_cast<check_type&&>(c);

    auto d = a;

    void test_emplace()
    {
       std::map<int, int> m;
       m.emplace(1, 2); // fails with g++ 4.6
    }
])])

if test x"${enable_14}" = xyes; then
  for f in -std=c++14 '-std=c++14 -stdlib=libc++' -std=c++1y
  do
    AX_CHECK_COMPILE_FLAG([$f], [CXXFLAGS="$CXXFLAGS $f" stdpass=true], [], [],
                          [_AX_CXX_COMPILE_STDCXX_14_testbody])
    ${stdpass-false} && break
  done
  if ! "${stdpass-false}"; then
    AC_ERROR([unable to turn on C++14 mode with this compiler])
  fi
else
  for f in -std=c++11 '-std=c++11 -stdlib=libc++' -std=c++0x
  do
    AX_CHECK_COMPILE_FLAG([$f], [CXXFLAGS="$CXXFLAGS $f" stdpass=true], [], [],
                          [_AX_CXX_COMPILE_STDCXX_11_testbody])
    ${stdpass-false} && break
  done
  if ! "${stdpass-false}"; then
    AC_ERROR([unable to turn on C++11 mode with this compiler])
  fi
fi

AX_CHECK_BUDDY

AC_CHECK_HEADERS([sys/times.h])
AC_CHECK_FUNCS([times kill alarm sigaction])

LT_CONFIG_LTDL_DIR([ltdl])
LT_INIT([win32-dll])
LTDL_INIT([subproject convenience])
# Debian resets this to no, but this break both Spot and the libtool
# test suite itself.  Instead of requiring developer to install a
# non-patched version of Libtool on any Debian they use, we just
# cancel the effect of Debian's patch here.
link_all_deplibs=yes
link_all_deplibs_CXX=yes

AX_BSYMBOLIC

AC_ARG_ENABLE([python],
              [AC_HELP_STRING([--disable-python],
                              [do not compile Python bindings])],
              [], [enable_python=yes])

case $enable_shared:$enable_python in
 no:no);;
 no:*)
    enable_python=no
    AC_MSG_NOTICE([Not building Python bindings because of --disable-shared.])
    ;;
esac

AM_CONDITIONAL([USE_PYTHON], [test "x${enable_python:-yes}" = xyes])

AM_CONDITIONAL([USE_LTSMIN], [test "x${enable_shared:-yes}" = xyes])

if test "x${enable_python:-yes}" = xyes; then
  AC_MSG_NOTICE([You may configure with --disable-python ]dnl
[if you do not need Python bindings.])
  adl_CHECK_PYTHON
fi


adl_ENABLE_DEBUG
ad_GCC_OPTIM
adl_NDEBUG
adl_ENABLE_GLIBCXX_DEBUG

spot_INTEL
if test x$enable_warnings = xyes; then
  CF_GXX_WARNINGS
fi

AM_CONDITIONAL([NEVER], [false])
# We need the absolute path for dot in the "doc/dot" script. Other places
# only require a relative path.
AC_PATH_PROG([DOT], [dot])
AC_CHECK_PROG([LBT], [lbt], [lbt])
AC_CHECK_PROG([LTL2BA], [ltl2ba], [ltl2ba])
AC_CHECK_PROG([LTL3BA], [ltl3ba], [ltl3ba])
AC_CHECK_PROG([MODELLA], [modella], [modella])
AC_CHECK_PROG([LTL2NBA], [script4lbtt.py], [script4lbtt.py])
AC_CHECK_PROG([PERL], [perl], [perl])
AC_CHECK_PROG([SPIN], [spin], [spin])
AC_CHECK_PROG([LBTT], [lbtt], [lbtt])
AC_CHECK_PROG([EMACS], [emacs], [emacs])
AC_CHECK_PROGS([IPYTHON], [ipython3 ipython], [ipython])
AC_CHECK_PROG([LBTT_TRANSLATE], [lbtt-translate], [lbtt-translate])
AX_CHECK_VALGRIND
AC_CHECK_PROG([WRING2LBTT], [wring2lbtt], [wring2lbtt])
# Debian has a binary for SWIG 3.0 named swig3.0 and they kept swig as
# an alias for swig-2.0.  Let's use the former when available.
AC_CHECK_PROGS([SWIG], [swig3.0 swig], [swig])

AC_SUBST([CROSS_COMPILING], [$cross_compiling])

AC_SUBST([GITPATCH], [$(if (git rev-parse) >/dev/null 2>&1; then
 echo ".$(git rev-list $(git rev-list --tags --no-walk --max-count=1)..HEAD \
 --count)"
fi)])

AC_CONFIG_FILES([
  Makefile
  bin/Makefile
  bin/man/Makefile
  bench/Makefile
  bench/dtgbasat/Makefile
  bench/emptchk/Makefile
  bench/emptchk/defs
  bench/ltlcounter/Makefile
  bench/ltlclasses/Makefile
  bench/ltl2tgba/Makefile
  bench/ltl2tgba/defs
  bench/spin13/Makefile
  bench/wdba/Makefile
  bench/stutter/Makefile
  doc/Doxyfile
  doc/Makefile
  doc/tl/Makefile
  doc/org/.dir-locals.el
  doc/org/init.el
  elisp/Makefile
  lib/Makefile
  picosat/Makefile
  spot/graph/Makefile
  spot/kripke/Makefile
  spot/ltsmin/Makefile
  spot/Makefile
  spot/misc/Makefile
  spot/parseaut/Makefile
  spot/parsetl/Makefile
  spot/priv/Makefile
  spot/taalgos/Makefile
  spot/ta/Makefile
  spot/tl/Makefile
  spot/twaalgos/gtec/Makefile
  spot/twaalgos/Makefile
  spot/twa/Makefile
  python/ajax/Makefile
  python/Makefile
  tests/core/defs
  tests/ltsmin/defs:tests/core/defs.in
  tests/Makefile
  tools/x-to-1
])
AC_CONFIG_FILES([doc/org/g++wrap], [chmod +x doc/org/g++wrap])
AC_CONFIG_FILES([doc/dot], [chmod +x doc/dot])
AC_CONFIG_FILES([tests/run], [chmod +x tests/run])
AC_OUTPUT

case $VERSION:$enable_devel in
  *[[abcdefghijklmnopqrstuvwxyz]]:yes)
    echo
    echo '==================================================================='
    echo ' This is a development version of Spot: Assertions and debuging    '
    echo ' code are enabled by default.  If you find this too slow or        '
    echo ' plan to do some benchmarking, run configure with --disable-devel. '
    echo '==================================================================='
  ;;
esac
