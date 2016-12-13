AC_PREREQ([2.57])
AC_INIT([buddy], [2.3a])
AC_CONFIG_AUX_DIR([tools])
AC_CONFIG_MACRO_DIR([m4])
AM_INIT_AUTOMAKE([foreign nostdinc no-define 1.7.3])

# If the user didn't supply a CFLAGS value,
# set an empty one to prevent autoconf to stick -O2 -g here.
test -z "$CFLAGS" && CFLAGS=
test -z "$CXXFLAGS" && CXXFLAGS=

adl_ENABLE_DEVEL

AC_PROG_CC

AM_PROG_LEX
AC_PROG_YACC

AC_PROG_CXX

# Option to activate C/C++14
AC_ARG_ENABLE([c++14],
              [AC_HELP_STRING([--enable-c++14],
                              [Use C++14.])],
              [enable_14=yes], [enable_14=no])

LT_INIT([win32-dll])
AX_BSYMBOLIC

# Use -Werror since using -fvisibility under MinGW is only a warning.
# (The option is ignored anyway since this does not make sense under windows).
AX_CHECK_COMPILE_FLAG([-Werror -fvisibility=hidden],
  [CFLAGS="$CFLAGS -fvisibility=hidden"])
AC_LANG(C++)
AX_CHECK_COMPILE_FLAG([-Werror -fvisibility=hidden],
  [CXXFLAGS="$CXXFLAGS -fvisibility=hidden"
  AX_CHECK_COMPILE_FLAG([-fvisibility-inlines-hidden],
    [CXXFLAGS="$CXXFLAGS -fvisibility-inlines-hidden"])])
AC_LANG(C)


adl_ENABLE_DEBUG
ad_GCC_OPTIM
adl_NDEBUG

buddy_INTEL
buddy_DEBUG_FLAGS

if test x$enable_warnings = xyes; then
  CF_GCC_WARNINGS
fi

# Turn on C++11 support
AC_LANG(C++)
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

AC_CONFIG_HEADERS([config.h])

AC_CONFIG_FILES([
  Makefile
  src/Makefile
  doc/Makefile
  examples/Makefile
  examples/adder/Makefile
  examples/bddcalc/Makefile
  examples/bddtest/Makefile
  examples/cmilner/Makefile
  examples/fdd/Makefile
  examples/milner/Makefile
  examples/money/Makefile
  examples/queen/Makefile
  examples/solitare/Makefile
])

AC_OUTPUT
