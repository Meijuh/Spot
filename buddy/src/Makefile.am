
include_HEADERS = bdd.h fdd.h bvec.h

BUDDY_FLAGS = -I$(top_builddir) -DVERSION=23 \
  -fvisibility=hidden -DBUDDY_DLL_EXPORTS -DBUDDY_DLL

# Compile the C++ part of the library with
# -fvisibility-inlines-hidden, this option is not valid for C.
lib_LTLIBRARIES = libbdd.la
libbdd_la_CPPFLAGS = $(BUDDY_FLAGS) -fvisibility-inlines-hidden
libbdd_la_SOURCES = cppext.cxx
libbdd_la_LIBADD = libbdd_c.la
# See the `Updating version info' node of the Libtool manual before
# changing this.
libbdd_la_LDFLAGS = -no-undefined -version-info 0:0:0

# The C part of the library.
noinst_LTLIBRARIES = libbdd_c.la
libbdd_c_la_CPPFLAGS = $(BUDDY_FLAGS)
libbdd_c_la_SOURCES = \
 bddio.c \
 bddop.c \
 bddtree.h \
 bvec.c \
 cache.c \
 cache.h \
 fdd.c \
 imatrix.c \
 imatrix.h \
 kernel.c \
 kernel.h \
 pairs.c \
 prime.c \
 prime.h \
 reorder.c \
 tree.c

check_PROGRAMS = bddtest
bddtest_SOURCES = bddtest.cxx
bddtest_CPPFLAGS = -I$(top_builddir)
bddtest_LDADD = ./libbdd.la
