## -*- coding: utf-8 -*-
## Copyright (C) 2011, 2013, 2014, 2015 Laboratoire de Recherche et
## Developpement de l'Epita (LRDE).
##
## This file is part of Spot, a model checking library.
##
## Spot is free software; you can redistribute it and/or modify it
## under the terms of the GNU General Public License as published by
## the Free Software Foundation; either version 3 of the License, or
## (at your option) any later version.
##
## Spot is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
## or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
## License for more details.
##
## You should have received a copy of the GNU General Public License
## along with this program.  If not, see <http://www.gnu.org/licenses/>.

AM_CPPFLAGS = -I$(top_srcdir)/src -I$(top_builddir)/src \
              $(BUDDY_CPPFLAGS) -I$(top_srcdir)/ltdl
AM_CXXFLAGS = $(WARNING_CXXFLAGS)

ltsmindir = $(pkgincludedir)/iface/ltsmin

ltsmin_HEADERS = ltsmin.hh

lib_LTLIBRARIES = libspotltsmin.la
libspotltsmin_la_LIBADD = \
  $(top_builddir)/src/libspot.la \
  $(top_builddir)/ltdl/libltdlc.la -lpthread
libspotltsmin_la_LDFLAGS = -no-undefined $(SYMBOLIC_LDFLAGS)
libspotltsmin_la_SOURCES = ltsmin.cc

noinst_PROGRAMS = modelcheck

modelcheck_SOURCES = modelcheck.cc
modelcheck_LDADD = libspotltsmin.la

check_SCRIPTS = defs

TESTS = check.test finite.test finite2.test kripke.test
EXTRA_DIST = $(TESTS) beem-peterson.4.dve finite.dve finite.pm

kripke.test: $(top_builddir)/src/tests/parse_print$(EXEEXT)

$(top_builddir)/src/tests/parse_print$(EXEEXT):
	cd $(top_builddir)/src/tests && \
	$(MAKE) $(AM_MAKEFLAGS) parse_print$(EXEEXT)

distclean-local:
	rm -rf $(TESTS:.test=.dir)
