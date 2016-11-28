## -*- coding: utf-8 -*-
## Copyright (C) 2011, 2013, 2014, 2015, 2016 Laboratoire de Recherche
## et Developpement de l'Epita (LRDE).
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

AM_CPPFLAGS = -I$(top_builddir) -I$(top_srcdir) \
              $(BUDDY_CPPFLAGS) $(LTDLINCL)
AM_CXXFLAGS = $(WARNING_CXXFLAGS)

ltsmindir = $(pkgincludedir)/ltsmin

ltsmin_HEADERS = ltsmin.hh

lib_LTLIBRARIES = libspotltsmin.la
libspotltsmin_la_DEPENDENCIES = \
  $(top_builddir)/spot/libspot.la \
  $(LTDLDEPS)
libspotltsmin_la_LIBADD = \
  $(top_builddir)/spot/libspot.la \
  $(LIBLTDL) -lpthread
libspotltsmin_la_LDFLAGS = -no-undefined $(SYMBOLIC_LDFLAGS)
libspotltsmin_la_SOURCES = ltsmin.cc
