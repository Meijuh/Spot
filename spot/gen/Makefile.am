## -*- coding: utf-8 -*-
## Copyright (C) 2017 Laboratoire de Recherche et Développement de l'Epita
## (LRDE).
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

AM_CPPFLAGS = -I$(top_builddir) -I$(top_srcdir) $(BUDDY_CPPFLAGS)
AM_CXXFLAGS = $(WARNING_CXXFLAGS)

spotgendir = $(pkgincludedir)/gen
spotgen_HEADERS = automata.hh

lib_LTLIBRARIES = libspotgen.la
libspotgen_la_SOURCES = \
  automata.cc
#libspotgen_la_LDFLAGS = $(BUDDY_LDFLAGS) -no-undefined $(SYMBOLIC_LDFLAGS)

