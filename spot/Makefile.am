## -*- coding: utf-8 -*-
## Copyright (C) 2009, 2010, 2012, 2013, 2014, 2015, 2016 Laboratoire
## de Recherche et Développement de l'Epita (LRDE).
## Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
## département Systèmes Répartis Coopératifs (SRC), Université Pierre
## et Marie Curie.
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

AUTOMAKE_OPTIONS = subdir-objects

# List directories in the order they must be built.  Keep tests at the
# end, after building '.' (since the current directory contains
# libspot.la needed by the tests)
SUBDIRS = misc priv tl graph twa twaalgos ta taalgos kripke	\
          parseaut parsetl . ltsmin

lib_LTLIBRARIES = libspot.la
libspot_la_SOURCES =
libspot_la_LDFLAGS = $(BUDDY_LDFLAGS) -no-undefined $(SYMBOLIC_LDFLAGS)
libspot_la_LIBADD =  \
  kripke/libkripke.la \
  misc/libmisc.la \
  parseaut/libparseaut.la \
  parsetl/libparsetl.la \
  priv/libpriv.la \
  taalgos/libtaalgos.la \
  ta/libta.la \
  tl/libtl.la \
  twaalgos/libtwaalgos.la \
  twa/libtwa.la \
  ../lib/libgnu.la \
  ../picosat/libpico.la

# Dummy C++ source to cause C++ linking.
nodist_EXTRA_libspot_la_SOURCES = _.cc
_.cc:; touch $@
