## -*- coding: utf-8 -*-
## Copyright (C) 2010, 2011, 2013, 2014, 2015 Laboratoire de Recherche et Development de
## l'Epita (LRDE).
## Copyright (C) 2003, 2004  Laboratoire d'Informatique de Paris 6 (LIP6),
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

SUBDIRS = . ajax tests

AM_CPPFLAGS = -I$(PYTHONINC) -I$(top_srcdir)/src -I$(top_builddir)/src \
	      $(BUDDY_CPPFLAGS) -DSWIG_TYPE_TABLE=spot

EXTRA_DIST = spot_impl.i buddy.i
python_PYTHON = $(srcdir)/spot_impl.py $(srcdir)/buddy.py spot.py
pyexec_LTLIBRARIES = _spot_impl.la _buddy.la

MAINTAINERCLEANFILES = \
  $(srcdir)/spot_impl_wrap.cxx $(srcdir)/spot_impl.py \
  $(srcdir)/buddy_wrap.cxx $(srcdir)/buddy.py

## spot

_spot_impl_la_SOURCES = $(srcdir)/spot_impl_wrap.cxx
_spot_impl_la_LDFLAGS = -avoid-version -module $(SYMBOLIC_LDFLAGS)
_spot_impl_la_LIBADD = $(top_builddir)/src/libspot.la

$(srcdir)/spot_impl_wrap.cxx: $(srcdir)/spot_impl.i
	$(SWIG) -c++ -python -I$(srcdir) -I$(top_srcdir)/src $(srcdir)/spot_impl.i

$(srcdir)/spot_impl.py: $(srcdir)/spot_impl.i
	$(MAKE) $(AM_MAKEFLAGS) spot_impl_wrap.cxx


## buddy

_buddy_la_SOURCES = $(srcdir)/buddy_wrap.cxx
_buddy_la_LDFLAGS = -avoid-version -module $(BUDDY_LDFLAGS) $(SYMBOLIC_LDFLAGS)

$(srcdir)/buddy_wrap.cxx: $(srcdir)/buddy.i
	$(SWIG) -c++ -python $(BUDDY_CPPFLAGS) $(srcdir)/buddy.i

$(srcdir)/buddy.py: $(srcdir)/buddy.i
	$(MAKE) $(AM_MAKEFLAGS) buddy_wrap.cxx
