## -*- coding: utf-8 -*-
## Copyright (C) 2010, 2011, 2013, 2014, 2015, 2016 Laboratoire de Recherche
## et Development de l'Epita (LRDE).
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

SUBDIRS = . ajax

AM_CPPFLAGS = -I$(PYTHONINC) -I$(top_builddir) -I$(top_srcdir) \
	      $(BUDDY_CPPFLAGS) -DSWIG_TYPE_TABLE=spot

# Disable fastproxy, because IPython 2 bogusly ignores _repr_latex_
# when -fastproxy is used.
#   https://github.com/ipython/ipython/issues/7003
# Once a fixed version of IPython hits Debian stable, we can remove
# this.
SWIGFLAGS = -c++ -python -py3 -O -nofastproxy

EXTRA_DIST = buddy.i spot/impl.i spot/ltsmin.i
python_PYTHON = \
  $(srcdir)/spot/__init__.py \
  $(srcdir)/spot/impl.py \
  $(srcdir)/spot/ltsmin.py \
  $(srcdir)/buddy.py
pyexec_LTLIBRARIES = _buddy.la spot/_impl.la spot/_ltsmin.la

MAINTAINERCLEANFILES = \
  $(srcdir)/spot/impl_wrap.cxx $(srcdir)/spot/impl.py \
  $(srcdir)/spot/ltsmin_wrap.cxx $(srcdir)/spot/ltsmin.py \
  $(srcdir)/buddy_wrap.cxx $(srcdir)/buddy.py

## spot

spot__impl_la_SOURCES = $(srcdir)/spot/impl_wrap.cxx
spot__impl_la_LDFLAGS = -avoid-version -module $(SYMBOLIC_LDFLAGS)
spot__impl_la_LIBADD = $(top_builddir)/spot/libspot.la

$(srcdir)/spot/impl_wrap.cxx: $(srcdir)/spot/impl.i
	$(SWIG) $(SWIGFLAGS) -I$(srcdir) -I$(top_srcdir) $(srcdir)/spot/impl.i

$(srcdir)/spot/impl.py: $(srcdir)/spot/impl.i
	$(MAKE) $(AM_MAKEFLAGS) spot/impl_wrap.cxx


## spot-ltsmin

spot__ltsmin_la_SOURCES = $(srcdir)/spot/ltsmin_wrap.cxx
spot__ltsmin_la_LDFLAGS = -avoid-version -module $(SYMBOLIC_LDFLAGS)
spot__ltsmin_la_LIBADD = $(top_builddir)/spot/libspot.la \
                       $(top_builddir)/spot/ltsmin/libspotltsmin.la

$(srcdir)/spot/ltsmin_wrap.cxx: $(srcdir)/spot/ltsmin.i
	$(SWIG) $(SWIGFLAGS) -I$(srcdir) -I$(top_srcdir) $(srcdir)/spot/ltsmin.i

$(srcdir)/spot/ltsmin.py: $(srcdir)/spot/ltsmin.i
	$(MAKE) $(AM_MAKEFLAGS) spot/ltsmin_wrap.cxx


## buddy

_buddy_la_SOURCES = $(srcdir)/buddy_wrap.cxx
_buddy_la_LDFLAGS = -avoid-version -module $(BUDDY_LDFLAGS) $(SYMBOLIC_LDFLAGS)

$(srcdir)/buddy_wrap.cxx: $(srcdir)/buddy.i
	$(SWIG) $(SWIGFLAGS) $(BUDDY_CPPFLAGS) $(srcdir)/buddy.i

$(srcdir)/buddy.py: $(srcdir)/buddy.i
	$(MAKE) $(AM_MAKEFLAGS) buddy_wrap.cxx
