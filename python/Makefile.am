## -*- coding: utf-8 -*-
## Copyright (C) 2010, 2011, 2013-2017 Laboratoire de Recherche
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

AUTOMAKE_OPTIONS = subdir-objects

AM_CPPFLAGS = -I$(PYTHONINC) -I$(top_builddir) -I$(top_srcdir) \
	      $(BUDDY_CPPFLAGS) -DSWIG_TYPE_TABLE=spot

# Disable fastproxy, because IPython 2 bogusly ignores _repr_latex_
# when -fastproxy is used.
#   https://github.com/ipython/ipython/issues/7003
# Once a fixed version of IPython hits Debian stable, we can remove
# this.
SWIGFLAGS = -c++ -python -py3 -O -nofastproxy -MD

EXTRA_DIST = buddy.i spot/impl.i spot/ltsmin.i spot/gen.i
nobase_python_PYTHON = \
  spot/__init__.py \
  spot/aux.py \
  spot/impl.py \
  spot/ltsmin.py \
  spot/gen.py \
  buddy.py
nobase_pyexec_LTLIBRARIES = _buddy.la spot/_impl.la \
  spot/_ltsmin.la spot/_gen.la

MAINTAINERCLEANFILES = \
  $(srcdir)/spot/impl_wrap.cxx $(srcdir)/spot/impl.py \
  $(srcdir)/spot/ltsmin_wrap.cxx $(srcdir)/spot/ltsmin.py \
  $(srcdir)/spot/gen_wrap.cxx $(srcdir)/spot/gen.py \
  $(srcdir)/buddy_wrap.cxx $(srcdir)/buddy.py

## spot

spot__impl_la_SOURCES = spot/impl_wrap.cxx
spot__impl_la_LDFLAGS = -avoid-version -module $(SYMBOLIC_LDFLAGS)
spot__impl_la_LIBADD = $(top_builddir)/spot/libspot.la

@AMDEP_TRUE@@am__include@ @am__quote@./spot/$(DEPDIR)/impl_wrap.Pcxx@am__quote@

${srcdir}/spot/impl_wrap.cxx: spot/impl.i
	$(SWIG) $(SWIGFLAGS) -I$(srcdir) -I$(top_srcdir) -MF spot/$(DEPDIR)/impl_wrap.TPcxx $(srcdir)/spot/impl.i
	mv spot/$(DEPDIR)/impl_wrap.TPcxx spot/$(DEPDIR)/impl_wrap.Pcxx

spot/impl.py: spot/impl.i
	$(MAKE) $(AM_MAKEFLAGS) spot/impl_wrap.cxx


## spot-ltsmin

spot__ltsmin_la_SOURCES = spot/ltsmin_wrap.cxx
spot__ltsmin_la_LDFLAGS = -avoid-version -module $(SYMBOLIC_LDFLAGS)
spot__ltsmin_la_LIBADD = $(top_builddir)/spot/libspot.la \
                       $(top_builddir)/spot/ltsmin/libspotltsmin.la

@AMDEP_TRUE@@am__include@ @am__quote@./spot/$(DEPDIR)/ltsmin_wrap.Pcxx@am__quote@

${srcdir}/spot/ltsmin_wrap.cxx: spot/ltsmin.i
	$(SWIG) $(SWIGFLAGS) -I$(srcdir) -I$(top_srcdir) -MF spot/$(DEPDIR)/ltsmin_wrap.TPcxx $(srcdir)/spot/ltsmin.i
	mv spot/$(DEPDIR)/ltsmin_wrap.TPcxx spot/$(DEPDIR)/ltsmin_wrap.Pcxx

spot/ltsmin.py: spot/ltsmin.i
	$(MAKE) $(AM_MAKEFLAGS) spot/ltsmin_wrap.cxx


## spot-gen

spot__gen_la_SOURCES = spot/gen_wrap.cxx
spot__gen_la_LDFLAGS = -avoid-version -module $(SYMBOLIC_LDFLAGS)
spot__gen_la_LIBADD = $(top_builddir)/spot/libspot.la \
                       $(top_builddir)/spot/gen/libspotgen.la

@AMDEP_TRUE@@am__include@ @am__quote@./spot/$(DEPDIR)/gen_wrap.Pcxx@am__quote@

${srcdir}/spot/gen_wrap.cxx: spot/gen.i
	$(SWIG) $(SWIGFLAGS) -I$(srcdir) -I$(top_srcdir) -MF spot/$(DEPDIR)/gen_wrap.TPcxx $(srcdir)/spot/gen.i
	mv spot/$(DEPDIR)/gen_wrap.TPcxx spot/$(DEPDIR)/gen_wrap.Pcxx

spot/gen.py: spot/gen.i
	$(MAKE) $(AM_MAKEFLAGS) spot/gen_wrap.cxx


## buddy

_buddy_la_SOURCES = buddy_wrap.cxx
_buddy_la_LDFLAGS = -avoid-version -module $(BUDDY_LDFLAGS) $(SYMBOLIC_LDFLAGS)

@AMDEP_TRUE@@am__include@ @am__quote@./$(DEPDIR)/buddy_wrap.Pcxx@am__quote@

${srcdir}/buddy_wrap.cxx: buddy.i
	$(SWIG) $(SWIGFLAGS) $(BUDDY_CPPFLAGS) -MF $(DEPDIR)/buddy_wrap.TPcxx $(srcdir)/buddy.i
	mv $(DEPDIR)/buddy_wrap.TPcxx $(DEPDIR)/buddy_wrap.Pcxx

buddy.py: buddy.i
	$(MAKE) $(AM_MAKEFLAGS) buddy_wrap.cxx
