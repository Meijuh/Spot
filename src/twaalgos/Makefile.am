## -*- coding: utf-8 -*-
## Copyright (C) 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015 Laboratoire
## de Recherche et Développement de l'Epita (LRDE).
## Copyright (C) 2003, 2004, 2005 Laboratoire d'Informatique de Paris
## 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
## Université Pierre et Marie Curie.
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

SUBDIRS = gtec

AM_CPPFLAGS = -I$(srcdir)/.. -I.. $(BUDDY_CPPFLAGS)
AM_CXXFLAGS = $(WARNING_CXXFLAGS)

twaalgosdir = $(pkgincludedir)/twaalgos

twaalgos_HEADERS = \
  are_isomorphic.hh \
  bfssteps.hh \
  canonicalize.hh \
  cleanacc.hh \
  complete.hh \
  compsusp.hh \
  cycles.hh \
  dtgbacomp.hh \
  degen.hh \
  dotty.hh \
  dtbasat.hh \
  dtgbasat.hh \
  dupexp.hh \
  emptiness.hh \
  emptiness_stats.hh \
  gv04.hh \
  hoa.hh \
  isdet.hh \
  isweakscc.hh \
  lbtt.hh \
  ltl2taa.hh \
  ltl2tgba_fm.hh \
  magic.hh \
  mask.hh \
  minimize.hh \
  neverclaim.hh \
  postproc.hh \
  powerset.hh \
  product.hh \
  projrun.hh \
  randomgraph.hh \
  randomize.hh \
  reachiter.hh \
  reducerun.hh \
  relabel.hh \
  remfin.hh \
  remprop.hh \
  replayrun.hh \
  safety.hh \
  sbacc.hh \
  sccfilter.hh \
  scc.hh \
  sccinfo.hh \
  se05.hh \
  simulation.hh \
  stats.hh \
  stripacc.hh \
  stutter.hh \
  tau03.hh \
  tau03opt.hh \
  totgba.hh \
  translate.hh \
  word.hh

noinst_LTLIBRARIES = libtwaalgos.la
libtwaalgos_la_SOURCES = \
  are_isomorphic.cc \
  bfssteps.cc \
  canonicalize.cc \
  cleanacc.cc \
  complete.cc \
  compsusp.cc \
  cycles.cc \
  dtgbacomp.cc \
  degen.cc \
  dotty.cc \
  dtbasat.cc \
  dtgbasat.cc \
  dupexp.cc \
  emptiness.cc \
  gv04.cc \
  hoa.cc \
  isdet.cc \
  isweakscc.cc \
  lbtt.cc \
  ltl2taa.cc \
  ltl2tgba_fm.cc \
  magic.cc \
  mask.cc \
  minimize.cc \
  ndfs_result.hxx \
  neverclaim.cc \
  postproc.cc \
  powerset.cc \
  product.cc \
  projrun.cc \
  randomgraph.cc \
  randomize.cc \
  reachiter.cc \
  reducerun.cc \
  remfin.cc \
  remprop.cc \
  replayrun.cc \
  relabel.cc \
  safety.cc \
  sbacc.cc \
  scc.cc \
  sccinfo.cc \
  sccfilter.cc \
  se05.cc \
  simulation.cc \
  stats.cc \
  stripacc.cc \
  stutter.cc \
  tau03.cc \
  tau03opt.cc \
  totgba.cc \
  translate.cc \
  weight.cc \
  weight.hh \
  word.cc

libtwaalgos_la_LIBADD = gtec/libgtec.la
