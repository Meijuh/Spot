## -*- coding: utf-8 -*-
## Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014, 2015 Laboratoire de
## Recherche et Développement de l'Epita (LRDE).
## Copyright (C) 2003, 2004, 2005, 2006 Laboratoire d'Informatique de
## Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
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

AM_CPPFLAGS = -I$(srcdir)/.. -I.. $(BUDDY_CPPFLAGS)
AM_CXXFLAGS = $(WARNING_CXXFLAGS)
LDADD = ../libspot.la

# These are the most used test programs, and they are also useful
# to run manually outside the test suite.  Always build them.
noinst_PROGRAMS = ltl2tgba randtgba

check_SCRIPTS = defs
# Keep this sorted alphabetically.
check_PROGRAMS = \
  acc \
  bitvect \
  complement \
  checkpsl \
  checkta \
  emptchk \
  intvcomp \
  intvcmp2 \
  ltlprod \
  readsat \
  taatgba

# Keep this sorted alphabetically.
acc_SOURCES = acc.cc
bitvect_SOURCES  = bitvect.cc
checkpsl_SOURCES = checkpsl.cc
checkta_SOURCES = checkta.cc
complement_SOURCES = complementation.cc
emptchk_SOURCES  = emptchk.cc
intvcomp_SOURCES = intvcomp.cc
intvcmp2_SOURCES = intvcmp2.cc
ltl2tgba_SOURCES = ltl2tgba.cc
ltlprod_SOURCES  = ltlprod.cc
randtgba_SOURCES = randtgba.cc
readsat_SOURCES = readsat.cc
taatgba_SOURCES = taatgba.cc

# Keep this sorted by STRENGTH.  Test basic things first,
# because such failures will be easier to diagnose and fix.
TESTS = \
  acc.test \
  acc2.test \
  intvcomp.test \
  bitvect.test \
  ltlcross3.test \
  taatgba.test \
  renault.test \
  nondet.test \
  det.test \
  neverclaimread.test \
  hoaparse.test \
  remfin.test \
  dstar.test \
  readsave.test \
  ltldo.test \
  ltldo2.test \
  maskacc.test \
  maskkeep.test \
  simdet.test \
  sim2.test \
  ltl2tgba.test \
  ltl2neverclaim.test \
  ltl2neverclaim-lbtt.test \
  ltlprod.test \
  explprod.test \
  explpro2.test \
  explpro3.test \
  explpro4.test \
  tripprod.test \
  dupexp.test \
  exclusive.test \
  remprop.test \
  degendet.test \
  degenid.test \
  degenlskip.test \
  kv.test \
  randomize.test \
  lbttparse.test \
  scc.test \
  sccdot.test \
  sccsimpl.test \
  dbacomp.test \
  obligation.test \
  wdba.test \
  wdba2.test \
  babiak.test \
  monitor.test \
  dra2dba.test \
  ltlcross4.test \
  ltl2dstar.test \
  ltl2dstar2.test \
  ltl2dstar3.test \
  ltl2ta.test \
  ltl2ta2.test \
  randaut.test \
  randtgba.test \
  isomorph.test \
  uniq.test \
  sbacc.test \
  stutter.test \
  emptchk.test \
  emptchke.test \
  dfs.test \
  ltlcrossce.test \
  ltlcrossce2.test \
  emptchkr.test \
  ltlcounter.test \
  basimul.test \
  satmin.test \
  satmin2.test \
  spotlbtt.test \
  ltlcross.test \
  spotlbtt2.test \
  ltlcross2.test \
  complementation.test \
  randpsl.test \
  cycles.test

EXTRA_DIST = $(TESTS)

distclean-local:
	rm -rf $(TESTS:.test=.dir)
