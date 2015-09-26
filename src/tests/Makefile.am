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
noinst_PROGRAMS = ikwiad randtgba

check_SCRIPTS = defs
# Keep this sorted alphabetically.
check_PROGRAMS = \
  acc \
  bitvect \
  complement \
  checkpsl \
  checkta \
  consterm \
  emptchk \
  equals \
  graph \
  kind \
  length \
  intvcomp \
  intvcmp2 \
  ltlprod \
  ltl2dot \
  ltl2text \
  ltlrel \
  lunabbrev \
  nequals \
  nenoform \
  ngraph \
  parse_print \
  readsat \
  reduc \
  reduccmp \
  reduceu \
  reductaustr \
  syntimpl \
  taatgba \
  tgbagraph \
  tostring \
  tunabbrev \
  tunenoform

# Keep this sorted alphabetically.
acc_SOURCES = acc.cc
bitvect_SOURCES  = bitvect.cc
checkpsl_SOURCES = checkpsl.cc
checkta_SOURCES = checkta.cc
complement_SOURCES = complementation.cc
emptchk_SOURCES  = emptchk.cc
graph_SOURCES = graph.cc
ikwiad_SOURCES = ikwiad.cc
intvcomp_SOURCES = intvcomp.cc
intvcmp2_SOURCES = intvcmp2.cc
ltlprod_SOURCES  = ltlprod.cc
ngraph_SOURCES = ngraph.cc
parse_print_SOURCES = parse_print_test.cc
randtgba_SOURCES = randtgba.cc
readsat_SOURCES = readsat.cc
taatgba_SOURCES = taatgba.cc
tgbagraph_SOURCES = twagraph.cc
consterm_SOURCES = consterm.cc
equals_SOURCES = equalsf.cc
kind_SOURCES = kind.cc
length_SOURCES = length.cc
ltl2dot_SOURCES = readltl.cc
ltl2dot_CPPFLAGS = $(AM_CPPFLAGS) -DDOTTY
ltl2text_SOURCES = readltl.cc
ltlrel_SOURCES = ltlrel.cc
lunabbrev_SOURCES = equalsf.cc
lunabbrev_CPPFLAGS = $(AM_CPPFLAGS) -DUNABBREV='"^ie"'
nenoform_SOURCES = equalsf.cc
nenoform_CPPFLAGS = $(AM_CPPFLAGS) -DNENOFORM
nequals_SOURCES = equalsf.cc
nequals_CPPFLAGS = $(AM_CPPFLAGS) -DNEGATE
reduc_SOURCES = reduc.cc
reduccmp_SOURCES = equalsf.cc
reduccmp_CPPFLAGS = $(AM_CPPFLAGS) -DREDUC
reduceu_SOURCES = equalsf.cc
reduceu_CPPFLAGS = $(AM_CPPFLAGS) -DREDUC -DEVENT_UNIV
reductaustr_SOURCES = equalsf.cc
reductaustr_CPPFLAGS = $(AM_CPPFLAGS) -DREDUC_TAUSTR
syntimpl_SOURCES = syntimpl.cc
tostring_SOURCES = tostring.cc
tunabbrev_SOURCES = equalsf.cc
tunabbrev_CPPFLAGS = $(AM_CPPFLAGS) -DUNABBREV='"^ieFG"'
tunenoform_SOURCES = equalsf.cc
tunenoform_CPPFLAGS = $(AM_CPPFLAGS) -DNENOFORM -DUNABBREV='"^ieFG"'


# Keep this sorted by STRENGTH.  Test basic things first,
# because such failures will be easier to diagnose and fix.
TESTS =  $(TESTS_ltl) $(TESTS_graph) $(TESTS_kripke) $(TESTS_twa)

TESTS_ltl = \
  bare.test \
  parse.test \
  parseerr.test \
  utf8.test \
  length.test \
  equals.test \
  tostring.test \
  lunabbrev.test \
  tunabbrev.test \
  nenoform.test \
  tunenoform.test \
  unabbrevwm.test \
  consterm.test \
  kind.test \
  remove_x.test \
  ltlrel.test \
  ltlgrind.test \
  ltlcrossgrind.test \
  ltlfilt.test \
  exclusive-ltl.test \
  latex.test \
  lbt.test \
  lenient.test \
  rand.test \
  isop.test \
  syntimpl.test \
  reduc.test \
  reduc0.test \
  reducpsl.test \
  reduccmp.test \
  uwrm.test \
  eventuniv.test \
  stutter-ltl.test

TESTS_graph = \
  graph.test \
  ngraph.test \
  tgbagraph.test

TESTS_kripke = \
  kripke.test \
  bad_parsing.test

TESTS_twa = \
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
  parseaut.test \
  optba.test \
  complete.test \
  remfin.test \
  dstar.test \
  readsave.test \
  ltldo.test \
  ltldo2.test \
  maskacc.test \
  maskkeep.test \
  prodor.test \
  simdet.test \
  sim2.test \
  sim3.test \
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
  exclusive-tgba.test \
  remprop.test \
  degendet.test \
  degenid.test \
  degenlskip.test \
  randomize.test \
  lbttparse.test \
  scc.test \
  sccdot.test \
  sccsimpl.test \
  sepsets.test \
  dbacomp.test \
  obligation.test \
  wdba.test \
  wdba2.test \
  babiak.test \
  monitor.test \
  dra2dba.test \
  unambig.test \
  ltlcross4.test \
  ltl3dra.test \
  ltl2dstar.test \
  ltl2dstar2.test \
  ltl2dstar3.test \
  ltl2dstar4.test \
  ltl2ta.test \
  ltl2ta2.test \
  randaut.test \
  randtgba.test \
  isomorph.test \
  uniq.test \
  sbacc.test \
  stutter-tgba.test \
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
