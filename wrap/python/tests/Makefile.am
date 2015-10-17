## -*- coding: utf-8 -*-
## Copyright (C) 2010, 2012, 2013, 2014, 2015 Labortatoire de
## Recherche et Développement de l'EPITA.
## Copyright (C) 2003, 2004, 2005  Laboratoire d'Informatique de Paris 6 (LIP6),
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

EXTRA_DIST = \
  $(TESTS) \
  ltl2tgba.py \
  ipnbdoctest.py

LOG_COMPILER = ./run
LOG_DRIVER = $(TEST_LOG_DRIVER)
# ensure run is rebuilt before the tests are run.
check_SCRIPTS = run

TESTS = \
  accparse.ipynb \
  accparse2.py \
  alarm.py \
  automata.ipynb \
  automata-io.ipynb \
  bddnqueen.py \
  formulas.ipynb \
  implies.py \
  interdep.py \
  ltl2tgba.test \
  ltlparse.py \
  ltlsimple.py \
  minato.py \
  optionmap.py \
  parsetgba.py \
  piperead.ipynb \
  randaut.ipynb \
  randgen.py \
  randltl.ipynb \
  relabel.py \
  remfin.py \
  setxor.py \
  testingaut.ipynb

SUFFIXES = .ipynb .html
.ipynb.html:
	$(IPYTHON) nbconvert $< --to html

.PHONY: nb-html
nb-html: $(TESTS:.ipynb=.html)
