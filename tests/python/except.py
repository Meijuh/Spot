# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2018 Laboratoire de Recherche et Développement de
# l'Epita (LRDE).
#
# This file is part of Spot, a model checking library.
#
# Spot is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# Spot is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.


# Test some function that must return exceptions on error.  Doing
# so is mostly a way to improve the coverage report.


import spot

try:
    spot.iar(spot.translate('GFa & GFb & GFc'))
except RuntimeError as e:
    assert 'iar() expects Rabin-like or Streett-like input' in str(e)

alt = spot.dualize(spot.translate('FGa | FGb'))

try:
    spot.tgba_determinize(alt)
except RuntimeError as e:
    assert 'tgba_determinize() does not support alternation' in str(e)


aut = spot.translate('a U b U c')
aps = aut.ap()
rem = spot.remove_ap()
rem.add_ap('"a"=0,b')
aut = rem.strip(aut)
assert aut.ap() == aps[2:]
try:
    rem.add_ap('"a=0,b')
except ValueError as e:
    assert """missing closing '"'""" in str(e)

try:
    rem.add_ap('a=0=b')
except ValueError as e:
    assert """unexpected '=' at position 3""" in str(e)


si = spot.scc_info(alt)
try:
    si.determine_unknown_acceptance()
except RuntimeError as e:
    assert "scc_info::determine_unknown_acceptance() does not supp" in str(e)
