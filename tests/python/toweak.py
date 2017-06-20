# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2017  Laboratoire de Recherche et Développement
# de l'Epita
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

import spot

phi1 = """GFb
X(!b | GF!a)
!a U X(b | GF!b)
GFa
G(a M b)
(!a | b) & GFb
(a U Xa) | G(b & Fa)
GF!b
(b & GF!b) | (!b & FGb)
b | (a & XF(b R a)) | (!a & XG(!b U !a))"""

phi1 = phi1.split('\n')

bdddict = spot.make_bdd_dict()

def equivalent(a, phi):
  negphi = spot.formula.Not(phi)
  nega = spot.dualize(a)
  a2 = spot.translate(phi, 'TGBA', 'SBAcc' )
  nega2 = spot.translate(negphi, 'TGBA', 'SBAcc')
  ra = spot.remove_alternation(a)
  ran = spot.remove_alternation(nega)
  return spot.product(spot.remove_alternation(a), nega2).is_empty()\
         and spot.product(spot.remove_alternation(nega), a2).is_empty()

def test_phi(phi):
  a =  spot.translate(phi, 'TGBA', 'SBAcc')
  a0 = spot.dualize(a)

  res = spot.to_weak_alternating(a0)
  assert equivalent(res, spot.formula.Not(spot.formula(phi)))

for p in phi1:
  test_phi(p)
