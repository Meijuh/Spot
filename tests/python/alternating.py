#!/usr/bin/python3
# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2016 Laboratoire de Recherche et Développement de
# l'EPITA.
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
import buddy

aut = spot.make_twa_graph(spot._bdd_dict)

p1 = buddy.bdd_ithvar(aut.register_ap("p1"))
p2 = buddy.bdd_ithvar(aut.register_ap("p2"))

m = aut.set_buchi()

aut.new_states(3)

aut.set_init_state(0)
aut.new_univ_edge(0, [1, 2], p1, m)
aut.new_univ_edge(0, [0, 1], p2)
aut.new_univ_edge(1, [0, 2, 1], p1 & p2)
aut.new_edge(2, 2, p1 | p2)

tr = [(s, [[x for x in aut.univ_dests(i)] for i in aut.out(s)])
      for s in range(3)]
print(tr)
assert [(0, [[1, 2], [0, 1]]), (1, [[0, 2, 1]]), (2, [[2]])] == tr
assert aut.is_alternating()

received = False
try:
    for i in aut.out(0):
        for j in aut.out(i.dst):
            pass
except RuntimeError:
    received = True
assert received

h = aut.to_str('hoa')
print(h)
assert h == """HOA: v1
States: 3
Start: 0
AP: 2 "p1" "p2"
acc-name: Buchi
Acceptance: 1 Inf(0)
properties: univ-branch trans-labels explicit-labels trans-acc
--BODY--
State: 0
[0] 1&2 {0}
[1] 0&1
State: 1
[0&1] 0&2&1
State: 2
[0 | 1] 2
--END--"""

aut2 = spot.automaton(h)
h2 = aut2.to_str('hoa')
print(h2)
assert h == h2
