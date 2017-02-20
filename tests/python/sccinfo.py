#!/usr/bin/python3
# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2017 Laboratoire de Recherche et Développement de
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

a = spot.translate('(Ga -> Gb) W c')

si = spot.scc_info(a)
n = si.scc_count()
assert n == 4

acc = 0
rej = 0
triv = 0
for i in range(n):
    acc += si.is_accepting_scc(i)
    rej += si.is_rejecting_scc(i)
    triv += si.is_trivial(i)
assert acc == 3
assert rej == 1
assert triv == 0

for scc in si:
    acc -= scc.is_accepting()
    rej -= scc.is_rejecting()
    triv -= scc.is_trivial()
assert acc == 0
assert rej == 0
assert triv == 0

l0 = si.states_of(0)
l1 = si.states_of(1)
l2 = si.states_of(2)
l3 = si.states_of(3)
l = sorted(list(l0) + list(l1) + list(l2) + list(l3))
assert l == [0, 1, 2, 3, 4]

i = si.initial()
todo = {i}
seen = {i}
while todo:
    e = todo.pop()
    for s in si.succ(e):
        if s not in seen:
            seen.add(s)
            todo.add(s)
assert seen == {0, 1, 2, 3}

assert not spot.is_weak_automaton(a, si)
