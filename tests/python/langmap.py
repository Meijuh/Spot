# -*- coding: utf-8 -*-
# Copyright (C) 2016 Laboratoire de Recherche et Développement de l'Epita.
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
# along with this program.  If not, see <http:#www.gnu.org/licenses/>.

import spot
import re
import sys


def test_langmap_functions_for(aut, expected):
    # First, let's get aut's languages map as v.
    v = ''
    try:
        v = spot.language_map(aut)
    except Exception as e:
        # If aut is not deterministic and the exception is as expected then
        # it is ok.
        if 'language_map only works with deterministic automata' in str(e)\
                and not spot.is_deterministic(aut):
                    return
        else:
            print(e, file=sys.stderr)
            exit(1)

    # Now let's check highligthed states.
    spot.highlight_languages(aut, v)
    lines = aut.to_str('hoa', '1.1').split('\n')
    colors_l = []
    for line in lines:
        if 'spot.highlight.states' in line:
            l = [int(w) for w in \
                    re.search(': (.+?)$', line).group(1).split(' ')]
            if l[1::2] != expected:
                print('expected:' + repr(expected) +
                      ' but got:' + repr(l[1::2]), file=sys.stderr)
                exit(1)

aut_l = []
expected_l = []

aut_l.append(spot.translate('(a U b) & GFc & GFd', 'BA', 'deterministic'))
expected_l.append([0, 1, 1, 1])

aut_l.append(spot.translate('GF(a <-> b) | c', 'BA', 'deterministic'))
expected_l.append([0, 1, 2, 2])

aut_l.append(spot.translate('GF(a <-> b) | c | X!a', 'BA', 'deterministic'))
expected_l.append([0, 1, 2, 3, 3])

aut = spot.automaton("""
HOA: v1
States: 4
properties: implicit-labels trans-labels no-univ-branch deterministic complete
acc-name: Rabin 2
Acceptance: 4 (Fin(0)&Inf(1))|(Fin(2)&Inf(3))
Start: 0
AP: 2 "p0" "p1"
--BODY--
State: 0 {0}
1
0
3
2
State: 1 {1}
1
0
3
2
State: 2 {0 3}
1
0
3
2
State: 3 {1 3}
1
0
3
2
--END--
""")
aut_l.append(aut)
expected_l.append([0, 0, 0, 0])

# Add a non deterministic test:
aut_l.append(spot.translate('GF(a <-> XXb) | Xc', 'BA'))
expected_l.append([])

len_aut = len(aut_l)
for i in range(0, len_aut):
    test_langmap_functions_for(aut_l[i], expected_l[i])
