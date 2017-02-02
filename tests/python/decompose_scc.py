# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2017 Laboratoire de Recherche et
# Développement de l'Epita
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

aut = spot.translate('(Ga -> Gb) W c')

si = spot.scc_info(aut)

assert (spot.decompose_scc(si, 2).to_str('hoa', '1.1') == """HOA: v1.1
States: 3
Start: 0
AP: 3 "b" "a" "c"
acc-name: Buchi
Acceptance: 1 Inf(0)
properties: trans-labels explicit-labels state-acc !complete
properties: deterministic
--BODY--
State: 0
[!1&!2] 0
[1&!2] 1
State: 1
[!1&!2] 0
[1&!2] 1
[1&2] 2
State: 2
[1] 2
--END--""")

try:
    spot.decompose_scc(si, 4)
except ValueError:
    pass
else:
    raise AssertionError
