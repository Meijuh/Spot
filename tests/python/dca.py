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

import sys
import spot


def gen_streett(formula):
    aut = spot.translate(formula, 'BA')
    aut.set_acceptance(2, 'Fin(0) | Inf(1)')
    for e in aut.edges():
        if (e.acc):
            e.acc = spot.mark_t([0,1])
        else:
            e.acc = spot.mark_t([0])
    return aut


aut = gen_streett(sys.argv[1])
print(aut.to_str('hoa'))
