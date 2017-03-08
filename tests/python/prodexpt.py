# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2016-2017 Laboratoire de Recherche et Développement de l'Epita
# (LRDE).
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

# make sure that we are not allowed to build the product of two automata with
# different dictionaries.

aut1 = spot.translate('Xa')
aut2 = spot.translate('Xb', dict=spot.make_bdd_dict())

try:
    spot.product(aut1, aut2)
    exit(2)
except RuntimeError:
    pass

try:
    spot.otf_product(aut1, aut2)
    exit(2)
except RuntimeError:
    pass
