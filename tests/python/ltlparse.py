# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2009, 2010, 2012, 2014, 2015, 2016 Laboratoire de Recherche et
# Développement de l'Epita (LRDE).
# Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
# département Systèmes Répartis Coopératifs (SRC), Université Pierre
# et Marie Curie.
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

e = spot.default_environment.instance()

l = ['GFa', 'a U (((b)) xor c)', '!(FFx <=> Fx)', 'a \/ a \/ b \/ a \/ a'];

for str1 in l:
    pf = spot.parse_infix_psl(str1, e, False)
    if pf.format_errors(spot.get_cout()):
        sys.exit(1)
    str2 = str(pf.f)
    del pf
    sys.stdout.write(str2 + "\n")
    # Try to reparse the stringified formula
    pf = spot.parse_infix_psl(str2, e)
    if pf.format_errors(spot.get_cout()):
        sys.exit(1)
    sys.stdout.write(str(pf.f) + "\n")
    del pf

assert spot.fnode_instances_check()
