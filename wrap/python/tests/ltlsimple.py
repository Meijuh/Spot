# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2009, 2010, 2012, 2015 Laboratoire de Recherche et Développement
# de l'Epita (LRDE).
# Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
# département Systemes Répartis Coopératifs (SRC), Université Pierre
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

import spot
import sys

#----------------------------------------------------------------------
a = spot.formula.ap('a')
b = spot.formula.ap('b')
c = spot.formula.ap('c')
c2 = spot.formula.ap('c')

assert c == c2

op  = spot.formula.And([a, b])
op2 = spot.formula.And([op, c])
op3 = spot.formula.And([a, c, b])

assert op2 == op3

# The symbol for a subformula which hasn't been cloned is better
# suppressed, so we don't attempt to reuse it elsewhere.
del op, c

sys.stdout.write('op2 = %s\n' % str(op2))

del a, b, c2

sys.stdout.write('op3 = %s\n' % str(op3))
assert op2 == op3

op4 = spot.formula.Or([op2, op3])

sys.stdout.write('op4 = %s\n' % str(op4))
assert op4 == op2

del op2, op3, op4

#----------------------------------------------------------------------
a = spot.formula.ap('a')
b = spot.formula.ap('b')
c = spot.formula.ap('c')
T = spot.formula.tt()
F = spot.formula.ff()

f1 = spot.formula.Equiv(c, a)
f2 = spot.formula.Implies(a, b)
f3 = spot.formula.Xor(b, c)
f4 = spot.formula.Not(f3); del f3
f5 = spot.formula.Xor(F, c)

del a, b, c, T, F, f1, f2, f4, f5

assert spot.fnode_instances_check()

#----------------------------------------------------------------------
assert str([x for x in spot.formula('a &b & c')]) == '[a, b, c]'


def switch_g_f(x):
    if x._is(spot.op_G):
        return spot.formula.F(switch_g_f(x[0]))
    if x._is(spot.op_F):
        return spot.formula.G(switch_g_f(x[0]))
    return x.map(switch_g_f)

f = spot.formula('GFa & XFGb & Fc & G(a | b | Fd)')
assert str(switch_g_f(f)) == 'FGa & XGFb & Gc & F(a | b | Gd)'

x = 0
def count_g(f):
    global x
    if f._is(spot.op_G):
        x += 1
f.traverse(count_g)
assert x == 3
