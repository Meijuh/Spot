// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2010, 2012, 2013, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#ifndef SPOT_LTLVISIT_MUTATION_HH
# define SPOT_LTLVISIT_MUTATION_HH

#include "ltlast/formula.hh"
#include <limits>
#include <set>
#include <vector>

#define MUT_AP2CONST 0x1
#define MUT_SIMPLIFY_BOUNDS 0x2
#define MUT_REMOVE_MULTOP_OPERANDS 0x4
#define MUT_REMOVE_OPS 0x8
#define MUT_SPLIT_OPS 0x10
#define MUT_REWRITE_OPS 0x20
#define MUT_REMOVE_ONE_AP 0x40

namespace spot
{
  namespace ltl
  {
    typedef std::vector<const formula*> vec;
    SPOT_API
    vec get_mutations(const formula*,
		      unsigned opts = 0xfff,
		      bool sort = true,
		      int n = std::numeric_limits<int>::max(),
		      unsigned m = 1);
  }
}
#endif
