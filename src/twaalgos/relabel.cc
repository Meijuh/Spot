// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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

#include "relabel.hh"

namespace spot
{
  void
  relabel_here(twa_graph_ptr& aut, ltl::relabeling_map* relmap)
  {
    bddPair* pairs = bdd_newpair();
    auto d = aut->get_dict();
    std::vector<int> vars;
    vars.reserve(relmap->size());
    for (auto& p: *relmap)
      {
	int oldv = aut->register_ap(p.first);
	int newv = aut->register_ap(p.second);
	bdd_setpair(pairs, oldv, newv);
	vars.push_back(oldv);
      }
    for (auto& t: aut->edges())
      t.cond = bdd_replace(t.cond, pairs);
    for (auto v: vars)
      d->unregister_variable(v, aut);
  }
}
