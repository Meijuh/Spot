// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2015 Laboratoire de Recherche et Developpement
// de l'Epita (LRDE).
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

#include "isunamb.hh"
#include "twaalgos/product.hh"
#include "sccfilter.hh"
#include "stats.hh"
#include <set>
#include <list>

namespace spot
{
  bool is_unambiguous(const const_twa_graph_ptr& aut)
  {
    if (aut->is_deterministic() || aut->is_unambiguous())
      return true;
    auto clean_a = scc_filter_states(aut);
    auto prod = product(clean_a, clean_a);
    auto clean_p = scc_filter_states(prod);
    tgba_statistics sa = stats_reachable(clean_a);
    tgba_statistics sp = stats_reachable(clean_p);
    return sa.states == sp.states && sa.transitions == sp.transitions;
  }

  bool check_unambiguous(const twa_graph_ptr& aut)
  {
    aut->prop_unambiguous(is_unambiguous(aut));
    return aut->is_unambiguous();
  }
}
