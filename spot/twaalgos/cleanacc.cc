// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2017 Laboratoire de Recherche et Développement
// de l'Epita.
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

#include <spot/twaalgos/cleanacc.hh>

namespace spot
{
  twa_graph_ptr cleanup_acceptance_here(twa_graph_ptr aut, bool strip)
  {
    auto& acc = aut->acc();
    if (acc.num_sets() == 0)
      return aut;

    auto c = aut->get_acceptance();
    acc_cond::mark_t used_in_cond = c.used_sets();

    acc_cond::mark_t used_in_aut = 0U;
    acc_cond::mark_t used_on_all_edges = used_in_cond;
    for (auto& t: aut->edges())
      {
        used_in_aut |= t.acc;
        used_on_all_edges &= t.acc;
      }

    auto useful = used_in_aut & used_in_cond;
    auto useless = strip ? acc.comp(useful) : (used_in_cond - used_in_aut);

    useless |= used_on_all_edges;

    if (!useless)
      return aut;

    // Remove useless marks from the automaton
    if (strip)
      for (auto& t: aut->edges())
        t.acc = t.acc.strip(useless);

    // if x appears on all edges, then
    //   Fin(x) = false and Inf(x) = true
    if (used_on_all_edges)
      c = c.remove(used_on_all_edges, false);

    // Remove useless marks from the acceptance condition
    if (strip)
      aut->set_acceptance(useful.count(), c.strip(useless, true));
    else
      aut->set_acceptance(aut->num_sets(), c.remove(useless, true));

    // This may in turn cause even more set to be unused, because of
    // some simplifications in the acceptance condition, so do it again.
    return cleanup_acceptance_here(aut, strip);
  }

  twa_graph_ptr cleanup_acceptance(const_twa_graph_ptr aut)
  {
    return cleanup_acceptance_here(make_twa_graph(aut,
                                                     twa::prop_set::all()));
  }


}
