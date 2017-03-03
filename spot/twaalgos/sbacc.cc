// -*- coding: utf-8 -*-
// Copyright (C) 2015-2017 Laboratoire de Recherche et Développement
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

#include <vector>
#include <map>
#include <utility>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  twa_graph_ptr sbacc(twa_graph_ptr old)
  {
    if (old->prop_state_acc())
      return old;
    if (!old->is_existential())
      throw std::runtime_error
        ("sbacc() does not support alternation");

    scc_info si(old);

    unsigned ns = old->num_states();
    acc_cond::mark_t all = old->acc().all_sets();
    // Marks that are common to all ingoing or outgoing transitions.
    std::vector<acc_cond::mark_t> common_in(ns, all);
    std::vector<acc_cond::mark_t> common_out(ns, all);
    // Marks that label one incoming transition from the same SCC.
    std::vector<acc_cond::mark_t> one_in(ns, 0U);
    for (auto& e: old->edges())
      if (si.scc_of(e.src) == si.scc_of(e.dst))
        {
          common_in[e.dst] &= e.acc;
          common_out[e.src] &= e.acc;
        }
    for (unsigned s = 0; s < ns; ++s)
      common_out[s] |= common_in[s];
    for (auto& e: old->edges())
      if (si.scc_of(e.src) == si.scc_of(e.dst))
        one_in[e.dst] = e.acc - common_out[e.src];

    auto res = make_twa_graph(old->get_dict());
    res->copy_ap_of(old);
    res->copy_acceptance_of(old);
    res->prop_copy(old, {false, true, true, true, true});
    res->prop_state_acc(true);

    typedef std::pair<unsigned, acc_cond::mark_t> pair_t;
    std::map<pair_t, unsigned> s2n;

    std::vector<std::pair<pair_t, unsigned>> todo;

    auto new_state =
      [&](unsigned state, acc_cond::mark_t m) -> unsigned
      {
        pair_t x(state, m);
        auto p = s2n.emplace(x, 0);
        if (p.second)                // This is a new state
          {
            unsigned s = res->new_state();
            p.first->second = s;
            todo.emplace_back(x, s);
          }
        return p.first->second;
      };

    unsigned old_init = old->get_init_state_number();
    acc_cond::mark_t init_acc = 0U;
    if (!si.is_rejecting_scc(si.scc_of(old_init)))
      // Use any edge going into the initial state to set the first
      // acceptance mark.
      init_acc = one_in[old_init] | common_out[old_init];

    res->set_init_state(new_state(old_init, init_acc));
    while (!todo.empty())
      {
        auto one = todo.back();
        todo.pop_back();
        unsigned scc_src = si.scc_of(one.first.first);
        bool maybe_accepting = !si.is_rejecting_scc(scc_src);
        for (auto& t: old->out(one.first.first))
          {
            unsigned scc_dst = si.scc_of(t.dst);
            acc_cond::mark_t acc = 0U;
            bool dst_acc = si.is_accepting_scc(scc_dst);
            if (maybe_accepting && scc_src == scc_dst)
              acc = t.acc - common_out[t.src];
            else if (dst_acc)
              // We enter a new accepting SCC. Use any edge going into
              // t.dst from this SCC to set the initial acceptance mark.
              acc = one_in[t.dst];
            if (dst_acc)
              acc |= common_out[t.dst];
            res->new_edge(one.second, new_state(t.dst, acc),
                          t.cond, one.first.second);
          }
      }
    res->merge_edges();
    return res;
  }
}
