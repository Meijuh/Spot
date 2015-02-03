// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement
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

#include <vector>
#include <map>
#include <utility>
#include "sbacc.hh"

namespace spot
{
  tgba_digraph_ptr sbacc(tgba_digraph_ptr& old)
  {
    if (old->has_state_based_acc())
      return old;

    auto res = make_tgba_digraph(old->get_dict());
    res->copy_ap_of(old);
    res->copy_acceptance_conditions_of(old);

    typedef std::pair<unsigned, acc_cond::mark_t> pair_t;
    std::map<pair_t, unsigned> s2n;

    std::vector<std::pair<pair_t, unsigned>> todo;

    auto new_state =
      [&](unsigned state, acc_cond::mark_t m) -> unsigned
      {
	pair_t x(state, m);
	auto p = s2n.emplace(x, 0);
	if (p.second)		// This is a new state
	  {
	    unsigned s = res->new_state();
	    p.first->second = s;
	    todo.emplace_back(x, s);
	  }
	return p.first->second;
      };

    // Find any transition going into the initial state, and use its
    // acceptance as mark.
    acc_cond::mark_t init_acc = 0U;
    unsigned old_init = old->get_init_state_number();
    for (auto& t: old->transitions())
      if (t.dst == old_init)
	{
	  init_acc = t.acc;
	  break;
	}

    res->set_init_state(new_state(old_init, init_acc));
    while (!todo.empty())
      {
	auto one = todo.back();
	todo.pop_back();
	for (auto& t: old->out(one.first.first))
	  res->new_transition(one.second,
			      new_state(t.dst, t.acc),
			      t.cond,
			      one.first.second);
      }
    return res;
  }
}
