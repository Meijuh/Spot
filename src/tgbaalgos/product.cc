// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include "product.hh"
#include "tgba/tgbagraph.hh"
#include <deque>
#include <unordered_map>
#include "misc/hash.hh"

namespace spot
{
  namespace
  {
    typedef std::pair<unsigned, unsigned> product_state;

    struct product_state_hash
    {
      size_t
      operator()(product_state s) const
      {
        return wang32_hash(s.first ^ wang32_hash(s.second));
      }
    };
  }


  tgba_digraph_ptr product(const const_tgba_digraph_ptr& left,
			   const const_tgba_digraph_ptr& right,
			   unsigned left_state,
			   unsigned right_state)
  {
    std::unordered_map<product_state, unsigned, product_state_hash> s2n;
    std::deque<std::pair<product_state, unsigned>> todo;

    assert(left->get_dict() == right->get_dict());
    auto res = make_tgba_digraph(left->get_dict());
    res->copy_ap_of(left);
    res->copy_ap_of(right);
    res->set_acceptance_conditions(left->acc().num_sets()
				   + right->acc().num_sets());

    auto v = new product_states;
    res->set_named_prop("product-states", v, [](void* vv) {
	delete static_cast<product_states*>(vv);
      });

    auto new_state =
      [&](unsigned left_state, unsigned right_state) -> unsigned
      {
	product_state x(left_state, right_state);
	auto p = s2n.emplace(x, 0);
	if (p.second)		// This is a new state
	  {
	    p.first->second = res->new_state();
	    todo.emplace_back(x, p.first->second);
	    assert(p.first->second == v->size());
	    v->push_back(x);
	  }
	return p.first->second;
      };

    new_state(left_state, right_state);
    while (!todo.empty())
      {
	auto top = todo.front();
	todo.pop_front();
	for (auto& l: left->out(top.first.first))
	  for (auto& r: right->out(top.first.second))
	    {
	      auto cond = l.cond & r.cond;
	      if (cond == bddfalse)
		continue;
	      auto dst = new_state(l.dst, r.dst);
	      res->new_transition(top.second, dst, cond,
				  res->acc().join(left->acc(), l.acc,
						  right->acc(), r.acc));
	      // If right is deterministic, we can abort immediately!
	    }
      }

    return res;
  }

  tgba_digraph_ptr product(const const_tgba_digraph_ptr& left,
			   const const_tgba_digraph_ptr& right)
  {
    return product(left, right,
		   left->get_init_state_number(),
		   right->get_init_state_number());
  }

}
