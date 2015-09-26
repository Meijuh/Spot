// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et
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
#include "twa/twagraph.hh"
#include "twaalgos/complete.hh"
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

    static
    twa_graph_ptr product_aux(const const_twa_graph_ptr& left,
			      const const_twa_graph_ptr& right,
			      unsigned left_state,
			      unsigned right_state,
			      bool and_acc)
    {
      std::unordered_map<product_state, unsigned, product_state_hash> s2n;
      std::deque<std::pair<product_state, unsigned>> todo;

      assert(left->get_dict() == right->get_dict());
      auto res = make_twa_graph(left->get_dict());
      res->copy_ap_of(left);
      res->copy_ap_of(right);
      auto left_num = left->num_sets();
      auto right_acc = right->get_acceptance();
      right_acc.shift_left(left_num);
      if (and_acc)
	right_acc.append_and(left->get_acceptance());
      else
	right_acc.append_or(acc_cond::acc_code(left->get_acceptance()));
      res->set_acceptance(left_num + right->num_sets(), right_acc);

      auto v = new product_states;
      res->set_named_prop("product-states", v);

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

      res->set_init_state(new_state(left_state, right_state));
      if (right_acc.is_false())
	// Do not bother doing any work if the resulting acceptance is
	// false.
	return res;
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
		res->new_edge(top.second, dst, cond,
			      res->acc().join(left->acc(), l.acc,
					      right->acc(), r.acc));
		// If right is deterministic, we can abort immediately!
	      }
	}

      res->prop_deterministic(left->is_deterministic()
			      && right->is_deterministic());
      res->prop_stutter_invariant(left->is_stutter_invariant()
				  && right->is_stutter_invariant());
      res->prop_stutter_sensitive(left->is_stutter_sensitive()
				  && right->is_stutter_sensitive());
      res->prop_state_based_acc(left->has_state_based_acc()
				&& right->has_state_based_acc());
      return res;
    }
  }

  twa_graph_ptr product(const const_twa_graph_ptr& left,
			const const_twa_graph_ptr& right,
			unsigned left_state,
			unsigned right_state)
  {
    return product_aux(left, right, left_state, right_state, true);
  }

  twa_graph_ptr product(const const_twa_graph_ptr& left,
			const const_twa_graph_ptr& right)
  {
    return product(left, right,
		   left->get_init_state_number(),
		   right->get_init_state_number());
  }

  twa_graph_ptr product_or(const const_twa_graph_ptr& left,
			   const const_twa_graph_ptr& right,
			   unsigned left_state,
			   unsigned right_state)
  {
    return product_aux(tgba_complete(left),
		       tgba_complete(right),
		       left_state, right_state, false);
  }

  twa_graph_ptr product_or(const const_twa_graph_ptr& left,
			   const const_twa_graph_ptr& right)
  {
    return product_or(left, right,
		      left->get_init_state_number(),
		      right->get_init_state_number());
  }

}
