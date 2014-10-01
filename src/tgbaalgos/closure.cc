// Copyright (C) 2014 Laboratoire de Recherche et Développement
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


#include <unordered_set>
#include <deque>
#include "closure.hh"
#include "dupexp.hh"

namespace spot
{
  namespace
  {
    struct transition
    {
      unsigned dst;
      acc_cond::mark_t acc;
      transition(unsigned dst, acc_cond::mark_t acc) :
	dst(dst), acc(acc)
      {
      }
    };

    struct transition_hash
    {
      size_t
      operator()(const transition& t) const
      {
	return wang32_hash(t.dst) ^ wang32_hash(t.acc);
      }
    };

    struct transition_equal
    {
      bool
      operator()(const transition& left, const transition& right) const
      {
	return left.dst == right.dst
	  && left.acc == right.acc;
      }
    };

    typedef std::unordered_map<transition, unsigned, transition_hash,
			       transition_equal> tmap_t;
    typedef std::set<unsigned> tset_t;
  }

  tgba_digraph_ptr
  closure(const const_tgba_digraph_ptr& a)
  {
    tgba_digraph_ptr res = tgba_dupexp_dfs(a);
    unsigned n = res->num_states();
    tset_t todo;

    for (unsigned state = 0; state < n; ++state)
      {
	tmap_t uniq;
	auto trans = res->out(state);

	for (auto it = trans.begin(); it != trans.end(); ++it)
	  {
	    todo.insert(it.trans());
	    uniq.emplace(transition(it->dst, it->acc), it.trans());
	  }

	while (!todo.empty())
	  {
	    unsigned t1 = *todo.begin();
	    todo.erase(t1);
	    tgba_graph_trans_data td = res->trans_data(t1);
	    unsigned dst = res->trans_storage(t1).dst;

	    for (auto& t2 : res->out(dst))
	      {
		bdd cond = td.cond & t2.cond;
		if (cond != bddfalse)
		  {
		    acc_cond::mark_t acc = td.acc | t2.acc;
		    transition jump(t2.dst, acc);
		    unsigned i;
		    auto u = uniq.find(jump);

		    if (u == uniq.end())
		      {
			i = res->new_transition(state, t2.dst, cond, acc);
			uniq.emplace(jump, i);
			todo.insert(i);
		      }

		    else
		      {
			bdd old_cond = res->trans_data(u->second).cond;
			if (!bdd_implies(cond, old_cond))
			  {
			    res->trans_data(u->second).cond = cond | old_cond;
			    todo.insert(u->second);
			  }
		      }
		  }
	      }
	  }
	uniq.clear();
      }
    return res;
  }
}
