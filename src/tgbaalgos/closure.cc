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
#include <algorithm>

namespace spot
{
  tgba_digraph_ptr
  closure(tgba_digraph_ptr&& a)
  {
    unsigned n = a->num_states();
    std::vector<unsigned> todo;
    std::vector<std::vector<unsigned> > dst2trans(n);

    for (unsigned state = 0; state < n; ++state)
      {
	auto trans = a->out(state);

	for (auto it = trans.begin(); it != trans.end(); ++it)
	  {
	    todo.push_back(it.trans());
	    dst2trans[it->dst].push_back(it.trans());
	  }

	while (!todo.empty())
	  {
	    auto t1 = a->trans_storage(todo.back());
	    todo.pop_back();

	    for (auto& t2 : a->out(t1.dst))
	      {
		bdd cond = t1.cond & t2.cond;
		if (cond != bddfalse)
		  {
                    bool need_new_trans = true;
		    acc_cond::mark_t acc = t1.acc | t2.acc;
                    for (auto& t: dst2trans[t2.dst])
                      {
                        auto& ts = a->trans_storage(t);
                        if (acc == ts.acc)
                          {
                            if (!bdd_implies(cond, ts.cond))
                              {
                                ts.cond = ts.cond | cond;
                                if (std::find(todo.begin(), todo.end(), t)
                                    == todo.end())
                                  todo.push_back(t);
                              }
                            need_new_trans = false;
                          }
                      }
                    if (need_new_trans)
                      {
			// Load t2.dst first, because t2 can be
			// invalidated by new_transition().
			auto dst = t2.dst;
                        auto i = a->new_transition(state, dst, cond, acc);
                        dst2trans[dst].push_back(i);
                        todo.push_back(i);
                      }
		  }
	      }
	  }
        for (auto& it: dst2trans)
          it.clear();
      }
    return a;
  }

  tgba_digraph_ptr
  closure(const const_tgba_digraph_ptr& a)
  {
    return closure(make_tgba_digraph(a));
  }
}
