// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement de
// l'Epita.
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

#include "tgbagraph.hh"
#include "ltlast/constant.hh"

namespace spot
{

  void tgba_digraph::merge_transitions()
  {
    // Map a pair (dest state, acc) to the first transition seen
    // with such characteristic.
    typedef std::pair<graph_t::state, acc_cond::mark_t> key_t;
    std::unordered_map<key_t, graph_t::transition, pair_hash> trmap;
    for (auto& s: g_.states())
      {
	// Get a clear map for each state.
	trmap.clear();

	auto t = g_.out_iteraser(s);
	while (t)
	  {
	    // Simply skip false transitions.
	    if (t->cond == bddfalse)
	      {
		t.erase();
		continue;
	      }

	    key_t k(t->dst, t->acc);
	    auto p = trmap.emplace(k, t.trans());
	    if (!p.second)
	      {
		// A previous transitions exists for k.  Merge the
		// condition, and schedule the transition for removal.
		g_.trans_data(p.first->second).cond |= t->cond;
		t.erase();
	      }
	    else
	      {
		++t;
	      }
	  }
      }
    g_.defrag();
  }

  void tgba_digraph::purge_unreachable_states()
  {
    unsigned num_states = g_.num_states();
    if (SPOT_UNLIKELY(num_states == 0))
      return;
    // The TODO vector serves two purposes:
    // - it is a stack of state to process,
    // - it is a set of processed states.
    // The lower 31 bits of each entry is a state on the stack. (The
    // next usable entry on the stack is indicated by todo_pos.)  The
    // 32th bit (i.e., the sign bit) of todo[x] indicates whether
    // states number x has been seen.
    std::vector<unsigned> todo(num_states, 0);
    const unsigned seen = 1 << (sizeof(unsigned)*8-1);
    const unsigned mask = seen - 1;
    todo[0] = init_number_;
    todo[init_number_] |= seen;
    unsigned todo_pos = 1;
    do
      {
	unsigned cur = todo[--todo_pos] & mask;
	todo[todo_pos] ^= cur;	// Zero the state
	for (auto& t: g_.out(cur))
	  if (!(todo[t.dst] & seen))
	    {
	      todo[t.dst] |= seen;
	      todo[todo_pos++] |= t.dst;
	    }
      }
    while (todo_pos > 0);
    // Now renumber each used state.
    unsigned current = 0;
    for (auto& v: todo)
      if (!(v & seen))
	v = -1U;
      else
	v = current++;
    if (current == todo.size())
      return;			// No unreachable state.
    init_number_ = todo[init_number_];
    g_.defrag_states(std::move(todo), current);
  }

  void tgba_digraph::purge_dead_states()
  {
    unsigned num_states = g_.num_states();
    if (num_states == 0)
      return;
    std::vector<unsigned> info(num_states, 0);
    // In this loop, info[s] means that the state is useless.
    bool untouched;
    do
      {
	untouched = true;
	for (unsigned s = 0; s < num_states; ++s)
	  {
	    if (info[s])
	      continue;
	    bool useless = true;
	    auto t = g_.out_iteraser(s);
	    while (t)
	      {
		// Erase any transition to a unused state.
		if (info[t->dst])
		  {
		    t.erase();
		    continue;
		  }
		// if we have a transition, to a used state,
		// then the state is useful.
		useless = false;
		++t;
	      }
	    if (useless)
	      {
		info[s] = true;
		untouched = false;
	      }
	  }
      }
    while (!untouched);

    // Assume that the initial state is useful.
    info[init_number_] = false;
    // Now renumber each used state.
    unsigned current = 0;
    for (auto& v: info)
      if (v)
	v = -1U;
      else
	v = current++;
    if (current == info.size())
      return;			// No useless state.
    init_number_ = info[init_number_];
    g_.defrag_states(std::move(info), current);
  }
}
