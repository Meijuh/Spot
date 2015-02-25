// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et Développement de
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
    g_.remove_dead_transitions_();

    typedef graph_t::trans_storage_t tr_t;
    g_.sort_transitions_([](const tr_t& lhs, const tr_t& rhs)
			 {
			   if (lhs.src < rhs.src)
			     return true;
			   if (lhs.src > rhs.src)
			     return false;
			   if (lhs.dst < rhs.dst)
			     return true;
			   if (lhs.dst > rhs.dst)
			     return false;
			   return lhs.acc < rhs.acc;
			   // Do not sort on conditions, we'll merge
			   // them.
			 });

    auto& trans = this->transition_vector();
    unsigned tend = trans.size();
    unsigned out = 0;
    unsigned in = 1;
    // Skip any leading false transition.
    while (in < tend && trans[in].cond == bddfalse)
      ++in;
    if (in < tend)
      {
	++out;
	if (out != in)
	  trans[out] = trans[in];
	for (++in; in < tend; ++in)
	  {
	    if (trans[in].cond == bddfalse) // Unusable transition
	      continue;
	    // Merge transitions with the same source, destination, and
	    // acceptance.  (We test the source last, because this is the
	    // most likely test to be true as transitions are ordered by
	    // sources and then destinations.)
	    if (trans[out].dst == trans[in].dst
		&& trans[out].acc == trans[in].acc
		&& trans[out].src == trans[in].src)
	      {
		trans[out].cond |= trans[in].cond;
	      }
	    else
	      {
		++out;
		if (in != out)
		  trans[out] = trans[in];
	      }
	  }
      }
    if (++out != tend)
      trans.resize(out);

    tend = out;
    out = in = 2;

    // FIXME: We could should also merge transitions when using
    // fin_acceptance, but the rule for Fin sets are different than
    // those for Inf sets, (and we need to be careful if a set is used
    // both as Inf and Fin)
    if ((in < tend) && !acc().uses_fin_acceptance())
      {
	typedef graph_t::trans_storage_t tr_t;
	g_.sort_transitions_([](const tr_t& lhs, const tr_t& rhs)
			     {
			       if (lhs.src < rhs.src)
				 return true;
			       if (lhs.src > rhs.src)
				 return false;
			       if (lhs.dst < rhs.dst)
				 return true;
			       if (lhs.dst > rhs.dst)
				 return false;
			       return lhs.cond.id() < rhs.cond.id();
			       // Do not sort on acceptance, we'll merge
			       // them.
			     });

	for (; in < tend; ++in)
	  {
	    // Merge transitions with the same source, destination,
	    // and conditions.  (We test the source last, for the
	    // same reason as above.)
	    if (trans[out].dst == trans[in].dst
		&& trans[out].cond.id() == trans[in].cond.id()
		&& trans[out].src == trans[in].src)
	      {
		trans[out].acc |= trans[in].acc;
	      }
	    else
	      {
		++out;
		if (in != out)
		  trans[out] = trans[in];
	      }
	  }
	if (++out != tend)
	  trans.resize(out);
      }

    g_.chain_transitions_();
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
