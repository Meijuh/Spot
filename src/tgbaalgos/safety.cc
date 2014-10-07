// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2011, 2013, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE)
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

#include "safety.hh"
#include "misc/hash.hh"
#include <deque>

namespace spot
{
  bool
  is_guarantee_automaton(const const_tgba_digraph_ptr& aut,
			 const scc_info* sm)
  {
    // Create an scc_info if the user did not give one to us.
    bool need_sm = !sm;
    if (need_sm)
      sm = new scc_info(aut);

    bool result = true;

    unsigned scc_count = sm->scc_count();
    for (unsigned scc = 0; scc < scc_count; ++scc)
      {
	if (!sm->is_accepting_scc(scc))
	  continue;
	// Accepting SCCs should have only one state.
	auto& st = sm->states_of(scc);
	if (st.size() != 1)
	  {
	    result = false;
	    break;
	  }
	// The state should have only one transition that is a
	// self-loop labelled by true.
	auto src = st.front();
	auto out = aut->out(src);
	auto it = out.begin();
	assert(it != out.end());
	result =
	  (it->cond == bddtrue) && (it->dst == src) && (++it == out.end());
	if (!result)
	  break;
      }

    if (need_sm)
      delete sm;
    return result;
  }

  bool is_safety_mwdba(const const_tgba_digraph_ptr& aut)
  {
    for (auto& t: aut->transitions())
      if (!aut->is_dead_transition(t))
	if (!aut->acc().accepting(t.acc))
	  return false;
    return true;
  }



}
