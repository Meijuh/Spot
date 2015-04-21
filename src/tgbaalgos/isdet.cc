// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014, 2015 Laboratoire de Recherche et
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

#include "tgbaalgos/isdet.hh"
#include <set>
#include <deque>

namespace spot
{
  namespace
  {
    template<bool count>
    static
    unsigned
    count_nondet_states_aux(const const_twa_graph_ptr& aut)
    {
      unsigned nondet_states = 0;
      unsigned ns = aut->num_states();
      for (unsigned src = 0; src < ns; ++src)
	{
	  bdd available = bddtrue;
	  for (auto& t: aut->out(src))
	    if (!bdd_implies(t.cond, available))
	      {
		++nondet_states;
		break;
	      }
	    else
	      {
		available -= t.cond;
	      }
	  // If we are not counting non-deterministic states, abort as
	  // soon as possible.
	  if (!count && nondet_states)
	    break;
	}
      return nondet_states;
    }
  }

  unsigned
  count_nondet_states(const const_twa_graph_ptr& aut)
  {
    return count_nondet_states_aux<true>(aut);
  }

  bool
  is_deterministic(const const_twa_graph_ptr& aut)
  {
    if (aut->is_deterministic())
      return true;
    return !count_nondet_states_aux<false>(aut);
  }

  bool
  is_complete(const const_twa_graph_ptr& aut)
  {
    unsigned ns = aut->num_states();
    for (unsigned src = 0; src < ns; ++src)
      {
	bdd available = bddtrue;
	for (auto& t: aut->out(src))
	  available -= t.cond;
	if (available != bddfalse)
	  return false;
      }
    // The empty automaton is not complete since it does not have an
    // initial state.
    return ns > 0;
  }
}
