// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et
// Développement de l'Epita.
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

#include "complete.hh"

namespace spot
{
  unsigned tgba_complete_here(twa_graph_ptr aut)
  {
    unsigned n = aut->num_states();
    unsigned sink = -1U;

    // UM is a pair (bool, mark).  If the Boolean is false, the
    // acceptance is always satisfiable.  Otherwise, MARK is an
    // example of unsatisfiable mark.
    auto um = aut->get_acceptance().unsat_mark();
    if (!um.first)
      {
	// We cannot safely complete an automaton if its
	// acceptance is always satisfiable.
	auto acc = aut->set_buchi();
	for (auto& t: aut->transition_vector())
	  t.acc = acc;
      }
    else
      {
	// Loop over the states and seek a state that has only self
	// loops, and that is not accepting.  This will be our sink
	// state.  Note that we do not even have to ensure that the
	// state is complete as we will complete the whole automaton
	// in a second pass.
	for (unsigned i = 0; i < n; ++i)
	  {
	    bool selfloop = true;
	    acc_cond::mark_t accsum = 0U;
	    for (auto& t: aut->out(i))
	      {
		if (t.dst != i)	// Not a self-loop
		  {
		    selfloop = false;
		    break;
		  }
		accsum |= t.acc;
	      }
	    if (selfloop && !aut->acc().accepting(accsum))
	      {
		// We have found a sink!
		sink = i;
		break;
	      }
	  }
      }

    unsigned t = aut->num_transitions();

    // Now complete all states (excluding any newly added the sink).
    for (unsigned i = 0; i < n; ++i)
      {
	bdd missingcond = bddtrue;
	acc_cond::mark_t acc = 0U;
	for (auto& t: aut->out(i))
	  {
	    missingcond -= t.cond;
	    // FIXME: This is ugly.
	    //
	    // In case the automaton uses state-based acceptance, we
	    // need to put the new transition in the same set as all
	    // the other.
	    //
	    // In case the automaton uses transition-based acceptance,
	    // it does not matter what acceptance set we put the new
	    // transition into.
	    //
	    // So in both cases, we put the transition in the same
	    // acceptance sets as the last outgoing transition of the
	    // state.
	    acc = t.acc;
	  }
	// If the state has incomplete successors, we need to add a
	// transition to some sink state.
	if (missingcond != bddfalse)
	  {
	    // If we haven't found any sink, simply add one.
	    if (sink == -1U)
	      {
		sink = aut->new_state();
		aut->new_transition(sink, sink, bddtrue, um.second);
	      }
	    // In case the automaton use state-based acceptance, propagate
	    // the acceptance of the first transition to the one we add.
	    aut->new_transition(i, sink, missingcond, acc);
	  }
      }

    // Get rid of any named property if the automaton changed.
    if (t < aut->num_transitions())
      aut->release_named_properties();
    else
      assert(t == aut->num_transitions());

    return sink;
  }

  twa_graph_ptr tgba_complete(const const_tgba_ptr& aut)
  {
    auto res = make_twa_graph(aut, {
					true, // state based
					true, // inherently_weak
					true, // deterministic
					true, // stutter inv.
				      });
    tgba_complete_here(res);
    return res;
  }

}
