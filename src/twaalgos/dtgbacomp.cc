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

#include "dtgbacomp.hh"
#include "sccinfo.hh"
#include "complete.hh"
#include "cleanacc.hh"

namespace spot
{
  twa_graph_ptr dtgba_complement_nonweak(const const_twa_graph_ptr& aut)
  {
    // Clone the original automaton.
    auto res = make_twa_graph(aut,
				 { false, // state based
				   false, // inherently_weak
				   false, // deterministic
				   true,  // stutter inv.
				  });
    // Copy the old acceptance condition before we replace it.
    acc_cond oldacc = aut->acc(); // Copy it!

    // We will modify res in place, and the resulting
    // automaton will only have one acceptance set.
    // This changes aut->acc();
    res->set_buchi();
    // The resulting automaton is weak.
    res->prop_inherently_weak();
    res->prop_state_based_acc();

    unsigned num_sets = oldacc.num_sets();
    unsigned n = res->num_states();
    // We will duplicate the automaton as many times as we have
    // acceptance sets, and we need one extra sink state.
    res->new_states(num_sets * n + 1);
    unsigned sink = res->num_states() - 1;
    // The sink state has an accepting self-loop.
    res->new_acc_edge(sink, sink, bddtrue);

    for (unsigned src = 0; src < n; ++src)
      {
	// Keep track of all conditions on edge leaving state
	// SRC, so we can complete it.
	bdd missingcond = bddtrue;
	for (auto& t: res->out(src))
	  {
	    if (t.dst >= n)	// Ignore edges we added.
	      break;
	    missingcond -= t.cond;
	    acc_cond::mark_t curacc = t.acc;
	    // The original edge must not accept anymore.
	    t.acc = 0U;

	    // Edge that were fully accepting are never cloned.
	    if (oldacc.accepting(curacc))
	      continue;
	    // Save t.cond and t.dst as the reference to t
	    // is invalided by calls to new_edge().
	    unsigned dst = t.dst;
	    bdd cond = t.cond;

	    // Iterate over all the acceptance conditions in 'curacc',
	    // an duplicate it for each clone for which it does not
	    // belong to the acceptance set.
	    unsigned add = 0;
	    for (unsigned set = 0; set < num_sets; ++set)
	      {
		add += n;
		if (!oldacc.has(curacc, set))
		  {
		    // Clone the edge
		    res->new_acc_edge(src + add, dst + add, cond);
		    assert(dst + add < sink);
		    // Using `t' is disallowed from now on as it is a
		    // reference to a edge that may have been
		    // reallocated.

		    // At least one edge per cycle should have a
		    // nondeterministic copy from the original clone.
		    // We use state numbers to select it, as any cycle
		    // is guaranteed to have at least one edge
		    // with dst <= src.  FIXME: Computing a feedback
		    // arc set would be better.
		    if (dst <= src)
		      res->new_edge(src, dst + add, cond);
		  }
	      }
	    assert(add == num_sets * n);
	  }
	// Complete the original automaton.
	if (missingcond != bddfalse)
	  res->new_edge(src, sink, missingcond);
      }
    res->merge_edges();
    res->purge_dead_states();
    return res;
  }

  twa_graph_ptr dtgba_complement_weak(const const_twa_graph_ptr& aut)
  {
    // Clone the original automaton.
    auto res = make_twa_graph(aut,
				 { true, // state based
				   true, // inherently weak
				   true, // determinisitic
				   true,  // stutter inv.
				 });
    scc_info si(res);

    // We will modify res in place, and the resulting
    // automaton will only have one acceptance set.
    acc_cond::mark_t all_acc = res->set_buchi();
    res->prop_state_based_acc();

    unsigned sink = res->num_states();

    for (unsigned src = 0; src < sink; ++src)
      {
	acc_cond::mark_t acc = 0U;
	unsigned scc = si.scc_of(src);
	if (si.is_rejecting_scc(scc) && !si.is_trivial(scc))
	  acc = all_acc;

	// Keep track of all conditions on edge leaving state
	// SRC, so we can complete it.
	bdd missingcond = bddtrue;
	for (auto& t: res->out(src))
	  {
	    missingcond -= t.cond;
	    t.acc = acc;
	  }
	// Complete the original automaton.
	if (missingcond != bddfalse)
	  {
	    if (res->num_states() == sink)
	      {
		res->new_state();
		res->new_acc_edge(sink, sink, bddtrue);
	      }
	    res->new_edge(src, sink, missingcond);
	  }
      }
    //res->merge_edges();
    return res;
  }

  twa_graph_ptr dtgba_complement(const const_twa_graph_ptr& aut)
  {
    if (aut->acc().is_generalized_buchi())
      {
	if (aut->is_inherently_weak())
	  return dtgba_complement_weak(aut);
	else
	  return dtgba_complement_nonweak(aut);
      }
    else
      {
	// Simply complete the automaton, and complement its
	// acceptance.
	auto res = cleanup_acceptance_here(tgba_complete(aut));
	res->set_acceptance(res->num_sets(),
			    res->get_acceptance().complement());
	return res;
      }
  }
}
