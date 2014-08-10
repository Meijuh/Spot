// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014 Laboratoire de Recherche et Développement
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

#include "dtgbacomp.hh"
#include "ltlast/constant.hh"
#include "dupexp.hh"

namespace spot
{
  tgba_digraph* dtgba_complement(const tgba* aut)
  {
    // Clone the original automaton.
    tgba_digraph* res = tgba_dupexp_dfs(aut);

    auto dict = res->get_dict();

    bdd oldaccs = aut->all_acceptance_conditions();
    bdd oldnegs = aut->neg_acceptance_conditions();

    // We will modify res in place, and the resulting
    // automaton will only have one acceptance set.
    dict->unregister_all_typed_variables(bdd_dict::acc, res);
    bdd theacc =
      bdd_ithvar(dict->register_acceptance_variable
		 (ltl::constant::true_instance(), res));
    res->set_acceptance_conditions(theacc);

    unsigned num_acc =  aut->number_of_acceptance_conditions();
    unsigned n = res->num_states();
    // We will duplicate the automaton as many times as we have
    // acceptance sets, and we need one extra sink state.
    res->new_states(num_acc * n + 1);
    unsigned sink = res->num_states() - 1;
    // The sink state has an accepting self-loop.
    res->new_transition(sink, sink, bddtrue, theacc);

    for (unsigned src = 0; src < n; ++src)
      {
	// Keep track of all conditions on transition leaving state
	// SRC, so we can complete it.
	bdd missingcond = bddtrue;
	for (auto& t: res->out(src))
	  {
	    if (t.dst >= n)	// Ignore transition we added.
	      break;
	    missingcond -= t.cond;
	    bdd curacc = t.acc;
	    // The original transition must not accept anymore.
	    t.acc = bddfalse;
	    // Transition that were fully accepting are never cloned.
	    if (curacc == oldaccs)
	      continue;
	    // Save t.cond and t.dst as the reference to t
	    // is invalided by calls to new_transition().
	    unsigned dst = t.dst;
	    bdd cond = t.cond;
	    // We want all acceptance bdd variable to appear in curacc.
	    if (curacc == bddfalse)
	      curacc = oldnegs;

	    // Iterate over all the acceptance conditions in 'curacc',
	    // an duplicate it each each clone for which it does not
	    // belong to the acceptance set.
	    unsigned add = 0;
	    while (curacc != bddtrue)
	      {
		add += n;
		bdd h = bdd_high(curacc);
		if (h == bddfalse)
		  {
		    // Clone the transition
		    res->new_transition(src + add, dst + add, cond, theacc);
		    assert(dst + add < sink);
		    // Using `t' is disallowed from now on as it is a
		    // reference to a transition that may have been
		    // reallocated.

		    // At least one transition per cycle should have a
		    // nondeterministic copy from the original clone.
		    // We use state numbers to select it, as any cycle
		    // is guaranteed to have at least one transition
		    // with dst <= src.  FIXME: Computing a feedback
		    // arc set would be better.
		    if (dst <= src)
		      res->new_transition(src, dst + add, cond);
		    curacc = bdd_low(curacc);
		  }
		else
		  {
		    // We know that only one variable can be positive
		    // on any branch, so since we have just seen such
		    // a variable, we want to go to explore its LOW
		    // branch for more positive variables.  The only
		    // case where we will not do that is if the LOW
		    // branch is false.  In that case we take the HIGH
		    // branch to enumerate all the remaining negated
		    // variables.
		    bdd tmp = bdd_low(curacc);
		    if (tmp != bddfalse)
		      curacc = tmp;
		    else
		      curacc = h;
		  }
	      }
	    assert(add == num_acc * n);
	  }
	// Complete the original automaton.
	if (missingcond != bddfalse)
	  res->new_transition(src, sink, missingcond);
      }
    res->merge_transitions();
    // FIXME: Remove unreachable states.
    return res;
  }
}
