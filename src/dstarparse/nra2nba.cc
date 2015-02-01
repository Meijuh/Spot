// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et
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

#include "public.hh"
#include "tgbaalgos/reachiter.hh"
#include "tgbaalgos/sccfilter.hh"

namespace spot
{
  namespace
  {
    // Christof Löding's Diploma Thesis: Methods for the
    // Transformation of ω-Automata: Complexity and Connection to
    // Second Order Logic.  Section 3.4.3: Rabin to Büchi.
    //
    // However beware that the {...,(Ei,Fi),...} pairs used by Löding
    // are reversed compared to the {...,(Li,Ui),...} pairs used by
    // several other people.  We have Ei=Ui and Fi=Li.
    class nra_to_nba_worker: public tgba_reachable_iterator_depth_first
    {
    public:
      // AUT is the automaton we iterate on, while A is the automaton
      // we read the acceptance conditions from.  Separating the two
      // makes its possible to mask AUT, as needed in dra_to_ba().
      nra_to_nba_worker(const const_dstar_aut_ptr& a, const_tgba_ptr aut):
	tgba_reachable_iterator_depth_first(aut),
	out_(make_tgba_digraph(aut->get_dict())),
	d_(a),
	num_states_(a->aut->num_states())
      {
	out_->copy_ap_of(aut);
	out_->set_single_acceptance_set();
	out_->prop_state_based_acc();
	out_->new_states(num_states_ * (d_->accpair_count + 1));
	out_->set_init_state(a->aut->get_init_state_number());
      }

      tgba_digraph_ptr
      result()
      {
	return out_;
      }

      void
      process_link(const state* sin, int,
		   const state* sout, int,
		   const tgba_succ_iterator* si)
      {
	int in = d_->aut->state_number(sin);
	int out = d_->aut->state_number(sout);

	bdd cond = si->current_condition();
	out_->new_transition(in, out, cond);

	// Create one clone of the automaton per accepting pair,
	// removing states from the Ui part of the (Li, Ui) pairs.
	// (Or the Ei part of Löding's (Ei, Fi) pairs.)
	bitvect& l = d_->accsets->at(2 * in);
	bitvect& u = d_->accsets->at(2 * in + 1);
	for (size_t i = 0; i < d_->accpair_count; ++i)
	  {
	    int shift = num_states_ * (i + 1);
	    // In the Ui set. (Löding's Ei set.)
	    if (!u.get(i))
	      {
		// Transition t1 is a non-deterministic jump
		// from the original automaton to the i-th clone.
		//
		// Transition t2 constructs the clone.
		//
		// Löding creates transition t1 regardless of the
		// acceptance set.  We restrict it to the non-Li
		// states.  Both his definition and this
		// implementation create more transitions than needed:
		// we do not need more than one transition per
		// accepting cycle.
		out_->new_transition(in, out + shift, cond);

		// A transition is accepting if it is in the Li
		// set. (Löding's Fi set.)
		out_->new_acc_transition(in + shift, out + shift, cond,
					 l.get(i));
	      }
	  }
      }

    protected:
      tgba_digraph_ptr out_;
      const_dstar_aut_ptr d_;
      size_t num_states_;
    };

  }

  // In dra_to_dba() we call this function with a second argument
  // that is a masked version of nra->aut.
  SPOT_LOCAL
  tgba_digraph_ptr nra_to_nba(const const_dstar_aut_ptr& nra,
			      const const_tgba_ptr& aut)
  {
    assert(nra->type == Rabin);
    nra_to_nba_worker w(nra, aut);
    w.run();
    return scc_filter_states(w.result());
  }

  tgba_digraph_ptr nra_to_nba(const const_dstar_aut_ptr& nra)
  {
    return nra_to_nba(nra, nra->aut);
  }

}
