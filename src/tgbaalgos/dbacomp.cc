// -*- coding: utf-8 -*-
// Copyright (C) 2013 Laboratoire de Recherche et Développement
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

#include "dbacomp.hh"
#include "ltlast/constant.hh"
#include "reachiter.hh"

namespace spot
{

  namespace
  {
    class dbacomp_iter: public tgba_reachable_iterator_depth_first
    {
      bdd orig_acc_;
      bdd acc_;
      bdd_dict* dict_;
      tgba_explicit_number* out_;
      typedef state_explicit_number::transition trans;
    public:
      dbacomp_iter(const tgba* a)
	: tgba_reachable_iterator_depth_first(a),
	  dict_(a->get_dict()),
	  out_(new tgba_explicit_number(dict_))
      {
	dict_->register_all_variables_of(a, out_);
	unsigned c = a->number_of_acceptance_conditions();
	orig_acc_ = a->all_acceptance_conditions();
	if (c == 1)
	  {
	    out_->copy_acceptance_conditions_of(a);
	    acc_ = orig_acc_;
	  }
	else
	  {
	    // If there is no acceptance conditions in the original
	    // automaton, add one.
	    assert(c == 0);
	    int accvar = dict_->register_acceptance_variable
	      (ltl::constant::true_instance(), out_);
	    acc_ = bdd_ithvar(accvar);
	    out_->set_acceptance_conditions(acc_);
	  }
      }

      tgba_explicit_number*
      result()
      {
	return out_;
      }

      void
      end()
      {
	out_->merge_transitions();
	// create a sink state if needed.
	if (out_->has_state(0))
	  {
	    trans* t = out_->create_transition(0, 0);
	    t->condition = bddtrue;
	    t->acceptance_conditions = acc_;
	  }
      }

      void process_state(const state*, int n,
			 tgba_succ_iterator* i)
      {
	// add a transition to a sink state if the state is not complete.
	bdd all = bddtrue;
	for (i->first(); !i->done(); i->next())
	  all -= i->current_condition();
	if (all != bddfalse)
	  {
	    trans* t = out_->create_transition(n, 0);
	    t->condition = all;
	  }
      }

      void
      process_link(const state*, int in,
		   const state*, int out,
		   const tgba_succ_iterator* si)
      {
	assert(in > 0);
	assert(out > 0);
	bdd a = si->current_acceptance_conditions();

	// Positive states represent a non-accepting copy of the
	// original automaton.
	trans* t1 = out_->create_transition(in, out);
	t1->condition = si->current_condition();

	// Negative states encode a copy of the automaton in which all
	// accepting transitions have been removed, and all the
	// remaining transitions are now accepting.
	if (a != orig_acc_)
	  {
	    trans* t2 = out_->create_transition(-in, -out);
	    t2->condition = si->current_condition();
	    t2->acceptance_conditions = acc_;
	  }

	// A non-deterministic transition between the two copies.
	trans* t3 = out_->create_transition(in, -out);
	t3->condition = si->current_condition();
      }

    };

  } // anonymous

  tgba_explicit_number* dba_complement(const tgba* aut)
  {
    dbacomp_iter dci(aut);
    dci.run();
    return dci.result();
  }
}
