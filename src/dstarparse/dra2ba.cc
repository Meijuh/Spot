// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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
#include "tgba/tgbamask.hh"
#include "tgbaalgos/scc.hh"
#include "tgbaalgos/reachiter.hh"
#include "tgbaalgos/gtec/gtec.hh"
#include "tgbaalgos/sccfilter.hh"
#include "tgbaalgos/dotty.hh"

namespace spot
{

  // IMPORTANT NOTE: If you attempt to follow Krishnan et
  // al. (ISAAC'94) paper while reading this code, make sure you
  // understand the difference between their Rabin acceptance
  // definition and the one we are using.
  //
  // Here, a cycle is accepting in a Rabin automaton if there exists
  // an acceptance pair (Lᵢ, Uᵢ) such that some states from Lᵢ are
  // visited while no states from Uᵢ are visited.   This is the
  // same definition used by ltl2dstar.
  //
  // In the Krishnan et al. paper, a cycle is accepting in a Rabin
  // automaton if there exists an acceptance pair (Lᵢ, Uᵢ) such that
  // some states from Lᵢ are visited and all visited states belongs to
  // Uᵢ.  In other words, you can switch from one definition to
  // the other by complementing the Uᵢ set.
  //
  // This is a source of confusion; you have been warned.


  // This function is defined in nra2nba.cc, and used only here.
  SPOT_LOCAL
  twa_graph_ptr nra_to_nba(const const_dstar_aut_ptr& nra,
			      const const_tgba_ptr& aut);

  namespace
  {
    typedef std::list<const state*> state_list;

    // The functions that take aut and dra as first arguments are
    // either called on the main automaton, in which case dra->aut ==
    // aut, or it is called on a sub-automaton in which case aut is a
    // masked version of dra->aut.  So we should always explore the
    // automaton aut, but because the state of aut are states of
    // dra->aut, we can use dra->aut to get labels, and dra->acccs to
    // retrive acceptances.

    static bool
    filter_states(const const_tgba_ptr& aut,
		  const const_dstar_aut_ptr& dra,
		  const state_list& sl,
		  state_list& final,
		  state_list& nonfinal);

    static bool
    filter_scc(const const_tgba_ptr& aut,
	       const const_dstar_aut_ptr& dra,
	       state_list& final,
	       state_list& nonfinal)
    {
      // Iterate over all non-trivial SCCs.
      scc_map sm(aut);
      sm.build_map();
      for (unsigned scc_max = sm.scc_count(), scc = 0;
	   scc < scc_max; ++scc)
	{
	  if (sm.trivial(scc))
	    {
	      nonfinal.push_back(sm.one_state_of(scc));
	      continue;
	    }

	  // Get the list of states of that SCC
	  const std::list<const state*>& sl = sm.states_of(scc);
	  assert(!sl.empty());
	  if (!filter_states(aut, dra, sl, final, nonfinal))
	    return false;
      }
      return true;
    }

    static bool
    filter_states(const const_tgba_ptr& aut,
		  const const_dstar_aut_ptr& dra,
		  const state_list& sl,
		  state_list& final,
		  state_list& nonfinal)
    {
      // Check whether the SCC composed of all states in sl contains
      // non-accepting cycles.
      //
      // A cycle is accepting (in a Rabin automaton) if there exists
      // an acceptance pair (Lᵢ, Uᵢ) such that some states from Lᵢ
      // are visited while no states from Uᵢ are visited.
      //
      // Consequently, a cycle is non-accepting if for all acceptance
      // pairs (Lᵢ, Uᵢ), either no states from Lᵢ are visited or some
      // states from Uᵢ are visited.  (This corresponds to an
      // accepting cycle with Streett acceptance.)
      //
      // Now we consider the SCC as one large cycle and check its
      // intersection with all Lᵢs and Uᵢs.  Let l=[l₁,l₂,...] and
      // u=[u₁,u₂,...] be bitvectors where bit lᵢ (resp. uᵢ)
      // indicates that Lᵢ (resp. Uᵢ) has been visited in the SCC.
      state_list::const_iterator it = sl.begin();
      int num = dra->aut->state_number(*it++);
      bitvect* l = dra->accsets->at(num * 2).clone();
      bitvect* u = dra->accsets->at(num * 2 + 1).clone();
      for (; it != sl.end(); ++it)
	{
	  num = dra->aut->state_number(*it);
	  *l |= dra->accsets->at(num * 2);
	  *u |= dra->accsets->at(num * 2 + 1);
	}
      // If we have l&!u = [0,0,...] that means that the cycle formed
      // by the entire SCC is not accepting.  However that does not
      // necessarily imply that all cycles in the SCC are also
      // non-accepting.  We may have a smaller cycle that is
      // accepting, but which becomes non-accepting when extended with
      // more states.
      *l -= *u;
      delete u;
      if (l->is_fully_clear())
	{
	  delete l;
	  // Check whether the SCC is accepting.  We do that by simply
	  // converting that SCC into a TGBA and running our emptiness
	  // check.  This is not a really smart implementation and
	  // could be improved.
	  {
	    state_set keep(sl.begin(), sl.end());
	    auto masked = build_tgba_mask_keep(dra->aut, keep, sl.front());
	    if (!nra_to_nba(dra, masked)->is_empty())
	      // This SCC is not DBA-realizable.
	      return false;
	  }
	  for (state_list::const_iterator i = sl.begin();
	       i != sl.end(); ++i)
	    nonfinal.push_back(*i);
	  return true;
	}
      // The bits sets in *l corresponds to Lᵢs that have been seen
      // without seeing the matching Uᵢ.  In this SCC, any state in Lᵢ
      // is therefore final.  Otherwise we do not know: it is possible
      // that there is a non-accepting cycle in the SCC that do not
      // visit Lᵢ.
      state_set unknown;
      for (it = sl.begin(); it != sl.end(); ++it)
	{
	  num = dra->aut->state_number(*it);
	  bitvect* l2 = dra->accsets->at(num * 2).clone();
	  *l2 &= *l;
	  if (!l2->is_fully_clear())
	    {
	      final.push_back(*it);
	    }
	  else
	    {
	      unknown.insert(*it);
	    }
	  delete l2;
	}
      delete l;
      // Check whether it is possible to build non-accepting cycles
      // using only the "unknown" states.
      while (!unknown.empty())
	{
	  //std::cerr << "unknown\n";
	  // Build a sub-automaton for just the unknown states,
	  // starting from any state in the SCC.
	  auto scc_mask = build_tgba_mask_keep(aut, unknown, *unknown.begin());
	  state_list local_final;
	  state_list local_nonfinal;
	  bool dbarealizable =
	    filter_scc(scc_mask, dra, local_final, local_nonfinal);
	  if (!dbarealizable)
	    return false;
	  for (state_list::const_iterator i = local_final.begin();
	       i != local_final.end(); ++i)
	    unknown.erase(*i);
	  final.splice(final.end(), local_final);
	  for (state_list::const_iterator i = local_nonfinal.begin();
	       i != local_nonfinal.end(); ++i)
	    unknown.erase(*i);
	  nonfinal.splice(nonfinal.end(), local_nonfinal);
	}
      return true;
    }



    class dra_to_ba_worker: public tgba_reachable_iterator_depth_first
    {
    public:
      dra_to_ba_worker(const const_dstar_aut_ptr& a,
		       const state_set& final,
		       const scc_map& sm,
		       const std::vector<bool>& realizable):
	tgba_reachable_iterator_depth_first(a->aut),
	in_(a),
	out_(make_twa_graph(a->aut->get_dict())),
	final_(final),
	num_states_(a->aut->num_states()),
	sm_(sm),
	realizable_(realizable)
      {
	out_->copy_ap_of(a->aut);
	out_->prop_state_based_acc();
	acc_ = out_->set_buchi();
	out_->new_states(num_states_ * (a->accpair_count + 1));
	out_->set_init_state(a->aut->get_init_state_number());

      }

      twa_graph_ptr
      result()
      {
	return out_;
      }

      void
      process_link(const state* sin, int,
		   const state* sout, int,
		   const tgba_succ_iterator* si)
      {
	int in = in_->aut->state_number(sin);
	int out = in_->aut->state_number(sout);
	unsigned in_scc = sm_.scc_of_state(sin);

	bdd cond = si->current_condition();
	unsigned t = out_->new_transition(in, out, cond);

	if (realizable_[in_scc])
	  {
	    if (final_.find(sin) != final_.end())
	      out_->trans_data(t).acc = acc_;
	  }
	else if (sm_.scc_of_state(sout) == in_scc)
	  {
	    // Create one clone of the SCC per accepting pair,
	    // removing states from the Ui part of the (Li, Ui) pairs.
	    // (Or the Ei part of Löding's (Ei, Fi) pairs.)
	    bitvect& l = in_->accsets->at(2 * in);
	    bitvect& u = in_->accsets->at(2 * in + 1);
	    for (size_t i = 0; i < in_->accpair_count; ++i)
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

		    // Acceptance transitions are those in the Li
		    // set. (Löding's Fi set.)
		    out_->new_acc_transition(in + shift, out + shift, cond,
					     l.get(i));
		  }
	      }
	  }
      }

    protected:
      const const_dstar_aut_ptr& in_;
      twa_graph_ptr out_;
      const state_set& final_;
      size_t num_states_;
      acc_cond::mark_t acc_;
      const scc_map& sm_;
      const std::vector<bool>& realizable_;
    };

  }


  twa_graph_ptr dra_to_ba(const const_dstar_aut_ptr& dra, bool* dba)
  {
    assert(dra->type == Rabin);

    state_list final;
    state_list nonfinal;

    // Iterate over all non-trivial SCCs.
    scc_map sm(dra->aut);
    sm.build_map();
    unsigned scc_max = sm.scc_count();

    bool dba_realizable = true;
    std::vector<bool> realizable(scc_max);

    for (unsigned scc = 0; scc < scc_max; ++scc)
      {
	if (sm.trivial(scc))
	  {
	    realizable[scc] = true;
	    continue;
	  }

	// Get the list of states of that SCC
	const std::list<const state*>& sl = sm.states_of(scc);
	assert(!sl.empty());
	bool scc_realizable = filter_states(dra->aut, dra, sl, final, nonfinal);
	dba_realizable &= scc_realizable;
	realizable[scc] = scc_realizable;
	//std::cerr << "realizable[" << scc << "] = " << scc_realizable << '\n';
      }

    if (dba)
      *dba = dba_realizable;

    // for (state_list::const_iterator i = final.begin();
    // 	 i != final.end(); ++i)
    //   std::cerr << dra->aut->get_label(*i) << " is final\n";
    // for (state_list::const_iterator i = nonfinal.begin();
    // 	 i != nonfinal.end(); ++i)
    //   std::cerr << dra->aut->get_label(*i) << " is non-final\n";

    state_set fs(final.begin(), final.end());
    dra_to_ba_worker w(dra, fs, sm, realizable);
    w.run();
    return scc_filter_states(w.result());
  }

}
