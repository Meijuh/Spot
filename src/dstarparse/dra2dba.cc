// Copyright (C) 2013 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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
#include "ltlast/constant.hh"

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
  tgba* nra_to_nba(const dstar_aut* nra, const tgba* aut);

  namespace
  {
    typedef std::list<const state*> state_list;

    static bool
    filter_states(const tgba* aut,
		  const dstar_aut* dra,
		  const state_list& sl,
		  state_list& final,
		  state_list& nonfinal);

    static bool
    filter_scc(const tgba* aut,
	       const dstar_aut* dra,
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
    filter_states(const tgba* aut,
		  const dstar_aut* dra,
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
      int num = dra->aut->get_label(*it++);
      bitvect* l = dra->accsets->at(num * 2).clone();
      bitvect* u = dra->accsets->at(num * 2 + 1).clone();
      for (; it != sl.end(); ++it)
	{
	  num = dra->aut->get_label(*it);
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
	    const tgba* masked =
	      build_tgba_mask_keep(dra->aut, keep, sl.front());
	    const tgba* nba = nra_to_nba(dra, masked);
	    emptiness_check* ec = couvreur99(nba);
	    emptiness_check_result* ecr = ec->check();
	    delete ecr;
	    delete ec;
	    delete nba;
	    delete masked;
	    if (ecr)
	      {
		// This SCC is not DBA-realizable.
		//std::cerr << "not DBA-realizable\n";
		return false;
	      }
	  }
	  //std::cerr << "non-accepting\n";
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
	  num = dra->aut->get_label(*it);
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
	  const tgba* scc_mask =
	    build_tgba_mask_keep(aut, unknown, *unknown.begin());
	  state_list local_final;
	  state_list local_nonfinal;
	  bool dbarealizable =
	    filter_scc(scc_mask, dra, local_final, local_nonfinal);
	  delete scc_mask;
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



    class dra_to_dba_worker: public tgba_reachable_iterator_depth_first
    {
    public:
      dra_to_dba_worker(const tgba_explicit_number* a, const state_set& final):
	tgba_reachable_iterator_depth_first(a),
	in_(a),
	out_(new tgba_explicit_number(a->get_dict())),
	final_(final)
      {
	bdd_dict* bd = a->get_dict();
	bd->register_all_variables_of(a, out_);

	// Invent a new acceptance set for the degeneralized automaton.
	int accvar =
	  bd->register_acceptance_variable(ltl::constant::true_instance(),
					   out_);
	acc_ = bdd_ithvar(accvar);
	out_->set_acceptance_conditions(acc_);
      }

      tgba_explicit_number*
      result()
      {
	return out_;
      }

      void
      process_link(const state* sin, int,
		   const state* sout, int,
		   const tgba_succ_iterator* si)
      {
	int in = in_->get_label(sin);
	int out = in_->get_label(sout);

	typedef state_explicit_number::transition trans;
	trans* t = out_->create_transition(in, out);
	bdd cond = t->condition = si->current_condition();

	if (final_.find(sin) != final_.end())
	  t->acceptance_conditions = acc_;
      }

    protected:
      const tgba_explicit_number* in_;
      tgba_explicit_number* out_;
      const tgba* d_;
      const state_set& final_;
      bdd acc_;
    };

  }


  tgba* dra_to_dba(const dstar_aut* dra)
  {
    assert(dra->type == Rabin);

    state_list final;
    state_list nonfinal;
    if (!filter_scc(dra->aut, dra, final, nonfinal))
      return 0;

    // for (state_list::const_iterator i = final.begin();
    // 	 i != final.end(); ++i)
    //   std::cerr << dra->aut->get_label(*i) << " is final\n";
    // for (state_list::const_iterator i = nonfinal.begin();
    // 	 i != nonfinal.end(); ++i)
    //   std::cerr << dra->aut->get_label(*i) << " is non-final\n";

    state_set fs(final.begin(), final.end());
    dra_to_dba_worker w(dra->aut, fs);
    w.run();
    tgba_explicit_number* res1 = w.result();
    tgba* res2 = scc_filter_states(res1);
    delete res1;
    return res2;
  }

}
