// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014 Laboratoire de
// Recherche et Développement de l'Epita (LRDE).
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

#include "sccfilter.hh"
#include "reachiter.hh"
#include "sccinfo.hh"

namespace spot
{
  namespace
  {
    // BDD.id -> Acc number
    typedef std::map<int, unsigned> accremap_t;
    typedef std::vector<accremap_t> remap_table_t;

    typedef std::tuple<bool, bdd, acc_cond::mark_t> filtered_trans;


    // SCC filters are objects with two methods:
    //  state(src) return true iff s should be kept
    //  trans(src, dst, cond, acc) returns a triplet
    //     (keep, cond2, acc2) where keep is a Boolean stating if the
    //                      transition should be kept, and cond2/acc2
    //                      give replacement values for cond/acc
    struct id_filter
    {
      scc_info* si;
      id_filter(scc_info* si)
	: si(si)
      {
      }

      // Accept all states
      bool state(unsigned)
      {
	return true;
      }

      unsigned accsets(unsigned n)
      {
	return n;
      }

      // Accept all transitions, unmodified
      filtered_trans trans(unsigned, unsigned, bdd cond, acc_cond::mark_t acc)
      {
	return filtered_trans{true, cond, acc};
      }
    };

    // Remove useless states.
    template <class next_filter = id_filter>
    struct state_filter: next_filter
    {
      template<typename... Args>
      state_filter(scc_info* si, Args&&... args)
	: next_filter(si, std::forward<Args>(args)...)
      {
      }

      bool state(unsigned s)
      {
	return this->next_filter::state(s) && this->si->is_useful_state(s);
      }
    };

    // Suspension filter, used only by compsusp.cc
    template <class next_filter = id_filter>
    struct susp_filter: next_filter
    {
      bdd suspvars;
      bdd ignoredvars;
      bool early_susp;

      template<typename... Args>
      susp_filter(scc_info* si,
		  bdd suspvars, bdd ignoredvars, bool early_susp,
		  Args&&... args)
	: next_filter(si, std::forward<Args>(args)...),
	  suspvars(suspvars),
	  ignoredvars(ignoredvars),
	  early_susp(early_susp)
      {
      }

      filtered_trans trans(unsigned src, unsigned dst,
			   bdd cond, acc_cond::mark_t acc)
      {
	bool keep;
	std::tie(keep, cond, acc) =
	  this->next_filter::trans(src, dst, cond, acc);

	if (keep)
	  {
	    // Always remove ignored variables
	    cond = bdd_exist(cond, ignoredvars);

	    // Remove the suspension variables only if
	    // the destination in not in an accepting SCC,
	    // or if we are between SCC with early_susp unset.
	    unsigned u = this->si->scc_of(dst);
	    if (!this->si->is_accepting_scc(u)
		|| (!early_susp && (u != this->si->scc_of(src))))
	      cond = bdd_exist(cond, suspvars);
	  }

	return filtered_trans(keep, cond, acc);
      }
    };

    // Remove acceptance conditions from all transitions outside of
    // non-accepting SCCs.
    template <class next_filter = id_filter>
    struct acc_filter_all: next_filter
    {
      template<typename... Args>
      acc_filter_all(scc_info* si, Args&&... args)
	: next_filter(si, std::forward<Args>(args)...)
      {
      }

      filtered_trans trans(unsigned src, unsigned dst,
			   bdd cond, acc_cond::mark_t acc)
      {
	bool keep;
	std::tie(keep, cond, acc) =
	  this->next_filter::trans(src, dst, cond, acc);

	if (keep)
	  {
	    unsigned u = this->si->scc_of(src);
	    // If the transition is between two SCCs, or in a
	    // non-accepting SCC.  Remove the acceptance sets.
	    if (!this->si->is_accepting_scc(u) || u != this->si->scc_of(dst))
	      acc = 0U;
	  }

	return filtered_trans(keep, cond, acc);
      }
    };

    // Remove acceptance conditions from all transitions whose
    // destination is not an accepting SCCs.
    template <class next_filter = id_filter>
    struct acc_filter_some: next_filter
    {
      template<typename... Args>
      acc_filter_some(scc_info* si, Args&&... args)
	: next_filter(si, std::forward<Args>(args)...)
      {
      }

      filtered_trans trans(unsigned src, unsigned dst,
			   bdd cond, acc_cond::mark_t acc)
      {
	bool keep;
	std::tie(keep, cond, acc) =
	  this->next_filter::trans(src, dst, cond, acc);

	if (!this->si->is_accepting_scc(this->si->scc_of(dst)))
	  acc = 0U;
	return filtered_trans(keep, cond, acc);
      }
    };

    // Simplify redundant acceptance sets used in each SCCs.
    template <class next_filter = id_filter>
    struct acc_filter_simplify: next_filter
    {
      // Acceptance sets to strip in each SCC.
      std::vector<acc_cond::mark_t> strip_;

      template<typename... Args>
      acc_filter_simplify(scc_info* si, Args&&... args)
	: next_filter(si, std::forward<Args>(args)...)
      {
      }

      unsigned accsets(unsigned n)
      {
	unsigned scc_count = this->si->scc_count();
	auto& acc = this->si->get_aut()->acc();
	assert(n == acc.num_sets());
	(void) n;

	auto used_acc = this->si->used_acc();
	assert(used_acc.size() == scc_count);
	strip_.resize(scc_count);
	std::vector<unsigned> cnt(scc_count); // # of useful sets in each SCC
	unsigned max = 0;		      // Max number of useful sets
	for (unsigned n = 0; n < scc_count; ++n)
	  {
	    if (!this->si->is_accepting_scc(n))
	      continue;
	    strip_[n] = acc.useless(used_acc[n].begin(), used_acc[n].end());
	    cnt[n] = acc.num_sets() - strip_[n].count();
	    if (cnt[n] > max)
	      max = cnt[n];
	  }
	// Now that we know about the max number of acceptance
	// conditions, add extra acceptance conditions to those SCC
	// that do not have enough.
	for (unsigned n = 0; n < scc_count; ++n)
	  {
	    if (!this->si->is_accepting_scc(n))
	      continue;
	    if (cnt[n] < max)
	      strip_[n].remove_some(max - cnt[n]);
	  }
	return max;
      }

      filtered_trans trans(unsigned src, unsigned dst, bdd cond,
			   acc_cond::mark_t acc)
      {
	bool keep;
	std::tie(keep, cond, acc) =
	  this->next_filter::trans(src, dst, cond, acc);

	if (keep && acc)
	  {
	    unsigned u = this->si->scc_of(dst);

	    if (!this->si->is_accepting_scc(u))
	      acc = 0U;
	    else
	      acc = this->si->get_aut()->acc().strip(acc, strip_[u]);
	  }
	return filtered_trans{keep, cond, acc};
      }
    };


    template<class F, typename... Args>
    tgba_digraph_ptr scc_filter_apply(const_tgba_digraph_ptr aut,
				   scc_info* given_si, Args&&... args)
    {
      tgba_digraph_ptr filtered = make_tgba_digraph(aut->get_dict());
      unsigned in_n = aut->num_states(); // Number of input states.
      if (in_n == 0)			 // Nothing to filter.
	return filtered;
      filtered->copy_ap_of(aut);

      // Compute scc_info if not supplied.
      scc_info* si = given_si;
      if (!si)
	si = new scc_info(aut);

      F filter(si, std::forward<Args>(args)...);

      // Renumber all useful states.
      unsigned out_n = 0;		 // Number of output states.
      std::vector<unsigned> inout; // Associate old states to new ones.
      inout.reserve(in_n);
      for (unsigned i = 0; i < in_n; ++i)
	if (filter.state(i))
	  inout.push_back(out_n++);
	else
	  inout.push_back(-1U);

      filtered->
	set_acceptance_conditions(filter.accsets(aut->acc().num_sets()));
      filtered->new_states(out_n);
      for (unsigned isrc = 0; isrc < in_n; ++isrc)
	{
	  unsigned osrc = inout[isrc];
	  if (osrc >= out_n)
	    continue;
	  for (auto& t: aut->out(isrc))
	    {
	      unsigned odst = inout[t.dst];
	      if (odst >= out_n)
		continue;
	      bool want;
	      bdd cond;
	      acc_cond::mark_t acc;
	      std::tie(want, cond, acc) =
		filter.trans(isrc, t.dst, t.cond, t.acc);
	      if (want)
		filtered->new_transition(osrc, odst, cond, acc);
	    }
	}
      if (!given_si)
	delete si;
      // If the initial state has been filtered out, we don't attempt
      // to fix it.
      auto init = inout[aut->get_init_state_number()];
      if (init < out_n)
	filtered->set_init_state(init);
      return filtered;
    }


  }

  tgba_digraph_ptr
  scc_filter_states(const const_tgba_digraph_ptr& aut, scc_info* given_si)
  {
    auto res = scc_filter_apply<state_filter<>>(aut, given_si);
    res->prop_copy(aut, true, true, true, true);
    return res;
  }

  tgba_digraph_ptr
  scc_filter(const const_tgba_digraph_ptr& aut, bool remove_all_useless,
	     scc_info* given_si)
  {
    tgba_digraph_ptr res;
    if (remove_all_useless)
      res = scc_filter_apply<state_filter
			     <acc_filter_all
			      <acc_filter_simplify<>>>>(aut, given_si);
    else
      res = scc_filter_apply<state_filter
			     <acc_filter_some
			      <acc_filter_simplify<>>>>(aut, given_si);
    res->merge_transitions();
    res->prop_copy(aut,
		   false,  // state-based acceptance is not preserved
		   true,
		   true,
		   true);
    return res;
  }

  tgba_digraph_ptr
  scc_filter_susp(const const_tgba_digraph_ptr& aut, bool remove_all_useless,
		  bdd suspvars, bdd ignoredvars, bool early_susp,
		  scc_info* given_si)
  {
    tgba_digraph_ptr res;
    if (remove_all_useless)
      res = scc_filter_apply<susp_filter
			     <state_filter
			      <acc_filter_all
			       <acc_filter_simplify<>>>>>(aut, given_si,
							  suspvars,
							  ignoredvars,
							  early_susp);
    else
      res = scc_filter_apply<susp_filter
			     <state_filter
			      <acc_filter_some
			       <acc_filter_simplify<>>>>>(aut, given_si,
							  suspvars,
							  ignoredvars,
							  early_susp);
    res->merge_transitions();
    res->prop_copy(aut,
		   false,  // state-based acceptance is not preserved
		   true,
		   true,
		   false);	// determinism may not be preserved
    return res;
  }

}
