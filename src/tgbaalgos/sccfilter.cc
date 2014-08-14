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
#include "scc.hh"
#include "sccinfo.hh"

namespace spot
{
  namespace
  {
    // BDD.id -> Acc number
    typedef std::map<int, unsigned> accremap_t;
    typedef std::vector<accremap_t> remap_table_t;

    typedef std::tuple<bool, bdd, bdd> filtered_trans;
    typedef std::pair<bdd, bdd> acc_pair;


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

      acc_pair accsets(bdd all, bdd all_neg)
      {
	return acc_pair(all, all_neg);
      }

      // Accept all transitions, unmodified
      filtered_trans trans(unsigned, unsigned, bdd cond, bdd acc)
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
			   bdd cond, bdd acc)
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
			   bdd cond, bdd acc)
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
	      acc = bddfalse;
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
			   bdd cond, bdd acc)
      {
	bool keep;
	std::tie(keep, cond, acc) =
	  this->next_filter::trans(src, dst, cond, acc);

	if (!this->si->is_accepting_scc(this->si->scc_of(dst)))
	  acc = bddfalse;
	return filtered_trans(keep, cond, acc);
      }
    };

    // Simplify redundant acceptance sets used in each SCCs.
    template <class next_filter = id_filter>
    struct acc_filter_simplify: next_filter
    {
      std::vector<bdd> acc_;
      typedef std::map<int, bdd> map_t;
      typedef std::vector<map_t> remap_t;
      remap_t remap_;

      template<typename... Args>
      acc_filter_simplify(scc_info* si, Args&&... args)
	: next_filter(si, std::forward<Args>(args)...)
      {
      }

      acc_pair accsets(bdd in_all, bdd in_all_neg)
      {
	std::tie(in_all, in_all_neg) =
	  this->next_filter::accsets(in_all, in_all_neg);

	unsigned scc_count = this->si->scc_count();
	remap_table_t remap_table(scc_count);
	std::vector<unsigned> max_table(scc_count);
	std::vector<bdd> useful_table(scc_count);
	std::vector<bdd> useless_table(scc_count);
	unsigned max_num = 1;
	const_tgba_digraph_ptr aut = this->si->get_aut();

	std::vector<bdd> used_acc = this->si->used_acc();

	for (unsigned n = 0; n < scc_count; ++n)
	  {
	    if (!this->si->is_accepting_scc(n))
	      continue;
	    bdd all = used_acc[n];

	    //std::cerr << "SCC #" << n << "; used = " << all << std::endl;

	    // Compute a set of useless acceptance sets.
	    // If the acceptance combinations occurring in
	    // the automata are  { a, ab, abc, bd }, then
	    // ALL contains (a&!b&!c&!d)|(a&b&!c&!d)|(a&b&c&!d)|(!a&b&!c&d)
	    // and we want to find that 'a' and 'b' are useless because
	    // they always occur with 'c'.
	    // The way we check if 'a' is useless is to look whether ALL
	    // implications (x -> a) for some other acceptance set x.
	    //
	    // The two while() loops in the code perform the equivalent of
	    //    for all a in allconds_a:
	    //       for all x in allconds_x:
	    //          check whether x -> a
	    //          ...
	    //
	    // Initially allconds_a = allconds_x contains all acceptance
	    // sets.  However when an acceptance set 'a' is determined to
	    // be useless, it can be removed from allconds_x from future
	    // iterations.
	    bdd allconds_a = bdd_support(in_all_neg);
	    bdd allconds_x = allconds_a;
	    bdd useless = bddtrue;
	    while (allconds_a != bddtrue)
	      {
		// Speed-up the computation of implied acceptance sets by
		// removing those that are always present.  We detect
		// those that appear as conjunction of positive variables
		// at the start of ALL.
		bdd prefix = bdd_satprefix(all);
		if (prefix != bddtrue)
		  {
		    assert(prefix == bdd_support(prefix));
		    allconds_a = bdd_exist(allconds_a, prefix);
		    if (allconds_a != bddtrue)
		      {
			useless &= prefix;
		      }
		    else
		      {
			// Never erase all conditions: at least keep one.
			useless &= bdd_high(prefix);
			break;
		      }
		    allconds_x = bdd_exist(allconds_x, prefix);
		  }

		// Pick an acceptance set 'a'.
		bdd a = bdd_ithvar(bdd_var(allconds_a));
		// For all acceptance sets 'x' that are not already
		// useless...
		bdd others = allconds_x;
		while (others != bddtrue)
		  {
		    bdd x = bdd_ithvar(bdd_var(others));
		    // ... check whether 'x' always implies 'a'.
		    if (x != a && bdd_implies(all, x >> a))
		      {
			// If so, 'a' is useless.
			all = bdd_exist(all, a);
			useless &= a;
			allconds_x = bdd_exist(allconds_x, a);
			break;
		      }
		    others = bdd_high(others);
		  }
		allconds_a = bdd_high(allconds_a);
	      }

	    // We never remove ALL acceptance marks.
	    assert(in_all_neg == bddtrue || useless != bdd_support(in_all_neg));

	    useless_table[n] = useless;
	    bdd useful = bdd_exist(in_all_neg, useless);

	    //std::cerr << "SCC #" << n << "; useful = " << useful << std::endl;

	    // Go over all useful sets of acceptance marks, and give them
	    // a number.
	    unsigned num = 1;
	    // First compute the number of acceptance conditions used.
	    for (BDD c = useful.id(); c != 1; c = bdd_low(c))
	      ++num;
	    max_table[n] = num;
	    if (num > max_num)
	      max_num = num;

	    useful_table[n] = useful;
	  }

	// Now that we know about the max number of acceptance
	// conditions, add extra acceptance conditions to those SCC
	// that do not have enough.
	for (unsigned n = 0; n < scc_count; ++n)
	  {
	    if (!this->si->is_accepting_scc(n))
	      continue;
	    //std::cerr << "SCC " << n << '\n';
	    bdd useful = useful_table[n];

	    int missing = max_num - max_table[n];
	    bdd useless = useless_table[n];
	    while (missing--)
	      {
		//std::cerr << useful << "  :  " << useless << std::endl;
		useful &= bdd_nithvar(bdd_var(useless));
		useless = bdd_high(useless);
	      }
	    int num = max_num;
	    // Then number all of these acceptance conditions in the
	    // reverse order.  This makes sure that the associated number
	    // varies in the same direction as the bdd variables, which in
	    // turn makes sure we preserve the acceptance condition
	    // ordering (which matters for degeneralization).
	    for (BDD c = useful.id(); c != 1; c = bdd_low(c))
	      remap_table[n].emplace(bdd_var(c), --num);

	    max_table[n] = max_num;
	  }

	acc_.resize(max_num);
	acc_[0] = bddfalse;
	bdd tmp = in_all;
	assert(aut->number_of_acceptance_conditions() >= max_num - 1);

	bdd all = bddfalse;
	bdd all_neg = bddtrue;

	if (tmp != bddfalse)
	  {
	    for (unsigned n = max_num - 1; n > 0; --n)
	      {
	    	assert(tmp != bddfalse);
		int v = bdd_var(tmp);
		bdd vn = bdd_nithvar(v);
		all = (all & vn) | (all_neg & bdd_ithvar(v));
		all_neg &= vn;
	    	tmp = bdd_low(tmp);
	      }
	    tmp = in_all;
	    for (unsigned n = max_num - 1; n > 0; --n)
	      {
		int v = bdd_var(tmp);
		acc_[n] = bdd_compose(all_neg, bdd_nithvar(v), v);
		tmp = bdd_low(tmp);
	      }
	  }
	else
	  {
	    assert(max_num == 1);
	  }

	remap_.resize(scc_count);
	bdd all_orig_neg = in_all_neg;
	bdd all_sup = bdd_support(all_orig_neg);

	for (unsigned n = 0; n < scc_count; ++n)
	  {
	    //std::cerr << "SCC #" << n << '\n';
	    if (!this->si->is_accepting_scc(n))
	      continue;

	    bdd all = used_acc[n];
	    while (all != bddfalse)
	      {
		bdd one = bdd_satoneset(all, all_sup, bddtrue);
		all -= one;
		bdd res = bddfalse;
		bdd resacc = bddfalse;
		while (one != bddtrue)
		  {
		    if (bdd_high(one) == bddfalse)
		      {
			one = bdd_low(one);
			continue;
		      }
		    int vn = bdd_var(one);
		    bdd v = bdd_ithvar(vn);
		    resacc |= bdd_exist(all_orig_neg, v) & v;
		    res |= acc_[remap_table[n][vn]];
		    one = bdd_high(one);
		  }
		int id = resacc.id();
		//std::cerr << resacc << " -> " << res << '\n';
		remap_[n][id] = res;
	      }
	  }
	return acc_pair{all, all_neg};
      }

      filtered_trans trans(unsigned src, unsigned dst, bdd cond, bdd acc)
      {
	bool keep;
	std::tie(keep, cond, acc) =
	  this->next_filter::trans(src, dst, cond, acc);

	if (keep && acc != bddfalse)
	  {
	    unsigned u = this->si->scc_of(dst);

	    auto i = remap_[u].find(acc.id());
	    if (i != remap_[u].end())
	      acc = i->second;
	    else
	      acc = bddfalse;
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

      {
	bdd all = aut->all_acceptance_conditions();
	bdd neg = aut->neg_acceptance_conditions();
	filtered->set_acceptance_conditions(filter.accsets(all, neg).first);
      }
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
	      bdd acc;
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
    bool sb = aut->get_bprop(tgba_digraph::StateBasedAcc);
    auto res = scc_filter_apply<state_filter<>>(aut, given_si);
    if (sb)
      res->set_bprop(tgba_digraph::StateBasedAcc);
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
    return res;
  }

}
