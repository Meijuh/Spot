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

#include "tgba/tgbaexplicit.hh"
#include "sccfilter.hh"
#include "reachiter.hh"
#include "tgbaalgos/scc.hh"
#include "tgbaalgos/sccinfo.hh"

namespace spot
{
  namespace
  {
    // BDD.id -> Acc number
    typedef std::map<int, unsigned> accremap_t;
    typedef std::vector<accremap_t> remap_table_t;

    static
    state_explicit_number::transition*
    create_transition(const tgba*, tgba_explicit_number* out_aut,
		      const state*, int in, const state*, int out)
    {
      return out_aut->create_transition(in, out);
    }

    static
    state_explicit_string::transition*
    create_transition(const tgba* aut, tgba_explicit_string* out_aut,
		      const state* in_s, int, const state* out_s, int)
    {
      const tgba_explicit_string* a =
	static_cast<const tgba_explicit_string*>(aut);
      return out_aut->create_transition(a->get_label(in_s),
					a->get_label(out_s));
    }

    static
    state_explicit_formula::transition*
    create_transition(const tgba* aut, tgba_explicit_formula* out_aut,
		      const state* in_s, int, const state* out_s, int)
    {
      const tgba_explicit_formula* a =
	static_cast<const tgba_explicit_formula*>(aut);
      const ltl::formula* in_f = a->get_label(in_s);
      const ltl::formula* out_f = a->get_label(out_s);
      if (!out_aut->has_state(in_f))
	in_f->clone();
      if ((in_f != out_f) && !out_aut->has_state(out_f))
	out_f->clone();
      return out_aut->create_transition(in_f, out_f);
    }

    template<class T>
    class filter_iter_states: public tgba_reachable_iterator_depth_first
    {
    public:
      typedef T output_t;

      filter_iter_states(const tgba* a,
			 const scc_map& sm,
			 const std::vector<bool>& useless)
	: tgba_reachable_iterator_depth_first(a),
	  out_(new T(a->get_dict())),
	  sm_(sm),
	  useless_(useless)
      {
	a->get_dict()->register_all_variables_of(a, out_);
	out_->set_acceptance_conditions(a->all_acceptance_conditions());
      }

      T*
      result()
      {
	return out_;
      }

      bool
      want_state(const state* s) const
      {
	return !useless_[sm_.scc_of_state(s)];
      }

      void
      process_link(const state* in_s, int in,
		   const state* out_s, int out,
		   const tgba_succ_iterator* si)
      {
	typename output_t::state::transition* t =
	  create_transition(this->aut_, out_, in_s, in, out_s, out);
	t->condition = si->current_condition();
	t->acceptance_conditions = si->current_acceptance_conditions();
      }

    protected:
      T* out_;
      const scc_map& sm_;
      const std::vector<bool>& useless_;
    };

    template<class T>
    class filter_iter: public tgba_reachable_iterator_depth_first
    {
    public:
      typedef T output_t;
      typedef std::map<int, bdd> map_t;
      typedef std::vector<map_t> remap_t;

      filter_iter(const tgba* a,
		  const scc_map& sm,
		  const std::vector<bool>& useless,
		  remap_table_t& remap_table,
		  unsigned max_num,
		  bool remove_all_useless)
	: tgba_reachable_iterator_depth_first(a),
	  out_(new T(a->get_dict())),
	  sm_(sm),
	  useless_(useless),
	  all_(remove_all_useless),
	  acc_(max_num)
      {
	acc_[0] = bddfalse;
	bdd tmp = a->all_acceptance_conditions();
	bdd_dict* d = a->get_dict();
	assert(a->number_of_acceptance_conditions() >= max_num - 1);
	if (tmp != bddfalse)
	  {
	    for (unsigned n = max_num - 1; n > 0; --n)
	      {
		assert(tmp != bddfalse);
		const ltl::formula* a = d->oneacc_to_formula(bdd_var(tmp));
		out_->declare_acceptance_condition(a->clone());
		tmp = bdd_low(tmp);
	      }
	    tmp = a->all_acceptance_conditions();
	    for (unsigned n = max_num - 1; n > 0; --n)
	      {
		const ltl::formula* a = d->oneacc_to_formula(bdd_var(tmp));
		acc_[n] = out_->get_acceptance_condition(a->clone());
		tmp = bdd_low(tmp);
	      }
	  }
	else
	  {
	    assert(max_num == 1);
	  }

	unsigned c = sm.scc_count();
	remap_.resize(c);
	bdd all_orig_neg = aut_->neg_acceptance_conditions();
	bdd all_sup = bdd_support(all_orig_neg);

	for (unsigned n = 0; n < c; ++n)
	  {
	    //std::cerr << "SCC #" << n << '\n';
	    if (!sm.accepting(n))
	      continue;

	    bdd all = sm.useful_acc_of(n);
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
      }

      T*
      result()
      {
	return out_;
      }

      bool
      want_state(const state* s) const
      {
	return !useless_[sm_.scc_of_state(s)];
      }

      void
      process_link(const state* in_s, int in,
		   const state* out_s, int out,
		   const tgba_succ_iterator* si)
      {
	typename output_t::state::transition* t =
	  create_transition(this->aut_, out_, in_s, in, out_s, out);
	out_->add_conditions(t, si->current_condition());

	// Regardless of all_, do not output any acceptance condition
	// if the destination is not in an accepting SCC.
	//
	// If all_ is set, do not output any acceptance condition if the
	// source is not in the same SCC as dest.
	//
	// (See the documentation of scc_filter() for a rational.)
	unsigned u = sm_.scc_of_state(out_s);
	unsigned v = sm_.scc_of_state(in_s);
	if (sm_.accepting(u) && (!all_ || u == v))
	  {
	    bdd acc = si->current_acceptance_conditions();
	    if (acc == bddfalse)
	      return;
	    map_t::const_iterator i = this->remap_[u].find(acc.id());
	    if (i != this->remap_[u].end())
	      {
		t->acceptance_conditions = i->second;
	      }
	    else
	      {
		//t->acceptance_conditions = this->remap_[v][acc.id()];
	      }
	  }
      }

    protected:
      T* out_;
      const scc_map& sm_;
      const std::vector<bool>& useless_;
      bool all_;
      std::vector<bdd> acc_;
      remap_t remap_;
    };

    template<class T>
    class filter_iter_susp: public filter_iter<T>
    {
    public:
      typedef filter_iter<T> super;
      filter_iter_susp(const tgba* a,
		       const scc_map& sm,
		       const std::vector<bool>& useless,
		       remap_table_t& remap_table,
		       unsigned max_num,
		       bool remove_all_useless,
		       bdd susp_pos, bool early_susp, bdd ignored)
	: super(a, sm, useless, remap_table, max_num, remove_all_useless),
	  susp_pos(susp_pos), early_susp(early_susp), ignored(ignored)
      {
      }


      void
      process_link(const state* in_s, int in,
		   const state* out_s, int out,
		   const tgba_succ_iterator* si)
      {
	unsigned u = this->sm_.scc_of_state(out_s);
	unsigned v = this->sm_.scc_of_state(in_s);
	bool destacc = this->sm_.accepting(u);

	typename super::output_t::state::transition* t =
	  create_transition(this->aut_, this->out_, in_s, in, out_s, out);

	bdd cond = bdd_exist(si->current_condition(), ignored);
	// Remove suspended variables on transitions going to
	// non-accepting SCC, or on transition between SCC unless
	// early_susp is set.
	if (!destacc || (!early_susp && (u != this->sm_.scc_of_state(in_s))))
	  cond = bdd_exist(cond, susp_pos);

	this->out_->add_conditions(t, cond);

	// Regardless of all_, do not output any acceptance condition
	// if the destination is not in an accepting SCC.
	//
	// If all_ is set, do not output any acceptance condition if the
	// source is not in the same SCC as dest.
	//
	// (See the documentation of scc_filter() for a rational.)
	if (destacc && (!this->all_ || u == v))
	  {
	    bdd acc = si->current_acceptance_conditions();
	    if (acc == bddfalse)
	      return;
	    typename super::map_t::const_iterator i =
	      this->remap_[u].find(acc.id());
	    if (i != this->remap_[u].end())
	      {
		t->acceptance_conditions = i->second;
	      }
	    else
	      {
		// t->acceptance_conditions = this->remap_[v][acc.id()];
	      }
	  }
      }
    protected:
      bdd susp_pos;
      bool early_susp;
      bdd ignored;
    };

  } // anonymous


  tgba* scc_filter(const tgba* aut, bool remove_all_useless,
		   scc_map* given_sm, bdd susp, bool early_susp, bdd ignored)
  {
    scc_map* sm = given_sm;
    if (!sm)
      {
	sm = new scc_map(aut);
	sm->build_map();
      }
    scc_stats ss = build_scc_stats(*sm);

    remap_table_t remap_table(ss.scc_total);
    std::vector<unsigned> max_table(ss.scc_total);
    std::vector<bdd> useful_table(ss.scc_total);
    std::vector<bdd> useless_table(ss.scc_total);
    unsigned max_num = 1;

    for (unsigned n = 0; n < ss.scc_total; ++n)
      {
	if (!sm->accepting(n))
	  continue;
	bdd all = sm->useful_acc_of(n);
	bdd negall = aut->neg_acceptance_conditions();

	//std::cerr << "SCC #" << n << "; used = " << all << std::endl;

	// Compute a set of useless acceptance sets.
	// If the acceptance combinations occurring in
	// the automata are  { a, ab, abc, bd }, then
	// ALL contains (a&!b&!c&!d)|(a&b&!c&!d)|(a&b&c&!d)|(!a&b&!c&d)
	// and we want to find that 'a' and 'b' are useless because
	// they always occur with 'c'.
	// The way we check if 'a' is useless is to look whether ALL
	// implies (x -> a) for some other acceptance set x.
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
	bdd allconds_a = bdd_support(negall);
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
	assert(negall == bddtrue || useless != bdd_support(negall));

	useless_table[n] = useless;
	bdd useful = bdd_exist(negall, useless);

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

    // Now that we know about the max number of acceptance conditions,
    // use add extra acceptance conditions to those SCC that do not
    // have enough.
    for (unsigned n = 0; n < ss.scc_total; ++n)
      {
	if (!sm->accepting(n))
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
	  remap_table[n].insert(std::make_pair(bdd_var(c), --num));

	max_table[n] = max_num;
      }

    tgba* ret;
    // In most cases we will create a tgba_explicit_string copy of the
    // initial tgba, but this is not very space efficient as the
    // labels are built using the "format_state()" string output of
    // the original automaton.  In the case where the source automaton is
    // a tgba_explicit_formula (typically after calling ltl2tgba_fm())
    // we can create another tgba_explicit_formula instead.
    const tgba_explicit_formula* af =
      dynamic_cast<const tgba_explicit_formula*>(aut);
    if (af)
      {
	if (susp == bddtrue)
	  {
	    filter_iter<tgba_explicit_formula> fi(af, *sm,
						  ss.useless_scc_map,
						  remap_table, max_num,
						  remove_all_useless);
	    fi.run();
	    tgba_explicit_formula* res = fi.result();
	    res->merge_transitions();
	    ret = res;
	  }
	else
	  {
	    filter_iter_susp<tgba_explicit_formula> fi(af, *sm,
						       ss.useless_scc_map,
						       remap_table, max_num,
						       remove_all_useless,
						       susp, early_susp,
						       ignored);
	    fi.run();
	    tgba_explicit_formula* res = fi.result();
	    res->merge_transitions();
	    ret = res;
	  }
      }
    else
      {
	const tgba_explicit_string* as =
	  dynamic_cast<const tgba_explicit_string*>(aut);
	if (as)
	  {
	    filter_iter<tgba_explicit_string> fi(aut, *sm, ss.useless_scc_map,
						 remap_table, max_num,
						 remove_all_useless);
	    fi.run();
	    tgba_explicit_string* res = fi.result();
	    res->merge_transitions();
	    ret = res;
	  }
	else
	  {
	    if (susp == bddtrue)
	      {
		filter_iter<tgba_explicit_number> fi(aut, *sm,
						     ss.useless_scc_map,
						     remap_table, max_num,
						     remove_all_useless);
		fi.run();
		tgba_explicit_number* res = fi.result();
		res->merge_transitions();
		ret = res;
	      }
	    else
	      {
		filter_iter_susp<tgba_explicit_number> fi(aut, *sm,
							  ss.useless_scc_map,
							  remap_table, max_num,
							  remove_all_useless,
							  susp, early_susp,
							  ignored);
		fi.run();
		tgba_explicit_number* res = fi.result();
		res->merge_transitions();
		ret = res;
	      }
	  }
      }
    if (!given_sm)
      delete sm;
    return ret;
  }

  tgba* scc_filter_states(const tgba* aut, scc_map* given_sm)
  {
    const tgba_digraph* autg = dynamic_cast<const tgba_digraph*>(aut);
    if (autg && !given_sm)
      return scc_filter_states(autg, nullptr);

    scc_map* sm = given_sm;
    if (!sm)
      {
	sm = new scc_map(aut);
	sm->build_map();
      }
    scc_stats ss = build_scc_stats(*sm);

    tgba* ret;

    const tgba_explicit_formula* af =
      dynamic_cast<const tgba_explicit_formula*>(aut);
    if (af)
      {
	filter_iter_states<tgba_explicit_formula> fi(af, *sm,
						     ss.useless_scc_map);
	fi.run();
	tgba_explicit_formula* res = fi.result();
	res->merge_transitions();
	ret = res;
      }
    else
      {
	const tgba_explicit_string* as =
	  dynamic_cast<const tgba_explicit_string*>(aut);
	if (as)
	  {
	    filter_iter_states<tgba_explicit_string> fi(aut, *sm,
							ss.useless_scc_map);
	    fi.run();
	    tgba_explicit_string* res = fi.result();
	    res->merge_transitions();
	    ret = res;
	  }
	else
	  {
	    filter_iter_states<tgba_explicit_number> fi(aut, *sm,
							ss.useless_scc_map);
	    fi.run();
	    tgba_explicit_number* res = fi.result();
	    res->merge_transitions();
	    ret = res;
	  }
      }
    if (!given_sm)
      delete sm;
    return ret;
  }


  //////////////////////////////////////////////////////////////////////
  // The goal is to remove all the code above this line eventually, so
  // do not waste your time code common to both sides of this note.
  //////////////////////////////////////////////////////////////////////

  namespace
  {

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
    struct state_filter: id_filter
    {
      state_filter(scc_info* si)
	: id_filter(si)
      {
      }

      bool state(unsigned s)
      {
	return si->is_useful_state(s);
      }
    };

    // Remove acceptance conditions from all transitions outside of
    // non-accepting SCCs.
    struct acc_filter_all: id_filter
    {
      acc_filter_all(scc_info* si)
	: id_filter(si)
      {
      }

      filtered_trans trans(unsigned src, unsigned dst,
			   bdd cond, bdd acc)
      {
	unsigned u = si->scc_of(src);
	// If the transition is between two SCCs, or in a
	// non-accepting SCC.  Remove the acceptance sets.
	if (!si->is_accepting_scc(u) || u != si->scc_of(dst))
	  acc = bddfalse;

	return filtered_trans(true, cond, acc);
      }
    };

    // Remove acceptance conditions from all transitions whose
    // destination is not an accepting SCCs.
    struct acc_filter_some: id_filter
    {
      acc_filter_some(scc_info* si)
	: id_filter(si)
      {
      }

      filtered_trans trans(unsigned, unsigned dst,
			   bdd cond, bdd acc)
      {
	if (!si->is_accepting_scc(si->scc_of(dst)))
	  acc = bddfalse;
	return filtered_trans(true, cond, acc);
      }
    };

    //
    struct acc_filter_simplify: id_filter
    {
      std::vector<bdd> acc_;
      typedef std::map<int, bdd> map_t;
      typedef std::vector<map_t> remap_t;
      remap_t remap_;

      acc_filter_simplify(scc_info* si)
	: id_filter(si)
      {
      }

      acc_pair accsets(bdd in_all, bdd in_all_neg)
      {
	unsigned scc_count = si->scc_count();
	remap_table_t remap_table(scc_count);
	std::vector<unsigned> max_table(scc_count);
	std::vector<bdd> useful_table(scc_count);
	std::vector<bdd> useless_table(scc_count);
	unsigned max_num = 1;
	const tgba_digraph* aut = si->get_aut();

	std::vector<bdd> used_acc = si->used_acc();

	for (unsigned n = 0; n < scc_count; ++n)
	  {
	    if (!si->is_accepting_scc(n))
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
	    if (!si->is_accepting_scc(n))
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
	      remap_table[n].insert(std::make_pair(bdd_var(c), --num));

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
	    if (!si->is_accepting_scc(n))
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

      filtered_trans trans(unsigned src, unsigned, bdd cond, bdd acc)
      {
	if (acc != bddfalse)
	  {
	    unsigned u = si->scc_of(src);
	    auto i = remap_[u].find(acc.id());
	    if (i != remap_[u].end())
	      acc = i->second;
	    else
	      acc = bddfalse;
	  }
	return filtered_trans{true, cond, acc};
      }

    };


    template<typename F1, typename... F2>
    struct compose_filters
    {
      F1 f1;
      compose_filters<F2...> f2;

      compose_filters(scc_info* si)
	: f1(si), f2(si)
      {
      }

      bool state(unsigned s)
      {
	return f1.state(s) && f2.state(s);
      }

      acc_pair accsets(bdd all, bdd all_neg)
      {
	auto t = f1.accsets(all, all_neg);
	return f2.accsets(t.first, t.second);
      }

      filtered_trans trans(unsigned src, unsigned dst,
			   bdd cond, bdd acc)
      {
	auto res = f1.trans(src, dst, cond, acc);
	if (!std::get<0>(res))
	  return res;
	return f2.trans(src, dst, std::get<1>(res), std::get<2>(res));
      }
    };

    // If there is nothing to compose, use the filter as-is.
    template<typename F1>
    struct compose_filters<F1>: F1
    {
      compose_filters(scc_info* si)
	: F1(si)
      {
      }
    };

    template<class F>
    tgba_digraph* scc_filter_apply(const tgba_digraph* aut,
				   scc_info* given_si)
    {
      // Compute scc_info if not supplied.
      scc_info* si = given_si;
      if (!si)
	si = new scc_info(aut);

      F filter(si);

      // Renumber all useful states.
      unsigned in_n = aut->num_states(); // Number of input states.
      unsigned out_n = 0;		 // Number of output states.
      std::vector<unsigned> inout; // Associate old states to new ones.
      inout.reserve(in_n);
      for (unsigned i = 0; i < in_n; ++i)
	if (filter.state(i))
	  inout.push_back(out_n++);
	else
	  inout.push_back(-1U);

      bdd_dict* bd = aut->get_dict();
      tgba_digraph* filtered = new tgba_digraph(bd);
      bd->register_all_variables_of(aut, filtered);
      {
	bdd all = aut->all_acceptance_conditions();
	bdd neg = aut->neg_acceptance_conditions();
	filtered->set_acceptance_conditions(filter.accsets(all, neg).first);
      }
      const tgba_digraph::graph_t& ing = aut->get_graph();
      tgba_digraph::graph_t& outg = filtered->get_graph();
      outg.new_states(out_n);
      for (unsigned isrc = 0; isrc < in_n; ++isrc)
	{
	  unsigned osrc = inout[isrc];
	  if (osrc >= out_n)
	    continue;
	  for (auto& t: ing.out(isrc))
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
		outg.new_transition(osrc, odst, cond, acc);
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

  tgba_digraph*
  scc_filter_states(const tgba_digraph* aut, scc_info* given_si)
  {
    return scc_filter_apply<state_filter>(aut, given_si);
  }

  tgba_digraph*
  scc_filter(const tgba_digraph* aut, bool remove_all_useless,
	     scc_info* given_si)
  {
    if (remove_all_useless)
      return scc_filter_apply<compose_filters<state_filter,
					      acc_filter_all,
					      acc_filter_simplify>>
	(aut, given_si);
    else
      return scc_filter_apply<compose_filters<state_filter,
					      acc_filter_some,
					      acc_filter_simplify>>
	(aut, given_si);
  }

}
