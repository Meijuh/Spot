// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2010, 2011, 2012, 2013 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
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
#include "tgba/tgbaexplicit.hh"
#include "reachiter.hh"
#include "tgbaalgos/scc.hh"

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
		  const std::vector<unsigned>& max_table,
		  bool remove_all_useless)
	: tgba_reachable_iterator_depth_first(a),
	  out_(new T(a->get_dict())),
	  sm_(sm),
	  useless_(useless),
	  max_num_(max_num),
	  all_(remove_all_useless),
	  acc_(max_num)
      {
	acc_[0] = bddfalse;
	bdd tmp = a->all_acceptance_conditions();
	bdd_dict* d = a->get_dict();
	assert(a->number_of_acceptance_conditions() >= max_num_ - 1);
	if (tmp != bddfalse)
	  {
	    for (unsigned n = max_num_ - 1; n > 0; --n)
	      {
		assert(tmp != bddfalse);
		const ltl::formula* a = d->oneacc_to_formula(bdd_var(tmp));
		out_->declare_acceptance_condition(a->clone());
		tmp = bdd_low(tmp);
	      }
	    tmp = a->all_acceptance_conditions();
	    for (unsigned n = max_num_ - 1; n > 0; --n)
	      {
		const ltl::formula* a = d->oneacc_to_formula(bdd_var(tmp));
		acc_[n] = out_->get_acceptance_condition(a->clone());
		tmp = bdd_low(tmp);
	      }
	  }
	else
	  {
	    assert(max_num_ == 1);
	  }

	unsigned c = sm.scc_count();
	remap_.resize(c);
	bdd all_orig_neg = aut_->neg_acceptance_conditions();
	bdd all_sup = bdd_support(all_orig_neg);

	for (unsigned n = 0; n < c; ++n)
	  {
	    if (!sm.accepting(n))
	      continue;

	    bdd missingacc = bddfalse;
	    for (unsigned a = max_table[n]; a < max_num_; ++a)
	      missingacc |= acc_[a];

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
		if (res != bddfalse)
		  res |= missingacc;
		int id = resacc.id();
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
	    t->acceptance_conditions = remap_[u][acc.id()];
	  }
      }

    protected:
      T* out_;
      const scc_map& sm_;
      const std::vector<bool>& useless_;
      unsigned max_num_;
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
		       const std::vector<unsigned>& max_table,
		       bool remove_all_useless,
		       bdd susp_pos, bool early_susp, bdd ignored)
	: super(a, sm, useless, remap_table, max_num, max_table,
		remove_all_useless),
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
	    t->acceptance_conditions = this->remap_[u][acc.id()];
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
    unsigned max_num = 1;

    for (unsigned n = 0; n < ss.scc_total; ++n)
      {
	if (!sm->accepting(n))
	  continue;
	bdd all = sm->useful_acc_of(n);
	bdd negall = aut->neg_acceptance_conditions();

	// Compute a set of useless acceptance conditions.
	// If the acceptance combinations occurring in
	// the automata are  { a, ab, abc, bd }, then
	// ALL contains (a&!b&!c&!d)|(a&b&!c&!d)|(a&b&c&!d)|(!a&b&!c&d)
	// and we want to find that 'a' and 'b' are useless because
	// they always occur with 'c'.
	// The way we check if 'a' is useless is to look whether ALL
	// implies (x -> a) for some other acceptance condition x.
	bdd allconds = bdd_support(negall);
	bdd allcondscopy = allconds;
	bdd useless = bddtrue;
	while (allconds != bddtrue)
	  {
	    // Speed-up the computation of implied acceptance by
	    // removing those that are always present.  We detect
	    // those that appear as conjunction of positive variables
	    // at the start of ALL.
	    bdd prefix = bdd_satprefix(all);
	    if (prefix != bddtrue)
	      {
		assert(prefix == bdd_support(prefix));
		allcondscopy = bdd_exist(allcondscopy, prefix);
		if (allcondscopy != bddtrue)
		  {
		    useless &= prefix;
		  }
		else
		  {
		    // Never erase all conditions: at least keep one.
		    useless &= bdd_high(prefix);
		    break;
		  }
		allconds = bdd_exist(allconds, prefix);
	      }

	    // Pick a non-useless acceptance condition a.
	    bdd a = bdd_ithvar(bdd_var(allconds));
	    // For all acceptance condition x that is not already useless...
	    bdd others = allcondscopy;
	    while (others != bddtrue)
	      {
		bdd x = bdd_ithvar(bdd_var(others));
		// ... check whether it always implies a.
		if (x != a && bdd_implies(all, x >> a))
		  {
		    // If so, a is useless.
		    all = bdd_exist(all, a);
		    useless &= a;
		    allcondscopy = bdd_exist(allcondscopy, a);
		    break;
		  }
		others = bdd_high(others);
	      }
	    allconds = bdd_high(allconds);
	  }

	// We never remove ALL acceptance marks.
	assert(negall == bddtrue || useless != bdd_support(negall));

	bdd useful = bdd_exist(negall, useless);

	// Go over all useful sets of acceptance marks, and give them
	// a number.
	unsigned num = 1;
	// First compute the number of acceptance conditions used.
	for (BDD c = useful.id(); c != 1; c = bdd_low(c))
	  ++num;
	max_table[n] = num;
	if (num > max_num)
	  max_num = num;
	// Then number all of these acceptance conditions in the
	// reverse order.  This makes sure that the associated number
	// varies in the same direction as the bdd variables, which in
	// turn makes sure we preserve the acceptance condition
	// ordering (which matters for degeneralization).
	for (BDD c = useful.id(); c != 1; c = bdd_low(c))
	  remap_table[n].insert(std::make_pair(bdd_var(c), --num));
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
						  max_table,
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
						       max_table,
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
						 max_table,
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
						     max_table,
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
							  max_table,
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

}
