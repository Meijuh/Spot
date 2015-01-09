// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2010, 2011, 2013, 2014, 2015 Laboratoire de
// Recherche et Développement de l'Epita (LRDE).
// Copyright (C) 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include <set>
#include <deque>
#include <iterator>
#include <vector>
#include "powerset.hh"
#include "misc/hash.hh"
#include "tgbaalgos/powerset.hh"
#include "tgbaalgos/sccinfo.hh"
#include "tgbaalgos/cycles.hh"
#include "tgbaalgos/gtec/gtec.hh"
#include "tgbaalgos/product.hh"
#include "tgba/bddprint.hh"
#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/gtec/gtec.hh"
#include "tgbaalgos/sccfilter.hh"
#include "tgbaalgos/ltl2tgba_fm.hh"
#include "tgbaalgos/dtgbacomp.hh"
#include "ltlast/unop.hh"

namespace spot
{
  tgba_digraph_ptr
  tgba_powerset(const const_tgba_digraph_ptr& aut, power_map& pm, bool merge)
  {
    typedef power_map::power_state power_state;
    typedef std::map<power_map::power_state, int> power_set;
    typedef std::deque<power_map::power_state> todo_list;

    power_set seen;
    todo_list todo;
    auto res = make_tgba_digraph(aut->get_dict());
    res->copy_ap_of(aut);

    {
      power_state ps{aut->get_init_state_number()};
      todo.push_back(ps);
      unsigned num = res->new_state();
      seen[ps] = num;
      pm.map_[num] = ps;
    }

    while (!todo.empty())
      {
	power_state src = todo.front();
	todo.pop_front();
	// Compute all variables occurring on outgoing arcs.
	bdd all_vars = bddtrue;
	for (auto s: src)
	  for (auto i: aut->out(s))
	    all_vars &= bdd_support(i.cond);

	bdd all_conds = bddtrue;
	// Iterate over all possible conditions
	while (all_conds != bddfalse)
	  {
	    bdd cond = bdd_satoneset(all_conds, all_vars, bddtrue);
	    all_conds -= cond;

	    // Construct the set of all states reachable via COND.
	    power_state dest;
	    for (auto s: src)
	      for (auto si: aut->out(s))
		if ((cond >> si.cond) == bddtrue)
		  dest.insert(si.dst);
	    if (dest.empty())
	      continue;
	    // Add that transition.
	    auto i = seen.find(dest);
	    int dest_num;
	    if (i != seen.end())
	      {
		dest_num = i->second;
	      }
	    else
	      {
		dest_num = res->new_state();
		seen[dest] = dest_num;
		pm.map_[dest_num] = dest;
		todo.push_back(dest);
	      }
	    res->new_transition(seen[src], dest_num, cond);
	  }
      }
    if (merge)
      res->merge_transitions();
    return res;
  }

  tgba_digraph_ptr
  tgba_powerset(const const_tgba_digraph_ptr& aut)
  {
    power_map pm;
    return tgba_powerset(aut, pm);
  }


  namespace
  {

    class fix_scc_acceptance: protected enumerate_cycles
    {
    public:
      typedef dfs_stack::const_iterator cycle_iter;
      typedef tgba_graph_trans_data trans;
      typedef std::set<trans*> trans_set;
      typedef std::vector<trans_set> set_set;
    protected:
      const_tgba_digraph_ptr ref_;
      power_map& refmap_;
      trans_set reject_;	// set of rejecting transitions
      set_set accept_;		// set of cycles that are accepting
      trans_set all_;		// all non rejecting transitions
      unsigned threshold_;	// maximum count of enumerated cycles
      unsigned cycles_left_; 	// count of cycles left to explore

    public:
      fix_scc_acceptance(const scc_info& sm, const_tgba_digraph_ptr ref,
			 power_map& refmap, unsigned threshold)
	: enumerate_cycles(sm), ref_(ref), refmap_(refmap),
	  threshold_(threshold)
      {
      }

      bool fix_scc(const int m)
      {
	reject_.clear();
	accept_.clear();
	cycles_left_ = threshold_;
	run(m);

//	std::cerr << "SCC #" << m << '\n';
//	std::cerr << "REJECT: ";
//	print_set(std::cerr, reject_) << '\n';
//	std::cerr << "ALL: ";
//	print_set(std::cerr, all_) << '\n';
//	for (set_set::const_iterator j = accept_.begin();
//	     j != accept_.end(); ++j)
//	  {
//	    std::cerr << "ACCEPT: ";
//	    print_set(std::cerr, *j) << '\n';
//	  }

	auto acc = aut_->acc().all_sets();
	for (auto i: all_)
	  i->acc = acc;
	return threshold_ != 0 && cycles_left_ == 0;
      }

      bool is_cycle_accepting(cycle_iter begin, trans_set& ts) const
      {
	auto a = std::const_pointer_cast<tgba_digraph>(aut_);

	// Build an automaton representing this loop.
	auto loop_a = make_tgba_digraph(aut_->get_dict());
	int loop_size = std::distance(begin, dfs_.end());
	loop_a->new_states(loop_size);
	int n;
	cycle_iter i;
	for (n = 1, i = begin; n <= loop_size; ++n, ++i)
	  {
	    trans* t = &a->trans_data(i->succ);
	    loop_a->new_transition(n - 1, n % loop_size, t->cond);
	    if (reject_.find(t) == reject_.end())
	      ts.insert(t);
	  }
	assert(i == dfs_.end());

	unsigned loop_a_init = loop_a->get_init_state_number();
	assert(loop_a_init == 0);

	// Check if the loop is accepting in the original automaton.
	bool accepting = false;

	// Iterate on each original state corresponding to the
	// start of the loop in the determinized automaton.
	const power_map::power_state& ps =
	  refmap_.states_of(a->state_number(begin->ts->first));
	for (auto s: ps)
	  {
	    // Check the product between LOOP_A, and ORIG_A starting
	    // in S.
	    if (!product(loop_a, ref_, loop_a_init, s)->is_empty())
	      {
		accepting = true;
		break;
	      }
	  }
	return accepting;
      }

      std::ostream&
      print_set(std::ostream& o, const trans_set& s) const
      {
	o << "{ ";
	for (auto i: s)
	  o << i << ' ';
	o << '}';
	return o;
      }

      virtual bool
      cycle_found(const state* start)
      {
	cycle_iter i = dfs_.begin();
	while (i->ts->first != start)
	  ++i;
	trans_set ts;
	bool is_acc = is_cycle_accepting(i, ts);
	do
	  {
	    //	    std::cerr << aut_->format_state(i->ts->first) << ' ';
	    ++i;
	  }
	while (i != dfs_.end());
	//	std::cerr << "  acc=" << is_acc << "  (";
	//	bdd_print_accset(std::cerr, aut_->get_dict(), s) << ") ";
	//	print_set(std::cerr, ts) << '\n';
	if (is_acc)
	  {
	    accept_.push_back(ts);
	    all_.insert(ts.begin(), ts.end());
	  }
	else
	  {
	    for (auto t: ts)
	      {
		reject_.insert(t);
		for (auto& j: accept_)
		  j.erase(t);
		all_.erase(t);
	      }
	  }

	// Abort this algorithm if we have seen too much cycles, i.e.,
	// when cycle_left_ *reaches* 0.  (If cycle_left_ == 0, that
	// means we had no limit.)
	return (cycles_left_ == 0) || --cycles_left_;
      }
    };

    static bool
    fix_dba_acceptance(tgba_digraph_ptr det,
		       const_tgba_digraph_ptr ref, power_map& refmap,
		       unsigned threshold)
    {
      det->copy_acceptance_conditions_of(ref);

      scc_info sm(det);

      unsigned scc_count = sm.scc_count();

      fix_scc_acceptance fsa(sm, ref, refmap, threshold);

      for (unsigned m = 0; m < scc_count; ++m)
	if (!sm.is_trivial(m))
	  if (fsa.fix_scc(m))
	    return true;
      return false;
    }
  }

  tgba_digraph_ptr
  tba_determinize(const const_tgba_digraph_ptr& aut,
		  unsigned threshold_states, unsigned threshold_cycles)
  {
    power_map pm;
    // Do not merge transitions in the deterministic automaton.  If we
    // add two self-loops labeled by "a" and "!a", we do not want
    // these to be merged as "1" before the acceptance has been fixed.
    auto det = tgba_powerset(aut, pm, false);

    if ((threshold_states > 0)
	&& (pm.map_.size() > aut->num_states() * threshold_states))
      return nullptr;
    if (fix_dba_acceptance(det, aut, pm, threshold_cycles))
      return nullptr;
    det->merge_transitions();
    return det;
  }

  tgba_digraph_ptr
  tba_determinize_check(const tgba_digraph_ptr& aut,
			unsigned threshold_states,
			unsigned threshold_cycles,
			const ltl::formula* f,
			const_tgba_digraph_ptr neg_aut)
  {
    if (f == 0 && neg_aut == 0)
      return 0;
    if (aut->acc().num_sets() > 1)
      return 0;

    auto det = tba_determinize(aut, threshold_states, threshold_cycles);

    if (!det)
      return nullptr;

    if (neg_aut == nullptr)
      {
	const ltl::formula* neg_f =
	  ltl::unop::instance(ltl::unop::Not, f->clone());
	neg_aut = ltl_to_tgba_fm(neg_f, aut->get_dict());
	neg_f->destroy();

	// Remove useless SCCs.
	neg_aut = scc_filter(neg_aut, true);
      }

    if (product(det, neg_aut)->is_empty())
      // Complement the DBA.
      if (product(aut, dtgba_complement(det))->is_empty())
	// Finally, we are now sure that it was safe
	// to determinize the automaton.
	return det;

    return aut;
  }
}
