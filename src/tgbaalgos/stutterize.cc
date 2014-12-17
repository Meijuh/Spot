// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
// Copyright (C) 2004, 2005 Laboratoire d'Informatique de Paris 6 (LIP6),
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

#include "stutterize.hh"
#include "tgba/tgba.hh"
#include "dupexp.hh"
#include "misc/hash.hh"
#include "misc/hashfunc.hh"
#include "ltlvisit/apcollect.hh"
#include <deque>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace spot
{
  namespace
  {
    typedef std::pair<unsigned, bdd> stutter_state;

    struct stutter_state_hash
    {
      size_t
      operator()(const stutter_state& s) const
      {
	return wang32_hash(s.first) ^ wang32_hash(s.second.id());
      }
    };

    // Associate the stutter state to its number.
    typedef std::unordered_map<stutter_state, unsigned,
			       stutter_state_hash> ss2num_map;

    // Queue of state to be processed.
    typedef std::deque<stutter_state> queue_t;
  }

  static bdd
  get_all_ap(const const_tgba_digraph_ptr& a)
  {
    bdd res = bddtrue;
    for (auto& i: a->transitions())
      res &= bdd_support(i.cond);
    return res;
  }

  tgba_digraph_ptr
  sl(const const_tgba_digraph_ptr& a, const ltl::formula* f)
  {
    bdd aps = f
      ? atomic_prop_collect_as_bdd(f, a)
      : get_all_ap(a);
    return sl(a, aps);
  }

  tgba_digraph_ptr
  sl2(const const_tgba_digraph_ptr& a, const ltl::formula* f)
  {
    bdd aps = f
      ? atomic_prop_collect_as_bdd(f, a)
      : get_all_ap(a);
    return sl2(a, aps);
  }

  tgba_digraph_ptr
  sl(const const_tgba_digraph_ptr& a, bdd atomic_propositions)
  {
    // The result automaton uses numbered states.
    tgba_digraph_ptr res = make_tgba_digraph(a->get_dict());
    // We use the same BDD variables as the input.
    res->copy_ap_of(a);
    res->copy_acceptance_conditions_of(a);
    // These maps make it possible to convert stutter_state to number
    // and vice-versa.
    ss2num_map ss2num;

    queue_t todo;

    unsigned s0 = a->get_init_state_number();
    stutter_state s(s0, bddfalse);
    ss2num[s] = 0;
    res->new_state();
    todo.push_back(s);

    while (!todo.empty())
      {
	s = todo.front();
	todo.pop_front();
	unsigned src = ss2num[s];

	bool self_loop_needed = true;

	for (auto& t : a->out(s.first))
	  {
	    bdd all = t.cond;
	    while (all != bddfalse)
	      {
		bdd one = bdd_satoneset(all, atomic_propositions, bddtrue);
		all -= one;

		stutter_state d(t.dst, one);

		auto r = ss2num.emplace(d, ss2num.size());
		unsigned dest = r.first->second;

		if (r.second)
		  {
		    todo.push_back(d);
		    unsigned u = res->new_state();
		    assert(u == dest);
		    (void)u;
		  }

		// Create the transition.
		res->new_transition(src, dest, one, t.acc);

		if (src == dest)
		  self_loop_needed = false;
	      }
	  }

	if (self_loop_needed && s.second != bddfalse)
	  res->new_transition(src, src, s.second, 0U);
      }
    res->merge_transitions();
    return res;
  }

  tgba_digraph_ptr
  sl2(tgba_digraph_ptr&& a, bdd atomic_propositions)
  {
    if (atomic_propositions == bddfalse)
      atomic_propositions = get_all_ap(a);
    unsigned num_states = a->num_states();
    unsigned num_transitions = a->num_transitions();
    for (unsigned state = 0; state < num_states; ++state)
      {
	auto trans = a->out(state);

	for (auto it = trans.begin(); it != trans.end()
             && it.trans() <= num_transitions; ++it)
	  {
	    if (it->dst != state)
	      {
		bdd all = it->cond;
		while (all != bddfalse)
		  {
		    unsigned dst = it->dst;
		    bdd one = bdd_satoneset(all, atomic_propositions, bddtrue);
		    unsigned tmp = a->new_state();
		    unsigned i = a->new_transition(state, tmp, one,
					it->acc);
                    assert(i > num_transitions);
		    i = a->new_transition(tmp, tmp, one, 0U);
                    assert(i > num_transitions);
		    i = a->new_transition(tmp, dst, one,
					it->acc);
                    assert(i > num_transitions);
		    all -= one;
		  }
	      }
	  }
      }
    a->merge_transitions();
    return a;
  }

  tgba_digraph_ptr
  sl2(const const_tgba_digraph_ptr& a, bdd atomic_propositions)
  {
    return sl2(make_tgba_digraph(a), atomic_propositions);
  }
}
