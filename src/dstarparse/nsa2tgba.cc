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

#include <sstream>
#include <deque>
#include "public.hh"
#include "tgbaalgos/sccfilter.hh"
#include "ltlenv/defaultenv.hh"
#include "priv/accmap.hh"

namespace spot
{
  // Christof Löding's Diploma Thesis: Methods for the
  // Transformation of ω-Automata: Complexity and Connection to
  // Second Order Logic.  Section 3.4.3, gives a transition
  // from Streett with |Q| states to BA with |Q|*(4^n-3^n+2)
  // states, if n is the number of acceptance pairs.
  //
  // Duret-Lutz et al. (ATVA'2009): On-the-fly Emptiness Check of
  // Transition-based Streett Automata.  Section 3.3 contains a
  // conversion from transition-based Streett Automata to TGBA using
  // the generalized Büchi acceptance to limit the explosion.  It goes
  // from Streett with |Q| states to (T)GBA with |Q|*(2^n+1) states.
  // However the definition of the number of acceptance sets in that
  // paper is suboptimal: only n are needed, not 2^n.
  //
  // This implements this second version.

  namespace
  {
    // A state in the resulting automaton corresponds is either a
    // state of the original automaton (in which case bv == 0) or a
    // state of the original automaton associated to a set of pending
    // acceptance represented by a bitvect.

    struct build_state
    {
      int s;
      const bitvect* pend;

      build_state(int st, const bitvect* bv = 0):
	s(st),
	pend(bv)
      {
      }
    };

    struct build_state_hash
    {
      size_t
      operator()(const build_state& s) const
      {
	if (!s.pend)
	  return s.s;
	else
	  return s.s ^ s.pend->hash();
      }
    };

    struct build_state_equal
    {
      bool
      operator()(const build_state& left,
                 const build_state& right) const
      {
	if (left.s != right.s)
	  return false;
	if (left.pend == right.pend)
	  return true;
	if (!right.pend || !left.pend)
	  return false;
        return *left.pend == *right.pend;
      }
    };

    // Associate the build state to its number.
    typedef std::unordered_map<build_state, int,
			       build_state_hash, build_state_equal> bs2num_map;

    // Queue of state to be processed.
    typedef std::deque<build_state> queue_t;

  }

  tgba_digraph_ptr nsa_to_tgba(const const_dstar_aut_ptr& nsa)
  {
    assert(nsa->type == Streett);
    auto a = nsa->aut;
    auto res = make_tgba_digraph(a->get_dict());
    res->copy_ap_of(a);

    // Create accpair_count acceptance sets for the output.
    unsigned npairs = nsa->accpair_count;
    acc_mapper_consecutive_int acc_b(res, npairs);

    // These maps make it possible to convert build_state to number
    // and vice-versa.
    bs2num_map bs2num;

    queue_t todo;

    build_state s(a->get_init_state_number());
    bs2num[s] = res->new_state();
    todo.push_back(s);

    while (!todo.empty())
      {
        s = todo.front();
        todo.pop_front();
        int src = bs2num[s];

	for (auto& t: a->out(s.s))
	  {
	    bitvect* pend = 0;
	    acc_cond::mark_t acc = 0U;
	    if (s.pend)
	      {
		pend = s.pend->clone();
		*pend |= nsa->accsets->at(2 * t.dst); // L
		*pend -= nsa->accsets->at(2 * t.dst + 1); // U

		for (size_t i = 0; i < npairs; ++i)
		  if (!pend->get(i))
		    acc |= acc_b.lookup(i).second;
	      }


	    build_state d(t.dst, pend);
            // Have we already seen this destination?
            int dest;
	    auto dres = bs2num.emplace(d, 0);
            if (!dres.second)
              {
                dest = dres.first->second;
		delete d.pend;
              }
            else		// No, this is a new state
              {
		dest = dres.first->second = res->new_state();
                todo.push_back(d);
	      }
	    res->new_transition(src, dest, t.cond, acc);

	    // Jump to level ∅
	    if (s.pend == 0)
	      {
		bitvect* pend = make_bitvect(npairs);
		build_state d(t.dst, pend);
		// Have we already seen this destination?
		int dest;
		auto dres = bs2num.emplace(d, 0);
		if (!dres.second)
		  {
		    dest = dres.first->second;
		    delete d.pend;
		  }
		else		// No, this is a new state
		  {
		    dest = dres.first->second = res->new_state();
		    todo.push_back(d);
		  }
		res->new_transition(src, dest, t.cond);
	      }
	  }
      }


    // {
    //   bs2num_map::iterator i = bs2num.begin();
    //   while (i != bs2num.end())
    // 	{
    // 	  std::cerr << i->second << ": (" << i->first.s << ',';
    // 	  if (i->first.pend)
    // 	    std::cerr << *i->first.pend << ")\n";
    // 	  else
    // 	    std::cerr << "-)\n";
    // 	  ++i;
    // 	}
    // }

    // Cleanup the bs2num map.
    bs2num_map::iterator i = bs2num.begin();
    while (i != bs2num.end())
      delete (i++)->first.pend;

    res->acc().set_generalized_buchi();
    return res;
  }

}
