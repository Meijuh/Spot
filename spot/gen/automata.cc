// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Developpement de
// l'EPITA (LRDE).
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

#include <spot/twa/twagraph.hh>
#include <spot/gen/automata.hh>
#include <spot/tl/parse.hh>

namespace spot
{
  namespace gen
  {
    namespace
    {
      static twa_graph_ptr
      ks_cobuchi(unsigned n)
      {
        if (n == 0)
          throw std::runtime_error("ks_cobuchi expects a positive argument");
        // the alphabet has four letters:
        // i, s (for sigma), p (for pi), h (for hash)
        // we encode this four letters alphabet thanks to two AP a and b
        // the exact encoding is not important
        // each letter is a permutation of the set {1..2n}
        // s = (1 2 .. 2n) the rotation
        // p = (1 2) the swap of the first two elements
        // i is the identity
        // d is the identity on {2..2n} but is undefined on 1

        // the automaton has 2n+1 states, numbered from 0 to 2n
        // 0 is the initial state and the only non-deterministic state

        auto dict = make_bdd_dict();
        auto aut = make_twa_graph(dict);

        // register aps
        bdd a = bdd_ithvar(aut->register_ap("a"));
        bdd b = bdd_ithvar(aut->register_ap("b"));

        // name the four letters
        bdd i = a & b;
        bdd s = a & (!b);
        bdd p = (!a) & b;
        bdd h = (!a) & (!b);

        // actually build the automaton
        aut->new_states(2*n+1);
        aut->set_init_state(0);
        aut->set_acceptance(1, acc_cond::acc_code::cobuchi());

        // from 0, we can non-deterministically jump to any state
        // (except 0) with any letter.
        for (unsigned q = 1; q <= 2*n; ++q)
          aut->new_edge(0, q, bddtrue, {0});
        // i is the identity
        for (unsigned q = 1; q <= 2*n; ++q)
          aut->new_edge(q, q, i);
        // p swaps 1 and 2, and leaves all other states invariant
        aut->new_edge(1, 2, p);
        aut->new_edge(2, 1, p);
        for (unsigned q = 3; q <= 2*n; ++q)
          aut->new_edge(q, q, p);
        // s does to next state (mod 2*n, 0 excluded)
        aut->new_edge(2*n, 1, s);
        for (unsigned q = 1; q < 2*n; ++q)
          aut->new_edge(q, q+1, s);
        // h is the same as i, except on 1 where it goes back to the
        // initial state
        aut->new_edge(1, 0, h);
        for (unsigned q = 2; q <= 2*n; ++q)
          aut->new_edge(q, q, h);

        aut->merge_edges();
        aut->prop_state_acc(true);
        return aut;
      }
    }

    twa_graph_ptr aut_pattern(aut_pattern_id pattern, int n)
    {
      if (n < 0)
        {
          std::ostringstream err;
          err << "pattern argument for " << aut_pattern_name(pattern)
              << " should be positive";
          throw std::runtime_error(err.str());
        }

      switch (pattern)
        {
          // Keep this alphabetically-ordered!
        case AUT_KS_COBUCHI:
          return ks_cobuchi(n);
        case AUT_END:
          break;
        }
      throw std::runtime_error("unsupported pattern");
    }

    const char* aut_pattern_name(aut_pattern_id pattern)
    {
      static const char* const class_name[] =
        {
          "ks-cobuchi",
        };
      // Make sure we do not forget to update the above table every
      // time a new pattern is added.
      static_assert(sizeof(class_name)/sizeof(*class_name)
                    == AUT_END - AUT_BEGIN, "size mismatch");
      if (pattern < AUT_BEGIN || pattern >= AUT_END)
        throw std::runtime_error("unsupported pattern");
      return class_name[pattern - AUT_BEGIN];
    }
  }
}
