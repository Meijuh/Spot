// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et
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

#include "misc/timer.hh"
#include "ltlast/atomic_prop.hh"
#include "tgbaalgos/dtgbacomp.hh"
#include "tgbaalgos/stutter_invariance.hh"
#include "tgbaalgos/randomgraph.hh"
#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/product.hh"
#include "tgbaalgos/stutterize.hh"
#include "tgbaalgos/closure.hh"
#include "tgba/tgbagraph.hh"
#include "tgba/bdddict.hh"
#include <cstdio>
#include <cstring>
#include <vector>

int
main()
{
  spot::bdd_dict_ptr dict = spot::make_bdd_dict();
  spot::tgba_digraph_ptr a;
  spot::tgba_digraph_ptr na;
  unsigned n = 10;
  for (unsigned states_n = 1; states_n <= 50; ++states_n)
    for (float d = 0; d <= 1; d += 0.1)
      {
        for (unsigned props_n = 1; props_n <= 4; ++props_n)
          {
            // random ap set
            auto ap = new spot::ltl::atomic_prop_set();
            spot::ltl::default_environment& e =
              spot::ltl::default_environment::instance();
            for (unsigned i = 1; i < props_n; ++i)
              {
                std::ostringstream p;
                p << 'p' << i;
                ap->insert(static_cast<const spot::ltl::atomic_prop*>
                           (e.require(p.str())));
              }

            // ap set as bdd
            bdd apdict = bddtrue;
            for (auto& i: *ap)
              apdict &= bdd_ithvar(dict->register_proposition(i, a));

            // generate n random automata
            typedef std::pair<spot::tgba_digraph_ptr, spot::tgba_digraph_ptr>
              aut_pair_t;
            std::vector<aut_pair_t> vec;
            for (unsigned i = 0; i < n; ++i)
              {
                a = spot::random_graph(states_n, d, ap, dict, 2, 0.1, 0.5,
                                       true);
                na = spot::dtgba_complement(a);
                vec.push_back(aut_pair_t(a, na));
              }

            for (char algo = '1'; algo <= '8'; ++algo)
              {
                // Set SPOT_STUTTER_CHECK environment variable.
                char algostr[2] = { 0 };
                algostr[0] = algo;
                setenv("SPOT_STUTTER_CHECK", algostr, true);

                // Copy vec, because is_stutter_invariant modifies the
                // automata.
                std::vector<aut_pair_t> dup(vec);
                spot::stopwatch sw;
                sw.start();
                bool res;
                for (auto& a: vec)
                  res = spot::is_stutter_invariant(std::move(a.first),
                                                   std::move(a.second),
                                                   apdict);
                const double time = sw.stop();

                vec = dup;
                std::cout << algo << ", " << props_n << ", " << states_n
                          << ", " << res << ", " << time << std::endl;
              }
            spot::ltl::destroy_atomic_prop_set(*ap);
            delete(ap);
          }
      }

  return 0;
}
