// -*- coding: utf-8 -*-
// Copyright (C) 2016 Laboratoire de Recherche et Développement de
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

#include <spot/twaalgos/alternation.hh>
#include <algorithm>
#include <spot/misc/minato.hh>

namespace spot
{
  outedge_combiner::outedge_combiner(const twa_graph_ptr& aut)
    : aut_(aut), vars_(bddtrue)
  {
  }

  outedge_combiner::~outedge_combiner()
  {
    aut_->get_dict()->unregister_all_my_variables(this);
  }

  bdd outedge_combiner::operator()(unsigned st)
  {
    const auto& dict = aut_->get_dict();
    bdd res = bddtrue;
    for (unsigned d1: aut_->univ_dests(st))
      {
        bdd res2 = bddfalse;
        for (auto& e: aut_->out(d1))
          {
            bdd out = bddtrue;
            for (unsigned d: aut_->univ_dests(e.dst))
              {
                auto p = state_to_var.emplace(d, 0);
                if (p.second)
                  {
                    int v = dict->register_anonymous_variables(1, this);
                    p.first->second = v;
                    var_to_state.emplace(v, d);
                    vars_ &= bdd_ithvar(v);
                  }
                out &= bdd_ithvar(p.first->second);
              }
            res2 |= e.cond & out;
          }
        res &= res2;
      }
    return res;
  }

  void outedge_combiner::new_dests(unsigned st, bdd out) const
  {
    minato_isop isop(out);
    bdd cube;
    std::vector<unsigned> univ_dest;
    while ((cube = isop.next()) != bddfalse)
      {
        bdd cond = bdd_exist(cube, vars_);
        bdd dest = bdd_existcomp(cube, vars_);
        while (dest != bddtrue)
          {
            assert(bdd_low(dest) == bddfalse);
            auto it = var_to_state.find(bdd_var(dest));
            assert(it != var_to_state.end());
            univ_dest.push_back(it->second);
            dest = bdd_high(dest);
          }
        std::sort(univ_dest.begin(), univ_dest.end());
        aut_->new_univ_edge(st, univ_dest.begin(), univ_dest.end(), cond);
        univ_dest.clear();
      }
  }

}
