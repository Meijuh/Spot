// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2011, 2012, 2014, 2015, 2016 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
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

#include <spot/twaalgos/copy.hh>
#include <spot/twa/twagraph.hh>
#include <deque>

namespace spot
{
  twa_graph_ptr
  copy(const const_twa_ptr& aut, twa::prop_set p,
       bool preserve_names, unsigned max_states)
  {
    twa_graph_ptr out = make_twa_graph(aut->get_dict());
    out->copy_acceptance_of(aut);
    out->copy_ap_of(aut);
    out->prop_copy(aut, p);

    std::vector<std::string>* names = nullptr;
    std::set<unsigned>* incomplete = nullptr;

    // Old highlighting maps
    typedef std::map<unsigned, unsigned> hmap;
    hmap* ohstates = nullptr;
    hmap* ohedges = nullptr;
    const_twa_graph_ptr aut_g = nullptr;
    // New highlighting maps
    hmap* nhstates = nullptr;
    hmap* nhedges = nullptr;

    if (preserve_names)
      {
        names = new std::vector<std::string>;
        out->set_named_prop("state-names", names);

        // If the input is a twa_graph and we were asked to preserve
        // names, also preserve highlights.
        aut_g = std::dynamic_pointer_cast<const twa_graph>(aut);
        if (aut_g)
          {
            ohstates = aut->get_named_prop<hmap>("highlight-states");
            if (ohstates)
              nhstates = out->get_or_set_named_prop<hmap>("highlight-states");
            ohedges = aut->get_named_prop<hmap>("highlight-edges");
            if (ohedges)
              nhedges = out->get_or_set_named_prop<hmap>("highlight-edges");
          }
      }

    // States already seen.
    state_map<unsigned> seen;
    // States to process
    std::deque<state_map<unsigned>::const_iterator> todo;

    auto new_state = [&](const state* s) -> unsigned
      {
        auto p = seen.emplace(s, 0);
        if (p.second)
          {
            p.first->second = out->new_state();
            todo.emplace_back(p.first);
            if (names)
              names->emplace_back(aut->format_state(s));
            if (ohstates)
              {
                auto q = ohstates->find(aut_g->state_number(s));
                if (q != ohstates->end())
                  nhstates->emplace(p.first->second, q->second);
              }
          }
        else
          {
            s->destroy();
          }
        return p.first->second;
      };

    out->set_init_state(new_state(aut->get_init_state()));
    while (!todo.empty())
      {
        const state* src1;
        unsigned src2;
        std::tie(src1, src2) = *todo.front();
        todo.pop_front();
        for (auto* t: aut->succ(src1))
          {
            unsigned edgenum = 0;
            if (SPOT_UNLIKELY(max_states < out->num_states()))
              {
                // If we have reached the max number of state, never try
                // to create a new one.
                auto i = seen.find(t->dst());
                if (i == seen.end())
                  {
                    if (!incomplete)
                      incomplete = new std::set<unsigned>;
                    incomplete->insert(src2);
                    continue;
                  }
                edgenum = out->new_edge(src2, i->second, t->cond(), t->acc());
              }
            else
              {
                edgenum =
                  out->new_edge(src2, new_state(t->dst()), t->cond(), t->acc());
              }
            if (ohedges)
              {
                auto q = ohedges->find(aut_g->edge_number(t));
                if (q != ohedges->end())
                  nhedges->emplace(edgenum, q->second);
              }
          }
      }


    auto s = seen.begin();
    while (s != seen.end())
      {
        // Advance the iterator before deleting the "key" pointer.
        const state* ptr = s->first;
        ++s;
        ptr->destroy();
      }

    if (incomplete)
      out->set_named_prop("incomplete-states", incomplete);
    return out;
  }
}
