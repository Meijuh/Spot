// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2004, 2005  Laboratoire d'Informatique de Paris 6 (LIP6),
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

#include "tgba/tgbagraph.hh"
#include "tgbaalgos/are_isomorphic.hh"
#include <unordered_map>
#include <vector>
#include <algorithm>
#include "misc/hashfunc.hh"

namespace
{
  typedef size_t class_t;
  typedef std::vector<unsigned> states_t;
  typedef std::unordered_map<class_t, states_t> class2states_t;
  typedef std::vector<class_t> state2class_t;
  typedef spot::tgba_digraph::graph_t::trans_storage_t trans_storage_t;

  bool
  trans_lessthan(trans_storage_t ts1, trans_storage_t ts2)
  {
    return
      ts1.src != ts2.src ?
        ts1.src < ts2.src :
      ts1.dst != ts2.dst ?
        ts1.dst < ts2.dst :
      ts1.acc != ts2.acc ?
        ts1.acc < ts2.acc :
      ts1.cond.id() < ts2.cond.id();
  }

  std::function<bool(trans_storage_t ts1, trans_storage_t ts2)>
  trans_lessthan_mapped(const std::vector<unsigned>& mapping)
  {
    return [mapping](trans_storage_t ts1,
                     trans_storage_t ts2)
      {
        return
          mapping[ts1.src] != mapping[ts2.src] ?
            mapping[ts1.src] < mapping[ts2.src] :
          mapping[ts1.dst] != mapping[ts2.dst] ?
            mapping[ts1.dst] < mapping[ts2.dst] :
          ts1.acc != ts2.acc ?
            ts1.acc < ts2.acc :
          ts1.cond.id() < ts2.cond.id();
      };
  }

  state2class_t
  map_state_class(const spot::const_tgba_digraph_ptr a)
  {
    state2class_t hashin(a->num_states(), 0);
    state2class_t hashout(a->num_states(), 0);
    state2class_t state2class(a->num_states());

    for (auto& t: a->transitions())
      {
        if (!a->is_dead_transition(t))
          {
            hashout[t.src] ^= spot::wang32_hash(t.cond.id());
            hashout[t.src] ^= spot::wang32_hash(t.acc);
            hashin[t.dst] ^= spot::wang32_hash(t.cond.id());
            hashin[t.dst] ^= spot::wang32_hash(t.acc);
          }
      }

    for (unsigned i = 0; i < a->num_states(); ++i)
      // Rehash the ingoing transitions so that the total hash differs for
      // different (in, out) pairs of ingoing and outgoing transitions, even if
      // the union of in and out is the same.
      state2class[i] = spot::wang32_hash(hashin[i]) ^ hashout[i];

    return state2class;
  }

  class2states_t
  map_class_states(const spot::const_tgba_digraph_ptr a)
  {
    unsigned n = a->num_states();
    std::vector<states_t> res;
    class2states_t class2states;
    auto state2class = map_state_class(a);

    for (unsigned s = 0; s < n; ++s)
      {
        class_t c1 = state2class[s];
        (*(class2states.emplace(c1, std::vector<unsigned>()).first)).second.
          emplace_back(s);
      }

    return class2states;
  }

  bool
  mapping_from_classes(std::vector<unsigned>& mapping,
                       class2states_t classes1,
                       class2states_t classes2)
  {
    if (classes1.size() != classes2.size())
      return false;
    for (auto& p : classes1)
      {
        if (p.second.size() != classes2[p.first].size())
          return false;
        for (unsigned j = 0; j < p.second.size(); ++j)
          mapping[p.second[j]] = classes2[p.first][j];
      }
    return true;
  }

  bool
  next_class_permutation(class2states_t& classes)
  {
    for (auto& p : classes)
      if (std::next_permutation(p.second.begin(), p.second.end()))
        return true;
    return false;
  }

  bool
  is_isomorphism(const std::vector<unsigned>& mapping,
                  const spot::const_tgba_digraph_ptr a1,
                  const spot::const_tgba_digraph_ptr a2)
  {
    unsigned n = a1->num_states();
    assert(n == a2->num_states());
    std::vector<trans_storage_t> trans1;
    std::vector<trans_storage_t> trans2;

    for (auto& t: a1->transitions())
      if (!(a1->is_dead_transition(t)))
        trans1.push_back(t);

    for (auto& t: a2->transitions())
      if (!(a2->is_dead_transition(t)))
        trans2.push_back(t);

    // Sort the vectors of transitions so that they can be compared.
    // To use the same metric, the transitions of a1 have to be mapped to
    // a2.
    std::sort(trans1.begin(), trans1.end(), trans_lessthan_mapped(mapping));
    std::sort(trans2.begin(), trans2.end(), trans_lessthan);

    for (unsigned i = 0; i < trans1.size(); ++i)
      {
        auto ts1 = trans1[i];
        auto ts2 = trans2[i];
        if (!(ts2.src == mapping[ts1.src] &&
              ts2.dst == mapping[ts1.dst] &&
              ts1.acc == ts2.acc &&
              ts1.cond.id() == ts2.cond.id()))
          {
            return false;
          }
      }

    return true;
  }

  bool
  are_trivially_different(const spot::const_tgba_digraph_ptr a1,
                          const spot::const_tgba_digraph_ptr a2)
  {
    return (a1->num_states() != a2->num_states() ||
            a1->num_transitions() != a2->num_transitions());
  }
}

namespace spot
{
  std::vector<unsigned>
  are_isomorphic(const const_tgba_digraph_ptr a1,
                 const const_tgba_digraph_ptr a2)
  {
    if (are_trivially_different(a1, a2))
      return std::vector<unsigned>();
    unsigned n = a1->num_states();
    assert(n == a2->num_states());
    class2states_t a1_classes = map_class_states(a1);
    class2states_t a2_classes = map_class_states(a2);
    std::vector<unsigned> mapping(n);

    // Get the first possible mapping between a1 and a2, or return false if
    // the number of class or the size of the classes do not match.
    if (!(mapping_from_classes(mapping, a1_classes, a2_classes)))
      return std::vector<unsigned>();

    while (!is_isomorphism(mapping, a1, a2))
      {
        if (!next_class_permutation(a2_classes))
          return std::vector<unsigned>();
        mapping_from_classes(mapping, a1_classes, a2_classes);
      }
    return mapping;
  }
}
