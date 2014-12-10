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

  struct transition
  {
    unsigned src;
    unsigned dst;
    int cond;
    spot::acc_cond::mark_t acc;


    transition(unsigned src, unsigned dst, int cond, spot::acc_cond::mark_t acc)
      : src(src), dst(dst), cond(cond), acc(acc)
    {
    }

    bool operator==(const transition& o) const
    {
      return src == o.src && dst == o.dst && cond == o.cond && acc == o.acc;
    }
  };

  static bool
  trans_lessthan(const transition& ts1, const transition& ts2)
  {
    return
      ts1.src != ts2.src ?
        ts1.src < ts2.src :
      ts1.dst != ts2.dst ?
        ts1.dst < ts2.dst :
      ts1.acc != ts2.acc ?
        ts1.acc < ts2.acc :
      ts1.cond < ts2.cond;
  }

  static state2class_t
  map_state_class(const spot::const_tgba_digraph_ptr a)
  {
    state2class_t hashin(a->num_states(), 0);
    state2class_t hashout(a->num_states(), 0);
    state2class_t state2class(a->num_states());

    for (auto& t: a->transitions())
      {
        hashout[t.src] ^= spot::wang32_hash(t.cond.id());
        hashout[t.src] ^= spot::wang32_hash(t.acc);
        hashin[t.dst] ^= spot::wang32_hash(t.cond.id());
        hashin[t.dst] ^= spot::wang32_hash(t.acc);
      }

    for (unsigned i = 0; i < a->num_states(); ++i)
      // Rehash the ingoing transitions so that the total hash differs for
      // different (in, out) pairs of ingoing and outgoing transitions, even if
      // the union of in and out is the same.
      state2class[i] = spot::wang32_hash(hashin[i]) ^ hashout[i];

    // XOR the initial state's hash with a pseudo random value so that it is
    // in its own class.
    state2class[a->get_init_state_number()] ^= 2654435761U;
    return state2class;
  }

  static class2states_t
  map_class_states(const spot::const_tgba_digraph_ptr a)
  {
    unsigned n = a->num_states();
    std::vector<states_t> res;
    class2states_t class2states;
    auto state2class = map_state_class(a);

    for (unsigned s = 0; s < n; ++s)
      {
        class_t c1 = state2class[s];
        auto& states =
          class2states.emplace(c1, std::vector<unsigned>()).first->second;
        states.emplace_back(s);
      }

    return class2states;
  }

  static bool
  mapping_from_classes(std::vector<unsigned>& mapping,
                       class2states_t classes1,
                       class2states_t classes2)
  {
    if (classes1.size() != classes2.size())
      return false;
    for (auto& p : classes1)
      {
	auto& c2 = classes2[p.first];
        if (p.second.size() != c2.size())
          return false;
	auto ps = p.second.size();
        for (unsigned j = 0; j < ps; ++j)
          mapping[p.second[j]] = c2[j];
      }
    return true;
  }

  static bool
  next_class_permutation(class2states_t& classes)
  {
    for (auto& p : classes)
      if (std::next_permutation(p.second.begin(), p.second.end()))
        return true;
    return false;
  }

  static bool
  is_isomorphism(const std::vector<unsigned>& mapping,
                  const spot::const_tgba_digraph_ptr a1,
                  const spot::const_tgba_digraph_ptr a2)
  {
    unsigned n = a1->num_states();
    assert(n == a2->num_states());
    unsigned tend = a1->num_transitions();
    assert(tend == a2->num_transitions());

    std::vector<transition> trans1;
    trans1.reserve(tend);
    std::vector<transition> trans2;
    trans2.reserve(tend);

    for (auto& t: a1->transitions())
      trans1.emplace_back(mapping[t.src], mapping[t.dst], t.acc, t.cond.id());

    for (auto& t: a2->transitions())
      trans2.emplace_back(t.src, t.dst, t.acc, t.cond.id());

    // Sort the vectors of transitions so that they can be compared.
    std::sort(trans1.begin(), trans1.end(), trans_lessthan);
    std::sort(trans2.begin(), trans2.end(), trans_lessthan);
    return trans1 == trans2;
  }

  static bool
  are_trivially_different(const spot::const_tgba_digraph_ptr a1,
                          const spot::const_tgba_digraph_ptr a2)
  {
    return (a1->num_states() != a2->num_states()
	    || a1->num_transitions() != a2->num_transitions()
	    || a1->acc().num_sets() != a2->acc().num_sets());
  }
}

namespace spot
{
  std::vector<unsigned>
  are_isomorphic(const const_tgba_digraph_ptr a1,
                 const const_tgba_digraph_ptr a2)
  {
    if (are_trivially_different(a1, a2))
      return {};
    unsigned n = a1->num_states();
    assert(n == a2->num_states());
    class2states_t a1_classes = map_class_states(a1);
    class2states_t a2_classes = map_class_states(a2);
    std::vector<unsigned> mapping(n);

    // Get the first possible mapping between a1 and a2, or return false if
    // the number of class or the size of the classes do not match.
    if (!(mapping_from_classes(mapping, a1_classes, a2_classes)))
      return {};

    while (!is_isomorphism(mapping, a1, a2))
      {
        if (!next_class_permutation(a2_classes))
          return {};
        mapping_from_classes(mapping, a1_classes, a2_classes);
      }
    return mapping;
  }
}
