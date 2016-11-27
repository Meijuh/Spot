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

#pragma once

#include <spot/twa/twagraph.hh>
#include <utility>

namespace spot
{
  /// \brief Helper class combine outgoing edges in alternating
  /// automata
  ///
  /// The idea is that you can the operator() on some state to get an
  /// BDD representation of its outgoing edges (labels and
  /// destinations, but not acceptance marks).  The BDD representation
  /// of different states can combined using & or | to build a new
  /// representation of some outgoing edges that can be attached to
  /// some state with new_dests.  The use of BDDs helps removing
  /// superfluous edges.
  ///
  /// Beware that new_dests() just *appends* the transitions to the
  /// supplied state, it does not remove existing ones.
  ///
  /// operator() can be called on states with universal branching
  /// (that's actually the point), and can be called on state number
  /// that designate groupes of destination states (in that case the
  /// conjunction of all those states are taken).
  class SPOT_API outedge_combiner
  {
  private:
    const twa_graph_ptr& aut_;
    std::map<unsigned, int> state_to_var;
    std::map<int, unsigned> var_to_state;
    bdd vars_;
  public:
    outedge_combiner(const twa_graph_ptr& aut);
    ~outedge_combiner();
    bdd operator()(unsigned st);
    void new_dests(unsigned st, bdd out) const;
  };

  /// @{
  /// \brief Combine two states in a conjunction.
  ///
  /// This creates a new state whose outgoing transitions are the
  /// conjunctions of the compatible transitions of s1 and s2.
  ///
  /// Acceptance marks are dropped.
  ///
  /// The results is very likely to be alternating.
  template<class I>
  SPOT_API
  unsigned states_and(const twa_graph_ptr& aut, I begin, I end)
  {
    if (begin == end)
      throw std::runtime_error
        ("state_and() expects an non-empty list of states");
    outedge_combiner combiner(aut);
    bdd combination = bddtrue;
    while (begin != end)
      combination &= combiner(*begin++);
    unsigned new_s = aut->new_state();
    combiner.new_dests(new_s, combination);
    return new_s;
  }

  template<class T>
  SPOT_API
  unsigned states_and(const twa_graph_ptr& aut,
                      const std::initializer_list<T>& il)
  {
    return states_and(aut, il.begin(), il.end());
  }
  /// @}




}
