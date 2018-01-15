// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et
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

#pragma once

#include <spot/misc/common.hh>
#include <spot/twa/fwd.hh>
#include <vector>
#include <utility>

namespace spot
{
  /// \brief Automata constructed by product() contain a property
  /// named "product-states" with this type
  typedef std::vector<std::pair<unsigned, unsigned>> product_states;

  /// \ingroup twa_algorithms
  /// \brief Intersect two automata using a synchronous product
  ///
  /// The resulting automaton will accept the intersection of both
  /// languages and have an acceptance condition that is the
  /// conjunction of the acceptance conditions of the two input
  /// automata.
  ///
  /// The algorithm also defines a named property called
  /// "product-states" with type spot::product_states.  This stores
  /// the pair of original state numbers associated to each state of
  /// the product.
  SPOT_API
  twa_graph_ptr product(const const_twa_graph_ptr& left,
                        const const_twa_graph_ptr& right);

  /// \ingroup twa_algorithms
  /// \brief Intersect two automata using a synchronous product
  ///
  /// These variant allow changing the initial state of both automata
  /// in case you want to start the product at a different place.
  ///
  /// The resulting automaton will accept the intersection of the
  /// languages recognized by each input automaton (with its initial
  /// state changed) and have an acceptance condition that is the
  /// conjunction of the acceptance conditions of the two input
  /// automata.
  ///
  /// The algorithm also defines a named property called
  /// "product-states" with type spot::product_states.  This stores
  /// the pair of original state numbers associated to each state of
  /// the product.
  SPOT_API
  twa_graph_ptr product(const const_twa_graph_ptr& left,
                        const const_twa_graph_ptr& right,
                        unsigned left_state,
                        unsigned right_state);

  /// \ingroup twa_algorithms
  /// \brief Sum two automata using a synchronous product
  ///
  /// The resulting automaton will accept the union of both
  /// languages and have an acceptance condition that is the
  /// disjunction of the acceptance conditions of the two input
  /// automata.
  ///
  /// The algorithm also defines a named property called
  /// "product-states" with type spot::product_states.  This stores
  /// the pair of original state numbers associated to each state of
  /// the product.
  SPOT_API
  twa_graph_ptr product_or(const const_twa_graph_ptr& left,
                           const const_twa_graph_ptr& right);

  /// \ingroup twa_algorithms
  /// \brief Sum two automata using a synchronous product
  ///
  /// These variant allow changing the initial state of both automata
  /// in case you want to start the product at a different place.
  ///
  /// The resulting automaton will accept the sum of the languages
  /// recognized by each input automaton (with its initial state
  /// changed) and have an acceptance condition that is the
  /// disjunction of the acceptance conditions of the two input
  /// automata.
  ///
  /// The algorithm also defines a named property called
  /// "product-states" with type spot::product_states.  This stores
  /// the pair of original state numbers associated to each state of
  /// the product.
  SPOT_API
  twa_graph_ptr product_or(const const_twa_graph_ptr& left,
                           const const_twa_graph_ptr& right,
                           unsigned left_state,
                           unsigned right_state);

}
