// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement de
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

#include <spot/twa/twa.hh>

namespace spot
{
  /// \brief Convert an alternating automaton to a weak alternating automaton.
  ///
  /// The input automaton must have a generalized co-Büchi or Büchi acceptance
  /// condition.
  /// The automaton will be converted into a weak Büchi automaton. If the input
  /// automaton is already weak, it will simply be copied.
  ///
  /// For details about the algorithm used, see the following papers:
  /** \verbatim
      @article{kupferman.01.tocl,
        author      = {Orna Kupferman and Moshe Y. Vardi},
        title       = {Weak alternating automata are not that weak},
        journal     = {ACM Transactions on Computational Logic (TOCL)},
        month       = {July},
        year        = 2001,
        pages       = {408--429},
        volume      = {2},
        number      = {3},
        publisher   = {ACM New York, NY, USA}
      }
      @article{kupferman.05.tcs,
        author      = {Orna Kupferman and Moshe Y. Vardi},
        title       = {From complementation to certification},
        journal     = {Theoretical Computer Science},
        month       = {November},
        year        = 2005,
        pages       = {83--100},
        volume      = {345},
        number      = {1},
        publisher   = {Elsevier}
      }
      \endverbatim */
  /// Although at the end of the above paper there is a hint at an optimization
  /// that greatly reduces the number of transition in the resulting automaton,
  /// but in return makes the run of remove_alternation algorithm way slower.
  /// Hence, the optimization is disabled by default.
  ///
  /// \param aut the automaton to convert to weak
  /// \param less whether to activate the optimization on the number of
  /// transitions or not, disabled by default
  SPOT_API
  twa_graph_ptr to_weak_alternating(const_twa_graph_ptr& aut,
                                    bool less = false);
}
