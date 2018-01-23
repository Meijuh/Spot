// -*- coding: utf-8 -*-
// Copyright (C) 2017-2018 Laboratoire de Recherche et Développement de l'Epita.
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

namespace spot
{
  /// \ingroup twa_acc_transform
  /// \brief Turn a Rabin-like or Streett-like automaton into a parity automaton
  /// based on the index appearence record (IAR)
  ///
  /// If the input automaton has n states and k pairs, the output automaton has
  /// at most k!*n states and 2k+1 colors. If the input automaton is
  /// deterministic, the output automaton is deterministic as well, which is the
  /// intended use case for this function. If the input automaton is
  /// non-deterministic, the result is still correct, but way larger than an
  /// equivalent Büchi automaton.
  /// If the input automaton is Rabin-like (resp. Streett-like), the output
  /// automaton has max odd (resp. min even) acceptance condition.
  /// Details on the algorithm can be found in:
  ///   https://arxiv.org/pdf/1701.05738.pdf (published at TACAS 2017)
  ///
  /// Throws an std::runtime_error if the input is neither Rabin-like nor
  /// Street-like.
  SPOT_API
  twa_graph_ptr
  iar(const const_twa_graph_ptr& aut);

  /// \ingroup twa_acc_transform
  /// \brief Turn a Rabin-like or Streett-like automaton into a parity automaton
  /// based on the index appearence record (IAR)
  ///
  /// Returns nullptr if the input automaton is neither Rabin-like nor
  /// Streett-like, and calls spot::iar() otherwise.
  SPOT_API
  twa_graph_ptr
  iar_maybe(const const_twa_graph_ptr& aut);
}
