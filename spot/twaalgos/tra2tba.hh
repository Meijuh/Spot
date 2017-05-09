// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement
// de l'Epita.
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
  /// \brief Convert a transition-based Rabin automaton to Büchi automaton,
  /// preserving determinism when possible.
  ///
  /// Return nullptr if the input is not a Rabin automaton, or is not
  /// transition-based.
  ///
  /// This modifies the algorithm from "Deterministic
  /// ω-automata vis-a-vis Deterministic Büchi Automata", S. Krishnan,
  /// A. Puri, and R. Brayton (ISAAC'94), but SCC-wise.
  SPOT_API twa_graph_ptr
  tra_to_tba(const const_twa_graph_ptr& aut);
}
