// -*- coding: utf-8 -*-
// Copyright (C) 2013-2015, 2017 Laboratoire de Recherche et
// Développement de l'Epita.
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
  /// \brief Complement a deterministic TωA
  ///
  /// The automaton \a aut should be deterministic.  It will be
  /// completed if it isn't already.  In these conditions,
  /// complementing the automaton can be done by just complementing
  /// the acceptance condition.
  ///
  /// In particular, this implies that an input that use
  /// generalized Büchi will be output as generalized co-Büchi.
  ///
  /// Functions like to_generalized_buchi() or remove_fin() are
  /// frequently called after dtwa_complement() to obtain an easier
  /// acceptance condition (maybe at the cost of losing determinism.)
  SPOT_API twa_graph_ptr
  dtwa_complement(const const_twa_graph_ptr& aut);
}
