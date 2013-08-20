// -*- coding: utf-8 -*-
// Copyright (C) 2013 Laboratoire de Recherche et Développement
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

#ifndef SPOT_TGBAALGOS_DTBASAT_HH
# define SPOT_TGBAALGOS_DTBASAT_HH

#include <iosfwd>
#include "tgba/tgba.hh"
#include "tgba/tgbaexplicit.hh"

namespace spot
{
  /// \brief Attempt to reduce a deterministic TBA with a SAT solver.
  ///
  /// \param a the TGBA to reduce.  It should have only one acceptance
  ///  set and be deterministic.  I.e., it should be a deterministic TBA.
  ///
  /// \param target_state_number the expected number of states wanted
  /// in the resulting automaton.  If \a target_state_number is left
  /// to its default value of -1, this function will attempt to build
  /// the smallest possible deterministic TBA is can produce.
  ///
  /// \param state_based set to true to force all outgoing transitions
  /// of a state to share the same acceptance condition, effectively
  /// turning the TBA into a BA.
  ///
  /// If no automaton with \a target_state_number states is found, or
  /// (in case <code>target_state_number == -1</code>) if no smaller
  /// automaton is found, then a null pointer is returned.
  SPOT_API tgba_explicit_number*
  dtba_sat_minimize(const tgba* a, int target_state_number = -1,
		    bool state_based = false);
}

#endif // SPOT_TGBAALGOS_DTBASAT_HH
