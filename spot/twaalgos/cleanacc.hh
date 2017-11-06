// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2017 Laboratoire de Recherche et Développement
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
  /// \ingroup twa_algorithms
  /// \brief Remove useless acceptance sets
  ///
  /// This removes from the automaton the acceptance marks that are
  /// not used in the acceptance condition.  This also removes from
  /// the acceptance conditions the terms that corresponds to empty
  /// or full sets.
  ///
  /// If \a strip is true (the default), the remaining acceptance set
  /// numbers will be shifted down to reduce maximal number of
  /// acceptance sets used.
  SPOT_API twa_graph_ptr
  cleanup_acceptance_here(twa_graph_ptr aut, bool strip = true);

  /// \ingroup twa_algorithms
  /// \brief Remove useless acceptance sets
  ///
  /// This removes from the automaton the acceptance marks that are
  /// not used in the acceptance condition.  This also removes from
  /// the acceptance conditions the terms that corresponds to empty
  /// or full sets.
  ///
  SPOT_API twa_graph_ptr
  cleanup_acceptance(const_twa_graph_ptr aut);

  /// @{
  /// \ingroup twa_algorithms
  /// \brief Simplify an acceptance condition
  ///
  /// Does evereything cleanup_acceptance() does, but additionally:
  /// merge identical sets, detect whether to sets i and j are
  /// complementary to apply the following reductions:
  ///   - `Fin(i) & Inf(j) = Fin(i)`
  ///   - `Fin(i) & Fin(j) = f`
  ///   - `Fin(i) & Inf(i) = f`
  ///   - `Fin(i) | Inf(j) = Inf(j)`
  ///   - `Inf(i) | Inf(j) = t`
  ///   - `Fin(i) | Inf(i) = t`
  SPOT_API twa_graph_ptr
  simplify_acceptance_here(twa_graph_ptr aut);

  SPOT_API twa_graph_ptr
  simplify_acceptance(const_twa_graph_ptr aut);
  /// @}
}
