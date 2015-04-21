// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include <bddx.h>
#include "tgbaproxy.hh"

namespace spot
{

  /// \ingroup tgba_on_the_fly_algorithms
  /// \brief Mask a TGBA, keeping a given set of states.
  ///
  /// Mask the TGBA \a to_mask, keeping only the
  /// states from \a to_keep.  The initial state
  /// can optionally be reset to \a init.
  SPOT_API const_twa_ptr
  build_tgba_mask_keep(const const_twa_ptr& to_mask,
		       const state_set& to_keep,
		       const state* init = 0);

  /// \ingroup tgba_on_the_fly_algorithms
  /// \brief Mask a TGBA, rejecting a given set of states.
  ///
  /// Mask the TGBA \a to_mask, keeping only the states that are not
  /// in \a to_ignore.  The initial state can optionally be reset to
  /// \a init.
  SPOT_API const_twa_ptr
  build_tgba_mask_ignore(const const_twa_ptr& to_mask,
			 const state_set& to_ignore,
			 const state* init = 0);


  /// \ingroup tgba_on_the_fly_algorithms
  /// \brief Mask a TGBA, rejecting some acceptance set of transitions.
  ///
  /// This will ignore all transitions that have the TO_IGNORE
  /// acceptance mark.  The initial state can optionally be reset to
  /// \a init.
  ///
  /// Note that the acceptance condition of the automaton (i.e. the
  /// set of all acceptance set) is not changed, because so far this
  /// function is only needed in graph algorithms that do not call
  /// all_acceptance_conditions().
  SPOT_API const_twa_ptr
  build_tgba_mask_acc_ignore(const const_twa_ptr& to_mask,
			     unsigned to_ignore,
			     const state* init = 0);
}
