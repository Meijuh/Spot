// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2011, 2013, 2014, 2015 Laboratoire de Recherche
// et Développement de l'Epita (LRDE)
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

#include "sccinfo.hh"

namespace spot
{
  /// \brief Whether an automaton is terminal.
  ///
  /// An automaton is terminal if it is weak, and all accepting SCCs
  /// are complete.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  SPOT_API bool
  is_terminal_automaton(const const_twa_graph_ptr& aut, scc_info* sm = nullptr);


  /// \brief Whether an automaton is weak.
  ///
  /// An automaton is weak if if any given SCC, all transitions belong
  /// to the same acceptance sets.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  SPOT_API bool
  is_weak_automaton(const const_twa_graph_ptr& aut, scc_info* sm = nullptr);

  /// \brief Whether a minimized WDBA represents a safety property.
  ///
  /// A minimized WDBA (as returned by a successful run of
  /// minimize_obligation()) represent safety property if it contains
  /// only accepting transitions.
  ///
  /// \param aut the automaton to check
  SPOT_API bool
  is_safety_mwdba(const const_twa_graph_ptr& aut);

  /// \brief Whether an automaton is weak or terminal.
  ///
  /// This sets the "weak" and "terminal" property as appropriate.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  SPOT_API void
  check_strength(const twa_graph_ptr& aut, scc_info* sm = nullptr);
}
