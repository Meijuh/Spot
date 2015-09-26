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
  /// \brief Whether an automaton represents a guarantee property.
  ///
  /// A weak deterministic TGBA represents a guarantee property if any
  /// accepting path ends on an accepting state with only one
  /// transition that is a self-loop labelled by true.
  ///
  /// Note that in the general case, this is only a sufficient
  /// condition : some guarantee automata might not be recognized with
  /// this check e.g. because of some non-determinism in the
  /// automaton.  In that case, you should interpret a \c false return
  /// value as "I don't know".
  ///
  /// If you apply this function on a weak deterministic TGBA
  /// (e.g. after a successful minimization with
  /// minimize_obligation()), then the result leaves no doubt: false
  /// really means that the automaton is not a guarantee property.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  SPOT_API bool
  is_guarantee_automaton(const const_twa_graph_ptr& aut,
			 scc_info* sm = nullptr);

  /// \brief Whether a minimized WDBA represents a safety property.
  ///
  /// A minimized WDBA (as returned by a successful run of
  /// minimize_obligation()) represent safety property if it contains
  /// only accepting transitions.
  ///
  /// \param aut the automaton to check
  SPOT_API bool
  is_safety_mwdba(const const_twa_graph_ptr& aut);

}
