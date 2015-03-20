// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014 Laboratoire de Recherche et Développement
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

#include "tgba/tgbagraph.hh"

namespace spot
{
  /// \ingroup tgba_misc
  /// \brief Degeneralize a spot::tgba into an equivalent sba with
  /// only one acceptance condition.
  ///
  /// This algorithms will build a new explicit automaton that has
  /// at most (N+1) times the number of states of the original automaton.
  ///
  /// When \a use_z_lvl is set, the level of the degeneralized
  /// automaton is reset everytime an accepting SCC is exited.  If \a
  /// use_cust_acc_orders is set, the degeneralization will compute a
  /// custom acceptance order for each SCC (this option is disabled by
  /// default because our benchmarks show that it usually does more
  /// harm than good).  If \a use_lvl_cache is set, everytime an SCC
  /// is entered on a state that as already been associated to some
  /// level elsewhere, reuse that level (set it to 2 to keep the
  /// smallest number, 3 to keep the largest level, and 1 to keep the
  /// first level found).
  ///
  /// Any of these three options will cause the SCCs of the automaton
  /// \a a to be computed prior to its actual degeneralization.
  ///
  /// The degeneralize_tba() variant produce a degeneralized automaton
  /// with transition-based acceptance.
  /// \@{
  SPOT_API tgba_digraph_ptr
  degeneralize(const const_tgba_digraph_ptr& a, bool use_z_lvl = true,
	       bool use_cust_acc_orders = false,
	       int use_lvl_cache = 1,
	       bool skip_levels = true);

  SPOT_API tgba_digraph_ptr
  degeneralize_tba(const const_tgba_digraph_ptr& a, bool use_z_lvl = true,
		   bool use_cust_acc_orders = false,
		   int use_lvl_cache = 1,
		   bool skip_levels = true);
  /// \@}
}
