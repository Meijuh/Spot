// -*- coding: utf-8 -*-
// Copyright (C) 2012-2015, 2017, 2018 Laboratoire de
// Recherche et Développement de l'Epita.
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
  /// \brief Degeneralize a spot::tgba into an equivalent sba with
  /// only one acceptance condition.
  ///
  /// This algorithms will build a new explicit automaton that has
  /// at most (N+1) times the number of states of the original automaton.
  ///
  /// When \a use_z_lvl is set, the level of the degeneralized
  /// automaton is reset everytime an SCC is exited.  If \a
  /// use_cust_acc_orders is set, the degeneralization will compute a
  /// custom acceptance order for each SCC (this option is disabled by
  /// default because our benchmarks show that it usually does more
  /// harm than good).  If \a use_lvl_cache is set, everytime an SCC
  /// is entered on a state that as already been associated to some
  /// level elsewhere, reuse that level (set it to 2 to keep the
  /// smallest number, 3 to keep the largest level, and 1 to keep the
  /// first level found). If \a ignaccsl is set, we do not directly
  /// jump to the accepting level if the entering state has an
  /// accepting self-loop.  If \a remove_extra_scc is set (the default)
  /// we ensure that the output automaton has as many SCCs as the input
  /// by removing superfluous SCCs.
  ///
  /// Any of these three options will cause the SCCs of the automaton
  /// \a a to be computed prior to its actual degeneralization.
  ///
  /// The degeneralize_tba() variant produce a degeneralized automaton
  /// with transition-based acceptance.
  ///
  /// The mapping between each state of the resulting automaton
  /// and the original state of the input automaton is stored in the
  /// "original-states" named property of the produced automaton.  Call
  /// `aut->get_named_prop<std::vector<unsigned>>("original-states")`
  /// to retrieve it.  Note that these functions may return the original
  /// automaton as-is if it is already degeneralized; in this case
  /// the "original-states" property is not defined.
  /// Similarly, the property "degen-levels" keeps track of the degeneralization
  /// levels.  To retrieve it, call
  /// `aut->get_named_prop<std::vector<unsigned>>("degen-levels")`.
  /// \@{
  SPOT_API twa_graph_ptr
  degeneralize(const const_twa_graph_ptr& a, bool use_z_lvl = true,
               bool use_cust_acc_orders = false,
               int use_lvl_cache = 1,
               bool skip_levels = true,
               bool ignaccsl = false,
               bool remove_extra_scc = true);

  SPOT_API twa_graph_ptr
  degeneralize_tba(const const_twa_graph_ptr& a, bool use_z_lvl = true,
                   bool use_cust_acc_orders = false,
                   int use_lvl_cache = 1,
                   bool skip_levels = true,
                   bool ignaccsl = false,
                   bool remove_extra_scc = true);
  /// \@}
}
