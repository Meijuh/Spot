// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2011, 2013, 2014, 2015, 2016, 2017 Laboratoire
// de Recherche et Développement de l'Epita (LRDE)
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

#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  /// \brief Check whether an automaton is terminal.
  ///
  /// An automaton is terminal if it is weak, all its accepting SCCs
  /// are complete, and no accepting transitions lead to a
  /// non-accepting SCC.
  ///
  /// If ignore_trivial_scc is set, accepting transitions from trivial
  /// SCCs are ignored.
  ///
  /// This property guarantees that a word is accepted if it has some
  /// prefix that reaches an accepting transition.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  ///
  /// In addition to returning the result as a Boolean, this will set
  /// the prop_terminal() property of the automaton as a side-effect,
  /// so further calls will return in constant-time.
  SPOT_API bool
  is_terminal_automaton(const const_twa_graph_ptr& aut, scc_info* sm = nullptr,
                        bool ignore_trivial_scc = false);

  /// \brief Check whether an automaton is weak.
  ///
  /// An automaton is weak if in any given SCC, all transitions belong
  /// to the same acceptance sets.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  ///
  /// In addition to returning the result as a Boolean, this will set
  /// the prop_weak() property of the automaton as a side-effect,
  /// so further calls will return in constant-time.
  SPOT_API bool
  is_weak_automaton(const const_twa_graph_ptr& aut, scc_info* sm = nullptr);

  /// \brief Check whether an automaton is very-weak.
  ///
  /// An automaton is very-weak if in any given SCC, all transitions
  /// belong to the same acceptance sets, and the SCC has only one
  /// state.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  ///
  /// In addition to returning the result as a Boolean, this will set
  /// the prop_very_weak() and prop_weak() properties of the automaton
  /// as a side-effect, so further calls will return in constant-time.
  SPOT_API bool
  is_very_weak_automaton(const const_twa_graph_ptr& aut,
                         scc_info* sm = nullptr);

  /// \brief Check whether an automaton is inherently weak.
  ///
  /// An automaton is inherently weak if in any given SCC, there
  /// are only accepting cycles, or only rejecting cycles.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  ///
  /// In addition to returning the result as a Boolean, this will set
  /// the prop_inherently_weak() property of the automaton as a
  /// side-effect, so further calls will return in constant-time.
  SPOT_API bool
  is_inherently_weak_automaton(const const_twa_graph_ptr& aut,
                               scc_info* sm = nullptr);

  /// \brief Check whether an automaton is a safety automaton.
  ///
  /// A safety automaton has only accepting SCCs (or trivial
  /// SCCs).
  ///
  /// A minimized WDBA (as returned by a successful run of
  /// minimize_obligation()) represent safety property if it is a
  /// safety automaton.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  SPOT_API bool
  is_safety_automaton(const const_twa_graph_ptr& aut,
                      scc_info* sm = nullptr);

  /// \brief Check whether an automaton is weak or terminal.
  ///
  /// This sets the "inherently weak", "weak", "very-weak" and
  /// "terminal" properties as appropriate.
  ///
  /// \param aut the automaton to check
  ///
  /// \param sm an scc_info object for the automaton if available (it
  /// will be built otherwise).
  SPOT_API void
  check_strength(const twa_graph_ptr& aut, scc_info* sm = nullptr);


  /// \brief Extract a sub-automaton of a given strength
  ///
  /// The string \a keep should be a non-empty combination of
  /// the following letters:
  /// - 'w': keep only inherently weak SCCs (i.e., SCCs in which
  ///        all transitions belong to the same acceptance sets) that
  ///        are not terminal.
  /// - 't': keep terminal SCCs (i.e., inherently weak SCCs that are complete)
  /// - 's': keep strong SCCs (i.e., SCCs that are not inherently weak).
  ///
  /// This algorithm returns a subautomaton that contains all SCCs of the
  /// requested strength, plus any upstream SCC (but adjusted not to be
  /// accepting).
  ///
  /// The definition are basically those used in the following paper,
  /// except that we extra the "inherently weak" part instead of the
  /// weak part because we can now test for inherent weakness
  /// efficiently enough (not enumerating all cycles as suggested in
  /// the paper).
  /** \verbatim
      @inproceedings{renault.13.tacas,
        author = {Etienne Renault and Alexandre Duret-Lutz and Fabrice
                  Kordon and Denis Poitrenaud},
        title = {Strength-Based Decomposition of the Property {B\"u}chi
                  Automaton for Faster Model Checking},
        booktitle = {Proceedings of the 19th International Conference on Tools
                  and Algorithms for the Construction and Analysis of Systems
                  (TACAS'13)},
        editor = {Nir Piterman and Scott A. Smolka},
        year = {2013},
        month = mar,
        pages = {580--593},
        publisher = {Springer},
        series = {Lecture Notes in Computer Science},
        volume = {7795},
        doi = {10.1007/978-3-642-36742-7_42}
      }
      \endverbatim */
  ///
  /// \param aut the automaton to decompose
  /// \param keep a string specifying the strengths to keep: it should
  SPOT_API twa_graph_ptr
  decompose_strength(const const_twa_graph_ptr& aut, const char* keep);

  /// \brief Extract a sub-automaton of a SCC
  ///
  /// This algorithm returns a subautomaton that contains the requested SCC,
  /// plus any upstream SCC (but adjusted not to be accepting).
  ///
  /// \param sm the SCC info map of the automaton
  /// \param scc_num the index in the map of the SCC to keep
  SPOT_API twa_graph_ptr
  decompose_scc(scc_info& sm, unsigned scc_num);

  /// \brief Extract a sub-automaton of an accepting SCC
  ///
  /// This algorithm returns a subautomaton that contains the `scc_index'th
  /// accepting SCC, plus any upstream SCC (but adjusted not to be accepting).
  ///
  /// \param aut the automaton to decompose
  /// \param scc_index the ID of the accepting SCC to keep
  SPOT_API twa_graph_ptr
  decompose_acc_scc(const const_twa_graph_ptr& aut, int scc_index);
}
