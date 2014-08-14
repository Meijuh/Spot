// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004, 2005 Laboratoire d'Informatique de Paris
// 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
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

#ifndef SPOT_TGBAALGOS_DUPEXP_HH
# define SPOT_TGBAALGOS_DUPEXP_HH

# include "tgba/tgbagraph.hh"

namespace spot
{
  /// \ingroup tgba_misc
  /// \brief Build an explicit automaton from all states of \a aut,
  /// numbering states in bread first order as they are processed.
  SPOT_API tgba_digraph_ptr
  tgba_dupexp_bfs(const const_tgba_ptr& aut);
  /// \ingroup tgba_misc
  /// \brief Build an explicit automaton from all states of \a aut,
  /// numbering states in depth first order as they are processed.
  SPOT_API tgba_digraph_ptr
  tgba_dupexp_dfs(const const_tgba_ptr& aut);

  /// \ingroup tgba_misc
  /// \brief Build an explicit automaton from all states of \a aut,
  /// numbering states in bread first order as they are processed.
  /// \a aut the automaton to duplicate
  /// \a relation a map of all the new states (represented by
  /// their number) to the old states.
  SPOT_API tgba_digraph_ptr
  tgba_dupexp_bfs(const const_tgba_ptr& aut,
		  std::vector<const state*>& relation);

  /// \ingroup tgba_misc
  /// \brief Build an explicit automata from all states of \a aut,
  /// numbering states in depth first order as they are processed.
  /// \a aut the automaton to duplicate
  /// \a relation a map of all the new states (represented by
  /// their number) to the old states.
  SPOT_API tgba_digraph_ptr
  tgba_dupexp_dfs(const const_tgba_ptr& aut,
		  std::vector<const state*>& relation);
}

#endif // SPOT_TGBAALGOS_DUPEXP_HH
