// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#ifndef SPOT_TGBAALGOS_ARE_ISOMORPHIC_HH
# define SPOT_TGBAALGOS_ARE_ISOMORPHIC_HH

#include "tgba/tgbagraph.hh"

namespace spot
{
  /// \ingroup tgba_misc
  /// \brief Check whether two automata are isomorphic.
  /// Two automata a1 and a2 are said to be isomorphic if there is a bijection
  /// f between the states of a1 and a2 such that for every pair of state (s1,
  /// s2) of a1:
  /// - there is a transition from s1 to s2 iff there is a transition from f(s1)
  /// to f(s2)
  /// - if there is such a transition, then the acceptance set and acceptance
  /// condition are the same on the transition from s1 to s2 and from f(s1) to
  /// f(s2)
  SPOT_API bool are_isomorphic(const const_tgba_digraph_ptr a1,
                               const const_tgba_digraph_ptr a2);
}

#endif
