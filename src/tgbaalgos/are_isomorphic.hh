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
#include <vector>

namespace spot
{
  /// \ingroup tgba_misc
  /// \brief Return an isomorphism between a1 and a2 if such an isomorphism
  /// exists. Otherwise, return an empty vector.
  /// The return value is a vector indexed by states of a1, and containing
  /// states of a2.
  SPOT_API std::vector<unsigned> are_isomorphic(const const_tgba_digraph_ptr a1,
                               const const_tgba_digraph_ptr a2);
}

#endif
