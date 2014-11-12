// Copyright (C) 2014 Laboratoire de Recherche et Développement
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


#ifndef SPOT_TGBAALGOS_STUTTER_INVARIANCE_HH
# define SPOT_TGBAALGOS_STUTTER_INVARIANCE_HH

#include "tgba/tgbagraph.hh"

namespace spot
{
  // TODO doc
  SPOT_API bool
  is_stutter_invariant(const ltl::formula* f);

  SPOT_API bool
  is_stutter_invariant(tgba_digraph_ptr&& aut_f,
		       tgba_digraph_ptr&& aut_nf, bdd aps,
		       int algo = 0);
}

#endif
