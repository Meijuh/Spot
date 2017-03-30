// -*- coding: utf-8 -*-
// Copyright (C) 2013-2015, 2017 Laboratoire de Recherche et
// Développement de l'Epita.
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

#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/dualize.hh>
#include <spot/twaalgos/isdet.hh>


namespace spot
{
  twa_graph_ptr
  dtwa_complement(const const_twa_graph_ptr& aut)
  {
    if (!is_deterministic(aut))
      throw
        std::runtime_error("dtwa_complement() requires a deterministic input");

    return dualize(aut);
  }
}
