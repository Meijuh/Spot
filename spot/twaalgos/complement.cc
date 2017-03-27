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
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/cleanacc.hh>

namespace spot
{
  twa_graph_ptr
  dtwa_complement(const const_twa_graph_ptr& aut)
  {
    if (!is_deterministic(aut))
      throw
        std::runtime_error("dtwa_complement() requires a deterministic input");

    // Simply complete the automaton, and complement its acceptance.
    auto res = cleanup_acceptance_here(complete(aut));
    res->set_acceptance(res->num_sets(), res->get_acceptance().complement());
    // Complementing the acceptance is likely to break the terminal
    // property, but not weakness.  We make a useless call to
    // prop_keep() just so we remember to update it in the future if a
    // new argument is added.
    res->prop_keep({true, true, true, true, true});
    res->prop_terminal(trival::maybe());
    return res;
  }
}
