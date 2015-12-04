// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et Développement
// de l'Epita (LRDE)
// Copyright (C) 2004  Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include <spot/twaalgos/projrun.hh>
#include <spot/twa/twa.hh>
#include <spot/twaalgos/emptiness.hh>

namespace spot
{

  twa_run_ptr
  project_twa_run(const const_twa_ptr& a_run,
		   const const_twa_ptr& a_proj,
		   const const_twa_run_ptr& run)
  {
    auto res = std::make_shared<twa_run>(a_proj);
    for (auto& i: run->prefix)
      res->prefix.emplace_back(a_run->project_state(i.s, a_proj),
			       i.label, i.acc);
    for (auto& i: run->cycle)
      res->prefix.emplace_back(a_run->project_state(i.s, a_proj),
			       i.label, i.acc);
    return res;
  }
}
