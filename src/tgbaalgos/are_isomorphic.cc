// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2004, 2005  Laboratoire d'Informatique de Paris 6 (LIP6),
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

#include "tgba/tgbagraph.hh"
#include "tgbaalgos/are_isomorphic.hh"
#include "tgbaalgos/canonicalize.hh"

namespace spot
{
  bool
  are_isomorphic(const const_tgba_digraph_ptr aut1,
                 const const_tgba_digraph_ptr aut2)
  {
    auto tmp1 = make_tgba_digraph(aut1);
    auto tmp2 = make_tgba_digraph(aut2);
    spot::canonicalize(tmp1);
    spot::canonicalize(tmp2);
    return *tmp1 == *tmp2;
  }
}
