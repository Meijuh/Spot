// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
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

#include "tgba/tgbagraph.hh"

namespace spot
{
  SPOT_API tgba_digraph_ptr
  sl(const const_tgba_digraph_ptr&, const ltl::formula* = nullptr);

  SPOT_API tgba_digraph_ptr
  sl(const const_tgba_digraph_ptr&, bdd);

  SPOT_API tgba_digraph_ptr
  sl2(const const_tgba_digraph_ptr&, const ltl::formula* = nullptr);

  SPOT_API tgba_digraph_ptr
  sl2(const const_tgba_digraph_ptr&, bdd);

#ifndef SWIG
  SPOT_API tgba_digraph_ptr
  sl2(tgba_digraph_ptr&&, bdd = bddfalse);
#endif

  SPOT_API tgba_digraph_ptr
  closure(const const_tgba_digraph_ptr&);

#ifndef SWIG
  SPOT_API tgba_digraph_ptr
  closure(tgba_digraph_ptr&&);
#endif

  /// \ingroup ltl_misc
  /// \brief Check if a formula has the stutter invariance property.
  SPOT_API bool
  is_stutter_invariant(const ltl::formula* f);

  SPOT_API bool
  is_stutter_invariant(tgba_digraph_ptr&& aut_f,
		       tgba_digraph_ptr&& aut_nf, bdd aps,
		       int algo = 0);
}
