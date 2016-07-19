// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015, 2016 Laboratoire de Recherche
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

#include <spot/twa/twagraph.hh>

namespace spot
{
  SPOT_API twa_graph_ptr
  sl(const twa_graph_ptr&);

  SPOT_API twa_graph_ptr
  sl(const const_twa_graph_ptr&, bdd);

  SPOT_API twa_graph_ptr
  sl2(const twa_graph_ptr&);

  SPOT_API twa_graph_ptr
  sl2(const const_twa_graph_ptr&, bdd);

#ifndef SWIG
  SPOT_API twa_graph_ptr
  sl2(twa_graph_ptr&&, bdd = bddfalse);
#endif

  SPOT_API twa_graph_ptr
  closure(const const_twa_graph_ptr&);

#ifndef SWIG
  SPOT_API twa_graph_ptr
  closure(twa_graph_ptr&&);
#endif

  /// \ingroup ltl_misc
  /// \brief Check if a formula has the stutter invariance property.
  SPOT_API bool
  is_stutter_invariant(formula f);

  SPOT_API bool
  is_stutter_invariant(twa_graph_ptr&& aut_f,
                       twa_graph_ptr&& aut_nf, bdd aps,
                       int algo = 0);

  /// \brief Check whether \a aut is stutter-invariant
  ///
  /// This procedure requires the negation of \a aut to
  /// be computed.  This is easily done of \a aut is deterministic
  /// or if a formula represented by \a aut is known.  Otherwise
  /// \a aut will be complemented by determinization, which can
  /// be expansive.   The determinization can be forbidden using
  /// the \a do_not_determinize flag.
  ///
  /// If no complemented automaton could be constructed, the
  /// the result will be returned as trival::maybe().
  SPOT_API trival
  check_stutter_invariance(const twa_graph_ptr& aut,
                           formula f = nullptr,
                           bool do_not_determinize = false);
}
