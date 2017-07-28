// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement de
// l'Epita (LRDE)
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

#include <spot/tl/formula.hh>
#include <spot/twa/fwd.hh>

namespace spot
{
  /// \brief Return true if the formula has the recurrence property.
  SPOT_API
  bool is_recurrence(formula f, const twa_graph_ptr& aut);

  /// \brief Return the class of \a f in the temporal hierarchy of Manna
  /// and Pnueli (PODC'90).
  ///
  /// The class is indicated using a character among:
  /// - 'B' (bottom) safety properties that are also guarantee properties
  /// - 'G' guarantee properties that are not also safety properties
  /// - 'S' safety properties that are not also guarantee properties
  /// - 'O' obligation properties that are not safety or guarantee
  ///       properties
  /// - 'P' persistence properties that are not obligations
  /// - 'R' recurrence properties that are not obligations
  /// - 'T' (top) properties that are not persistence or recurrence
  ///   properties
  SPOT_API char mp_class(formula f);


  /// \brief Return the class of \a f in the temporal hierarchy of Manna
  /// and Pnueli (PODC'90).
  ///
  /// The \a opt parameter should be a string specifying options
  /// for expressing the class.  If \a opt is empty, the
  /// result is one character among B, G, S, O, P, R, T, specifying
  /// the most precise class to which the formula belongs.
  /// If \a opt contains 'w', then the string contains all the
  /// characters corresponding to the classes that contain \a f.
  /// If \a opt contains 'v', then the characters are replaced
  /// by the name of each class.  Space and commas are ignored.
  /// Any ']' ends the processing of the options.
  SPOT_API std::string mp_class(formula f, const char* opt);

  /// \brief Expand a class in the temporal hierarchy of Manna
  /// and Pnueli (PODC'90).
  ///
  /// \a mpc should be a character among B, G, S, O, P, R, T
  /// specifying a class in the hierarchy.
  ///
  /// The \a opt parameter should be a string specifying options for
  /// expressing the class.  If \a opt is empty, the result is \a mpc.
  /// If \a opt contains 'w', then the string contains all the
  /// characters corresponding to the super-classes of \a mpc.  If \a
  /// opt contains 'v', then the characters are replaced by the name
  /// of each class.  Space and commas are ignored.  Any ']' ends the
  /// processing of the options.
  SPOT_API std::string mp_class(char mpc, const char* opt);
}
