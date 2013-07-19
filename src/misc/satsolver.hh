// -*- coding: utf-8 -*-
// Copyright (C) 2013 Laboratoire de Recherche et Développement
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

#ifndef SPOT_MISC_SATSOLVER_HH
#define SPOT_MISC_SATSOLVER_HH

#include "common.hh"

namespace spot
{
  class printable;

  /// \brief Run a SAT solver.
  ///
  /// Run a SAT solver using the input in file \a input,
  /// and sending output in file \a output.
  ///
  /// These two arguments are instance of printable, as
  /// they will be evaluated in a %-escaped string such as
  ///    "satsolver %I >%O"
  /// This command can be overridden using the
  /// <code>SPOT_SATSOLVER</code> environment variable.
  ///
  /// Note that temporary_file instances implement the
  /// printable interface.
  SPOT_API int
  satsolver(printable* input, printable* output);
}

#endif // SPOT_MISC_SATSOLVER_HH
