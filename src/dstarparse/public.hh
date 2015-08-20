// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include "twa/twagraph.hh"
#include "misc/location.hh"
#include "ltlenv/defaultenv.hh"
#include "parseaut/public.hh"
#include <string>
#include <list>
#include <utility>
#include <iosfwd>

namespace spot
{
  /// \addtogroup twa_io
  /// @{

  /// \brief Build a spot::twa_graph_ptr from ltl2dstar's output.
  /// \param filename The name of the file to parse.
  /// \param error_list A list that will be filled with
  ///        parse errors that occured during parsing.
  /// \param dict The BDD dictionary where to use.
  /// \param env The environment of atomic proposition into which parsing
  ///        should take place.
  /// \param debug When true, causes the parser to trace its execution.
  /// \return A pointer to the tgba built from \a filename, or
  ///        0 if the file could not be opened.
  ///
  /// Note that the parser usually tries to recover from errors.  It can
  /// return an non zero value even if it encountered error during the
  /// parsing of \a filename.  If you want to make sure \a filename
  /// was parsed succesfully, check \a error_list for emptiness.
  ///
  /// \warning This function is not reentrant.
  SPOT_API parsed_aut_ptr
  dstar_parse(const std::string& filename,
	      parse_aut_error_list& error_list,
	      const bdd_dict_ptr& dict,
	      ltl::environment& env = ltl::default_environment::instance(),
	      bool debug = false);

  /// @}
}
