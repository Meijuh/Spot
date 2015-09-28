// -*- coding: utf-8 -*_
// Copyright (C) 2011, 2013, 2014 Laboratoire de Recherche et
// Developpement de l'Epita (LRDE)
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

#include "kripke/kripkeexplicit.hh"
#include "misc/location.hh"
#include "tl/defaultenv.hh"
#include <string>
#include <list>
#include <utility>
#include <iosfwd>

namespace spot
{

  /// \brief A parse diagnostic with its location.
  typedef std::pair<location, std::string> kripke_parse_error;
  /// \brief A list of parser diagnostics, as filled by parse.
  typedef std::list<kripke_parse_error> kripke_parse_error_list;



  SPOT_API kripke_explicit_ptr
  kripke_parse(const std::string& name,
               kripke_parse_error_list& error_list,
               const bdd_dict_ptr& dict,
               environment& env
               = default_environment::instance(),
               bool debug = false);


  /// \brief Format diagnostics produced by spot::kripke_parse.
  /// \param os Where diagnostics should be output.
  /// \param filename The filename that should appear in the diagnostics.
  /// \param error_list The error list filled by spot::parse while
  ///        parsing \a ltl_string.
  /// \return \c true if any diagnostic was output.
  SPOT_API
  bool format_kripke_parse_errors(std::ostream& os,
                                  const std::string& filename,
                                  kripke_parse_error_list& error_list);
}
