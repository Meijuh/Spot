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
#include <string>
#include <list>
#include <utility>
#include <iosfwd>
#include <misc/bitvect.hh>

namespace spot
{
  /// \addtogroup twa_io
  /// @{

#ifndef SWIG
  /// \brief A parse diagnostic with its location.
  typedef std::pair<spot::location, std::string> parse_aut_error;
  /// \brief A list of parser diagnostics, as filled by parse.
  typedef std::list<parse_aut_error> parse_aut_error_list;
#else
    // Turn parse_aut_error_list into an opaque type for Swig.
  struct parse_aut_error_list {};
#endif

  enum class parsed_aut_type { HOA, NeverClaim, LBTT, DRA, DSA, Unknown };

  /// \brief Temporary encoding of an omega automaton produced by
  /// the parser.
  struct SPOT_API parsed_aut
  {
    // Transition structure of the automaton.
    // This is encoded as a TGBA without acceptance condition.
    twa_graph_ptr aut;
    bool aborted = false;
    spot::location loc;
    parsed_aut_type type = parsed_aut_type::Unknown;
  };

  typedef std::shared_ptr<parsed_aut> parsed_aut_ptr;
  typedef std::shared_ptr<const parsed_aut> const_parsed_aut_ptr;

  class SPOT_API automaton_stream_parser
  {
    spot::location last_loc;
    std::string filename_;
    bool ignore_abort_;
  public:
    automaton_stream_parser(const std::string& filename,
			    bool ignore_abort = false);
    // Read from an already open file descriptor.
    // Use filename in error messages.
    automaton_stream_parser(int fd, const std::string& filename,
			    bool ignore_abort = false);
    // Read from a buffer
    automaton_stream_parser(const char* data,
			    const std::string& filename,
			    bool ignore_abort = false);
    ~automaton_stream_parser();
    parsed_aut_ptr parse(parse_aut_error_list& error_list,
			 const bdd_dict_ptr& dict,
			 ltl::environment& env =
			 ltl::default_environment::instance(),
			 bool debug = false);
    // Raises a parse_error on any syntax error
    twa_graph_ptr parse_strict(const bdd_dict_ptr& dict,
			       ltl::environment& env =
			       ltl::default_environment::instance(),
			       bool debug = false);
  };

  /// \brief Build a spot::twa_graph from a HOA file or a neverclaim.
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
  /// return a non zero value even if it encountered error during the
  /// parsing of \a filename.  If you want to make sure \a filename
  /// was parsed succesfully, check \a error_list for emptiness.
  ///
  /// The specification of the HOA format can be found at
  ///    http://adl.github.io/hoaf/
  ///
  /// The grammar of neverclaim will not accept every possible
  /// neverclaim output.  It has been tuned to accept the output of
  /// spin -f, ltl2ba, ltl3ba, and modella.  If you know of some other
  /// tool that produce Büchi automata in the form of a neverclaim,
  /// but is not understood by this parser, please report it to
  /// spot@lrde.epita.fr.
  ///
  /// \warning This function is not reentrant.
  inline parsed_aut_ptr
  parse_aut(const std::string& filename,
	    parse_aut_error_list& error_list,
	    const bdd_dict_ptr& dict,
	    ltl::environment& env = ltl::default_environment::instance(),
	    bool debug = false)
  {
    try
      {
	automaton_stream_parser p(filename);
	return p.parse(error_list, dict, env, debug);
      }
    catch (std::runtime_error& e)
      {
	error_list.emplace_back(spot::location(), e.what());
	return nullptr;
      }
  }

  /// \brief Format diagnostics produced by spot::parse_aut.
  /// \param os Where diagnostics should be output.
  /// \param filename The filename that should appear in the diagnostics.
  /// \param error_list The error list filled by spot::ltl::parse while
  ///        parsing \a ltl_string.
  /// \return \c true iff any diagnostic was output.
  SPOT_API bool
  format_parse_aut_errors(std::ostream& os,
			  const std::string& filename,
			  parse_aut_error_list& error_list);

  /// @}
}
