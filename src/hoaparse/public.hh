// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014 Laboratoire de Recherche et Développement
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

#ifndef SPOT_HOAPARSE_PUBLIC_HH
# define SPOT_HOAPARSE_PUBLIC_HH

# include "tgba/tgbagraph.hh"
# include "misc/location.hh"
# include "ltlenv/defaultenv.hh"
# include <string>
# include <list>
# include <utility>
# include <iosfwd>
# include <misc/bitvect.hh>

namespace spot
{
  /// \addtogroup tgba_io
  /// @{

  /// \brief A parse diagnostic with its location.
  typedef std::pair<spot::location, std::string> hoa_parse_error;
  /// \brief A list of parser diagnostics, as filled by parse.
  typedef std::list<hoa_parse_error> hoa_parse_error_list;

  /// \brief Temporary encoding of an omega automaton produced by
  /// ltl2hoa.
  struct SPOT_API hoa_aut
  {
    // Transition structure of the automaton.
    // This is encoded as a TGBA without acceptance condition.
    tgba_digraph_ptr aut;
    bool aborted = false;
    spot::location loc;
  };

  typedef std::shared_ptr<hoa_aut> hoa_aut_ptr;
  typedef std::shared_ptr<const hoa_aut> const_hoa_aut_ptr;

  class SPOT_API hoa_stream_parser
  {
    spot::location last_loc;
  public:
    hoa_stream_parser(const std::string& filename);
    ~hoa_stream_parser();
    hoa_aut_ptr parse(hoa_parse_error_list& error_list,
		      const bdd_dict_ptr& dict,
		      ltl::environment& env =
		      ltl::default_environment::instance(),
		      bool debug = false);
  };

  /// \brief Build a spot::tgba_digraph from a HOA file.
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
  /// \warning This function is not reentrant.
  inline hoa_aut_ptr
  hoa_parse(const std::string& filename,
	    hoa_parse_error_list& error_list,
	    const bdd_dict_ptr& dict,
	    ltl::environment& env = ltl::default_environment::instance(),
	    bool debug = false)
  {
    try
      {
	hoa_stream_parser p(filename);
	return p.parse(error_list, dict, env, debug);
      }
    catch (std::runtime_error& e)
      {
	error_list.emplace_back(spot::location(), e.what());
	return nullptr;
      }
  }

  /// \brief Format diagnostics produced by spot::hoa_parse.
  /// \param os Where diagnostics should be output.
  /// \param filename The filename that should appear in the diagnostics.
  /// \param error_list The error list filled by spot::ltl::parse while
  ///        parsing \a ltl_string.
  /// \return \c true iff any diagnostic was output.
  SPOT_API bool
  format_hoa_parse_errors(std::ostream& os,
			  const std::string& filename,
			  hoa_parse_error_list& error_list);

  /// @}
}

#endif // SPOT_HOAPARSE_PUBLIC_HH
