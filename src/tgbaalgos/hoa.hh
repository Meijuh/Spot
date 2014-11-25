// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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

#ifndef SPOT_TGBAALGOS_HOA_HH
# define SPOT_TGBAALGOS_HOA_HH

#include <iosfwd>
#include "ltlast/formula.hh"
#include "tgba/fwd.hh"

namespace spot
{
  enum hoa_alias { Hoa_Alias_None, Hoa_Alias_Ap, Hoa_Alias_Cond };
  enum hoa_acceptance
    {
      Hoa_Acceptance_States,	/// state-based acceptance if
				/// (globally) possible
				/// transition-based acceptance
				/// otherwise.
      Hoa_Acceptance_Transitions, /// transition-based acceptance globally
      Hoa_Acceptance_Mixed    /// mix state-based and transition-based
    };

  /// \ingroup tgba_io
  /// \brief Print reachable states in Hanoi Omega Automata format.
  ///
  /// \param os The output stream to print on.
  /// \param g The automaton to output.
  /// \param f The (optional) formula associated to the automaton.  If given
  ///          it will be output as a comment.
  /// \param acceptance Force the type of acceptance mode used
  ///         in output.
  /// \param alias Whether aliases should be used in output.
  /// \param newlines Whether to use newlines in output.
  SPOT_API std::ostream&
  hoa_reachable(std::ostream& os,
		const const_tgba_ptr& g,
		const ltl::formula* f = 0,
		hoa_acceptance acceptance = Hoa_Acceptance_States,
		hoa_alias alias = Hoa_Alias_None,
		bool newlines = true);

  SPOT_API std::ostream&
  hoa_reachable(std::ostream& os,
		const const_tgba_ptr& g,
		const char* opt,
		const ltl::formula* f = 0);
}

#endif // SPOT_TGBAALGOS_HOA_HH
