// Copyright (C) 2010 Laboratoire de Recherche et Développement de
// l'EPITA (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#ifndef SPOT_LTLVISIT_CONSTERM_HH
# define SPOT_LTLVISIT_CONSTERM_HH

#include "ltlast/formula.hh"

namespace spot
{
  namespace ltl
  {
    /// \brief Compute the constant term of a formula.
    /// \ingroup ltl_misc
    ///
    /// The constant term of a formula is the empty word if the empty
    /// word is a model of the formula, it is false otherwise.
    ///
    /// \see constant_term_as_bool
    formula* constant_term(const formula* f);

    /// \brief Compute the constant term of a formula.
    /// \ingroup ltl_misc
    ///
    /// The constant term of a formula is the empty word if the empty
    /// word is a model of the formula, it is false otherwise.
    ///
    /// This variant of the function return true instead of
    /// constant::empty_word_instance() and false instead of
    /// constant::false_instance().
    ///
    /// \see constant_term
    bool constant_term_as_bool(const formula* f);
  }
}

#endif // SPOT_LTLVISIT_LENGTH_HH
