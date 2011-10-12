// Copyright (C) 2011 Laboratoire de Recherche et Developpement de
// l'Epita (LRDE).
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

#ifndef SPOT_LTLVISIT_SIMPLIFY_HH
# define SPOT_LTLVISIT_SIMPLIFY_HH

#include "ltlast/formula.hh"
#include "bdd.h"

namespace spot
{
  namespace ltl
  {
    class ltl_simplifier_options
    {
    public:
      ltl_simplifier_options(bool basics = true,
			     bool synt_impl = true,
			     bool event_univ = true,
			     bool containment_checks = false,
			     bool containment_checks_stronger = false,
			     bool nenoform_stop_on_boolean = false)
	: reduce_basics(basics),
	  synt_impl(synt_impl),
	  event_univ(event_univ),
	  containment_checks(containment_checks),
	  containment_checks_stronger(containment_checks_stronger),
	  // If true, Boolean subformulae will not be put into
	  // negative normal form.
	  nenoform_stop_on_boolean(nenoform_stop_on_boolean)
      {
      }

      bool reduce_basics;
      bool synt_impl;
      bool event_univ;
      bool containment_checks;
      bool containment_checks_stronger;
      // If true, Boolean subformulae will not be put into
      // negative normal form.
      bool nenoform_stop_on_boolean;
    };

    // fwd declaration to hide technical details.
    class ltl_simplifier_cache;

    /// \brief Rewrite or simplify \a f in various ways.
    /// \ingroup ltl_rewriting
    class ltl_simplifier
    {
    public:
      ltl_simplifier();
      ltl_simplifier(ltl_simplifier_options& opt);
      ~ltl_simplifier();

      /// Simplify the formula \a f (using options supplied to the constructor).
      formula* simplify(const formula* f);

      /// Build the negative normal form of formula \a f.
      /// All negations of the formula are pushed in front of the
      /// atomic propositions.  Operators <=>, =>, xor are all removed
      /// (calling spot::ltl::unabbreviate_ltl is not needed).
      ///
      /// \param f The formula to normalize.
      /// \param negated If \c true, return the negative normal form of
      ///        \c !f
      formula* negative_normal_form(const formula* f, bool negated = false);

      /// \brief Syntactic implication.
      ///
      /// Returns whether \a f syntactically implies \a g.
      ///
      /// This is adapted from
      /// \verbatim
      /// @InProceedings{          somenzi.00.cav,
      /// author         = {Fabio Somenzi and Roderick Bloem},
      /// title          = {Efficient {B\"u}chi Automata for {LTL} Formulae},
      /// booktitle      = {Proceedings of the 12th International Conference on
      ///                  Computer Aided Verification (CAV'00)},
      /// pages          = {247--263},
      /// year           = {2000},
      /// volume         = {1855},
      /// series         = {Lecture Notes in Computer Science},
      /// publisher      = {Springer-Verlag}
      /// }
      /// \endverbatim
      ///
      bool syntactic_implication(const formula* f, const formula* g);
      /// \brief Syntactic implication with one negated argument.
      ///
      /// If \a right is true, this method returns whether
      /// \a f implies !\a g.  If \a right is false, this returns
      /// whether !\a g implies \a g.
      bool syntactic_implication_neg(const formula* f, const formula* g, bool right);

    private:
      ltl_simplifier_cache* cache_;
      // Copy disallowed.
      ltl_simplifier(const ltl_simplifier&);
    };
  }

}

#endif // SPOT_LTLVISIT_SIMPLIFY_HH
