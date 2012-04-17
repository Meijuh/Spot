// Copyright (C) 2010, 2011, 2012 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

/// \file ltlast/bunop.hh
/// \brief Bounded Unary operators
#ifndef SPOT_LTLAST_BUNOP_HH
# define SPOT_LTLAST_BUNOP_HH

#include <map>
#include <iosfwd>
#include "refformula.hh"

namespace spot
{
  namespace ltl
  {

    /// \brief Bounded unary operator.
    /// \ingroup ltl_ast
    class bunop : public ref_formula
    {
    public:
      enum type { Star };

      static const unsigned unbounded = -1U;

      /// \brief Build a bunop with bounds \a min and \a max.
      ///
      /// The following trivial simplifications are performed
      /// automatically (the left expression is rewritten as the right
      /// expression):
      ///   - 0[*0..max] = [*0]
      ///   - 0[*min..max] = 0 if min > 0
      ///   - [*0][*min..max] = [*0]
      ///   - Exp[*0] = [*0]
      ///   - Exp[*i..j][*k..l] = Exp[*ik..jl] if i*(k+1)<=jk+1.
      ///   - Exp[*1] = Exp
      ///
      /// These rewriting rules imply that it is not possible to build
      /// an LTL formula object that is SYNTACTICALLY equal to one of
      /// these left expressions.
      static formula* instance(type op,
			       formula* child,
			       unsigned min = 0,
			       unsigned max = unbounded);

      /// \brief Implement <code>b[->i..j]</code> using the Kleen star.
      ///
      /// <code>b[->i..j]</code> is implemented as
      /// <code>((!b)[*];b)[*i..j]</code>.
      ///
      /// Note that \a min defaults to 1, not 0, because [->] means
      /// [->1..].
      ///
      /// \pre \a child must be a Boolean formula.
      static formula* sugar_goto(formula* child,
				 unsigned min = 1,
				 unsigned max = unbounded);

      /// \brief Implement b[=i..j] using the Kleen star.
      ///
      /// <code>b[=i..j]</code> is implemented as
      /// <code>((!b)[*];b)[*i..j];(!b)[*]</code>.
      ///
      /// \pre \a child must be a Boolean formula.
      static formula* sugar_equal(formula* child,
				  unsigned min = 0,
				  unsigned max = unbounded);

      virtual void accept(visitor& v);
      virtual void accept(const_visitor& v) const;

      /// Get the sole operand of this operator.
      const formula* child() const;
      /// Get the sole operand of this operator.
      formula* child();

      /// Minimum number of repetition.
      unsigned min() const;
      /// Minimum number of repetition.
      unsigned max() const;

      /// \brief A string representation of the operator.
      ///
      /// For instance "[*2..]".
      std::string format() const;

      /// Get the type of this operator.
      type op() const;
      /// Get the type of this operator, as a string.
      const char* op_name() const;

      /// Return a canonic representation of operation.
      virtual std::string dump() const;

      /// Number of instantiated unary operators.  For debugging.
      static unsigned instance_count();

      /// Dump all instances.  For debugging.
      static std::ostream& dump_instances(std::ostream& os);

    protected:
      typedef std::pair<unsigned, unsigned> pairu;
      typedef std::pair<type, formula*> pairo;
      typedef std::pair<pairo, pairu> pair;
      typedef std::map<pair, bunop*> map;
      static map instances;

      bunop(type op, formula* child, unsigned min, unsigned max);
      virtual ~bunop();

    private:
      type op_;
      formula* child_;
      unsigned min_;
      unsigned max_;
    };

    /// \brief Cast \a f into a bunop.
    ///
    /// Cast \a f into a bunop iff it is a bunop instance.  Return 0
    /// otherwise.  This is faster than \c dynamic_cast.
    inline
    bunop*
    is_bunop(const formula* f)
    {
      if (f->kind() != formula::BUnOp)
	return 0;
      return static_cast<bunop*>(const_cast<formula*>(f));
    }

    /// \brief Cast \a f into a bunop if it has type \a op.
    ///
    /// Cast \a f into a bunop iff it is a bunop instance with operator \a op.
    /// Returns 0 otherwise.
    inline
    bunop*
    is_bunop(const formula* f, bunop::type op)
    {
      if (f->kind() != formula::BUnOp)
	return 0;
      bunop* bo = static_cast<bunop*>(const_cast<formula*>(f));
      if (bo->op() != op)
	return 0;
      return bo;
    }

    /// \brief Cast \a f into a bunop if it is a Star.
    ///
    /// Return 0 otherwise.
    inline
    bunop*
    is_Star(const formula* f)
    {
      return is_bunop(f, bunop::Star);
    }

  }
}
#endif // SPOT_LTLAST_BUNOP_HH
