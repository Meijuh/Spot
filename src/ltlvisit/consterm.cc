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

#include "ltlvisit/consterm.hh"
#include "ltlast/allnodes.hh"
#include "ltlast/visitor.hh"

namespace spot
{
  namespace ltl
  {
    namespace
    {
      class consterm_visitor: public const_visitor
      {
      public:
	consterm_visitor() {}
	virtual ~consterm_visitor() {}

	bool result() const { return result_; }

	void
	visit(const atomic_prop*)
	{
	  result_ = false;
	}

	void
	visit(const constant* c)
	{
	  result_ = (c == constant::empty_word_instance());
	}

	void
	visit(const binop* bo)
	{
	  switch (bo->op())
	    {
	    case binop::Xor:
	    case binop::Implies:
	    case binop::Equiv:
	      assert(!"const_term not yet defined on Xor, Implies and Equiv");
	      break;
	    case binop::U:
	    case binop::W:
	    case binop::M:
	    case binop::R:
	    case binop::EConcat:
	    case binop::UConcat:
	    case binop::EConcatMarked:
	      assert(!"unsupported operator");
	      break;
	    }
	}

	void
	visit(const unop* uo)
	{
	  switch (uo->op())
	    {
	    case unop::Not:
	      result_ = false;
	      break;
	    case unop::Star:
	      result_ = true;
	      break;
	    case unop::X:
	    case unop::F:
	    case unop::G:
	    case unop::Finish:
	    case unop::Closure:
	    case unop::NegClosure:
	      assert(!"unsupported operator");
	      break;
	    }
	}

	void
	visit(const automatop*)
	{
	  assert(!"automatop not supported for constant term");
	}

	void
	visit(const multop* mo)
	{
	  // The fusion operator cannot be used to recognize the empty word.
	  if (mo->op() == multop::Fusion)
	    {
	      result_ = false;
	      return;
	    }

	  unsigned max = mo->size();
	  // This sets the initial value of result_.
	  mo->nth(0)->accept(*this);

	  for (unsigned n = 1; n < max; ++n)
	    {
	      bool r = constant_term_as_bool(mo->nth(n));

	      switch (mo->op())
		{
		case multop::Or:
		  result_ |= r;
		  if (result_)
		    return;
		  break;
		case multop::And:
		case multop::AndNLM:
		case multop::Concat:
		  result_ &= r;
		  if (!result_)
		    return;
		  break;
		case multop::Fusion:
		  /* Unreachable code */
		  assert(0);
		  break;
		}
	    }
	}

      private:
	bool result_;
      };

    }

    bool constant_term_as_bool(const formula* f)
    {
      consterm_visitor v;
      f->accept(v);
      return v.result();
    }

    formula* constant_term(const formula* f)
    {
      return constant_term_as_bool(f) ?
	constant::empty_word_instance() : constant::false_instance();
    }
  }
}
