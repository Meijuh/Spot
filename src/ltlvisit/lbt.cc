// -*- coding: utf-8 -*-
// Copyright (C) 2012 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include <cassert>
#include <sstream>
#include <ctype.h>
#include <ostream>
#include <cstring>
#include "ltlast/allnodes.hh"
#include "ltlast/visitor.hh"
#include "lbt.hh"


namespace spot
{
  namespace ltl
  {
    namespace
    {
      static bool
      is_pnum(const char* str)
      {
	if (str[0] != 'p')
	  return false;
	while (*++str)
	  if (*str < '0' || *str > '9')
	    return false;
	return true;
      }

      class lbt_visitor: public visitor
      {
      public:
	lbt_visitor(std::ostream& os)
	  : os_(os)
	{
	}

	virtual
	~lbt_visitor()
	{
	}

	void
	visit(const atomic_prop* ap)
	{
	  std::string str = ap->name();
	  if (!is_pnum(str.c_str()))
	    os_ << '"' << str << "\" ";
	  else
	    os_ << str << ' ';
	}

	void
	visit(const constant* c)
	{
	  switch (c->val())
	    {
	    case constant::False:
	      os_ << "f ";
	      break;
	    case constant::True:
	      os_ << "t ";
	      break;
	    case constant::EmptyWord:
	      assert(!"unsupported constant");
	      break;
	    }
	}

	void
	visit(const binop* bo)
	{
	  switch (bo->op())
	    {
	    case binop::Xor:

	      break;
	    case binop::Implies:
	      os_ << "i ";
	      break;
	    case binop::Equiv:
	      os_ << "e ";
	      break;
	    case binop::U:
	      os_ << "U ";
	      break;
	    case binop::R:
	      os_ << "V ";
	      break;
	    case binop::W:
	      os_ << "W ";
	      break;
	    case binop::M:
	      os_ << "M ";
	      break;
	    case binop::UConcat:
	    case binop::EConcat:
	    case binop::EConcatMarked:
	      assert(!"unsupported operator");
	      break;
	    }
	  bo->first()->accept(*this);
	  bo->second()->accept(*this);
	}

	void
	visit(const bunop*)
	{
	  assert(!"unsupported operator");
	}

	void
	visit(const unop* uo)
	{
	  switch (uo->op())
	    {
	    case unop::Not:
	      os_ << "! ";
	      break;
	    case unop::X:
	      os_ << "X ";
	      break;
	    case unop::F:
	      os_ << "F ";
	      break;
	    case unop::G:
	      os_ << "G ";
	      break;
	    case unop::Finish:
	    case unop::Closure:
	    case unop::NegClosure:
	    case unop::NegClosureMarked:
	      assert(!"unsupported operator");
	      break;
	    }
	  uo->child()->accept(*this);
	}

	void
	visit(const automatop*)
	{
	  assert(!"unsupported operator");
	}

	void
	visit(const multop* mo)
	{
	  char o = 0;
	  switch (mo->op())
	    {
	    case multop::Or:
	      o = '|';
	      break;
	    case multop::And:
	      o = '&';
	      break;
	    case multop::OrRat:
	    case multop::AndRat:
	    case multop::AndNLM:
	    case multop::Concat:
	    case multop::Fusion:
	      assert(!"unsupported operator");
	      break;
	    }

	  unsigned n = mo->size();
	  for (unsigned i = n - 1; i != 0; --i)
	    os_ << o << ' ';

	  for (unsigned i = 0; i < n; ++i)
	    {
	      mo->nth(i)->accept(*this);
	    }
	}
      protected:
	std::ostream& os_;
      };

    } // anonymous

    std::ostream&
    to_lbt_string(const formula* f, std::ostream& os)
    {
      assert(f->is_ltl_formula());
      lbt_visitor v(os);
      f->accept(v);
      return os;
    }
  }
}