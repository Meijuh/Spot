// Copyright (C) 2010 Laboratoire de Recherche et Développement
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

#include "kind.hh"
#include "ltlast/allnodes.hh"
#include "ltlast/visitor.hh"
#include <iostream>

namespace spot
{
  namespace ltl
  {
    namespace
    {

      class kind_visitor : public visitor
      {
	unsigned result_;
      public:
	kind_visitor()
	  : result_(All_Kind)
	{
	}
	~kind_visitor()
	{
	}

	unsigned
	result()
	{
	  return result_;
	}

	void
	visit(atomic_prop*)
	{
	}

	void
	visit(constant* c)
	{
	  if (c == constant::empty_word_instance())
	    result_ &= ~(Boolean_Kind | LTL_Kind | ELTL_Kind);
	}

	void
	visit(bunop* bo)
	{
	  result_ = recurse(bo->child());
	  result_ &= ~(Boolean_Kind | LTL_Kind | ELTL_Kind);
	}

	void
	visit(unop* uo)
	{
	  result_ = recurse(uo->child());

	  switch (uo->op())
	    {
	    case unop::NegClosure:
	    case unop::Closure:
	      result_ &= ~(Boolean_Kind | LTL_Kind | ELTL_Kind);
	      return;
	    case unop::Finish:
	      result_ &= ~(Boolean_Kind | LTL_Kind | PSL_Kind);
	      return;
	    case unop::Not:
	      if (!dynamic_cast<atomic_prop*>(uo->child()))
		result_ &= ~NeNoForm_Kind;
	      return;
	    case unop::X:
	      result_ &= ~(Boolean_Kind | No_X_Kind | ELTL_Kind);
	      return;
	    case unop::F:
	    case unop::G:
	      result_ &= ~(Boolean_Kind | SugarFree_LTL_Kind | ELTL_Kind);
	      return;
	    }
	  /* Unreachable code. */
	  assert(0);
	}

	void
	visit(automatop* ao)
	{
	  unsigned aos = ao->size();
	  for (unsigned i = 0; i < aos && !result_; ++i)
	    result_ &= recurse(ao->nth(i));

	  result_ &= ~(Boolean_Kind | LTL_Kind | PSL_Kind);
	}

	void
	visit(multop* mo)
	{
	  unsigned mos = mo->size();
	  for (unsigned i = 0; i < mos && !result_; ++i)
	    result_ &= recurse(mo->nth(i));

	  switch (mo->op())
	    {
	    case multop::Or:
	    case multop::And:
	      return;
	    case multop::AndNLM:
	      // The non-matching-length-And (&) can only appear
	      // in the rational parts of PSL formula.  We
	      // don't remove the Boolean_Kind flags, because
	      // applied to atomic propositions a&b has the same
	      // effect as a&&b.
	      result_ &= ~(LTL_Kind | ELTL_Kind);
	      return;
	    case multop::Concat:
	    case multop::Fusion:
	      result_ &= ~(Boolean_Kind | LTL_Kind | ELTL_Kind);
	      return;
	    }
	}

	void
	visit(binop* bo)
	{
	  result_ = recurse(bo->first()) & recurse(bo->second());

	  switch (bo->op())
	    {
	    case binop::EConcatMarked:
	    case binop::UConcat:
	    case binop::EConcat:
	      result_ &= ~(Boolean_Kind | LTL_Kind | ELTL_Kind);
	      return;
	    case binop::Xor:
	    case binop::Implies:
	    case binop::Equiv:
	      result_ &= ~(NeNoForm_Kind | SugarFree_Boolean_Kind);
	      return;
	    case binop::U:
	    case binop::W:
	    case binop::M:
	    case binop::R:
	      result_ &= ~(Boolean_Kind | ELTL_Kind);
	      return;
	    }
	  /* Unreachable code. */
	  assert(0);
	}

	unsigned
	recurse(const formula* f)
	{
	  return kind_of(f);
	}
      };
    }

    unsigned
    kind_of(const formula* f)
    {
      kind_visitor v;
      const_cast<formula*>(f)->accept(v);
      return v.result();
    }



    std::ostream&
    print_kind(std::ostream& o, unsigned k, bool abbreviated)
    {
      struct data { char abbrev; const char* name; };
      static const data kind_name[] =
	{
	  {'B', "Boolean formula"}, // 1
	  {'&', "no sugar Boolean operator"}, // 2
	  {'!', "in negative normal form"}, // 4
	  {'x', "no X LTL operator"}, // 8
	  {'f', "no sugar LTL operator"}, // 16
	  {'L', "LTL formula"}, // 32
	  {'E', "ELTL formula"}, // 64
	  {'P', "PSL formula"}, // 128
	};
      const char* comma = "";
      unsigned size = (sizeof kind_name)/(sizeof *kind_name);
      for (unsigned i = 0; i < size; ++i)
	{
	  if ((k & 1))
	    {
	      if (abbreviated)
		{
		  o << kind_name[i].abbrev;
		}
	      else
		{
		  o << comma << kind_name[i].name;
		  comma = ", ";
		}
	    }
	  k >>= 1;
	}
      return o;
    }


    std::ostream&
    print_kind(std::ostream& o, const formula* f, bool abbreviated)
    {
      print_kind(o, kind_of(f), abbreviated);
      return o;
    }


  }
}
