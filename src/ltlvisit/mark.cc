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

#include "mark.hh"
#include "ltlast/allnodes.hh"
#include <cassert>
#include <algorithm>

namespace spot
{
  namespace ltl
  {
    namespace
    {

      class has_mark_visitor : public visitor
      {
	bool result_;
      public:
	has_mark_visitor()
	  : result_(false)
	{
	}
	~has_mark_visitor()
	{
	}

	bool
	result()
	{
	  return result_;
	}

	void
	visit(atomic_prop*)
	{
	}

	void
	visit(constant*)
	{
	}

	void
	visit(unop*)
	{
	}

	void
	visit(automatop*)
	{
	}

	void
	visit(multop* mo)
	{
	  unsigned mos = mo->size();
	  for (unsigned i = 0; i < mos && !result_; ++i)
	    result_ = recurse(mo->nth(i));
	}

	void
	visit(binop* bo)
	{
	  switch (bo->op())
	    {
	    case binop::EConcatMarked:
	      result_ = true;
	      return;
	    case binop::Xor:
	    case binop::Implies:
	    case binop::Equiv:
	    case binop::U:
	    case binop::W:
	    case binop::M:
	    case binop::R:
	    case binop::EConcat:
	    case binop::UConcat:
	      return;
	    }
	  /* Unreachable code. */
	  assert(0);
	}

	bool
	recurse(const formula* f)
	{
	  return has_mark(f);
	}
      };

      class simplify_mark_visitor : public visitor
      {
	formula* result_;
	bool has_mark_;

      public:
	simplify_mark_visitor()
	  : has_mark_(false)
	{
	}

	~simplify_mark_visitor()
	{
	}

	formula*
	result()
	{
	  return result_;
	}

	bool
	has_mark()
	{
	  return has_mark_;
	}

	void
	visit(atomic_prop* ao)
	{
	  result_ = ao->clone();
	}

	void
	visit(constant* c)
	{
	  result_ = c->clone();
	}

	void
	visit(unop* uo)
	{
	  result_ = uo->clone();
	}

	void
	visit(automatop* ao)
	{
	  result_ = ao->clone();
	}

	void
	visit(multop* mo)
	{
	  unsigned mos = mo->size();
	  multop::vec* res = new multop::vec;
	  switch (mo->op())
	    {
	    case multop::Or:
	    case multop::Concat:
	    case multop::Fusion:
	      for (unsigned i = 0; i < mos; ++i)
		res->push_back(recurse(mo->nth(i)));
	      break;
	    case multop::And:
	      {
		typedef std::set<std::pair<formula*, formula*> > pset;
		pset Epairs, EMpairs;

		for (unsigned i = 0; i < mos; ++i)
		  {
		    formula* f = mo->nth(i);

		    binop* bo = dynamic_cast<binop*>(f);
		    if (!bo)
		      res->push_back(recurse(f));
		    else
		      {
			switch (bo->op())
			  {
			  case binop::Xor:
			  case binop::Implies:
			  case binop::Equiv:
			  case binop::U:
			  case binop::W:
			  case binop::M:
			  case binop::R:
			  case binop::UConcat:
			    res->push_back(recurse(f));
			    break;
			  case binop::EConcat:
			    Epairs.insert(std::make_pair(bo->first(),
							 bo->second()));
			    break;
			  case binop::EConcatMarked:
			    EMpairs.insert(std::make_pair(bo->first(),
							  bo->second()));
			    has_mark_ = true;
			    break;
			  }
		      }
		  }
		for (pset::const_iterator i = EMpairs.begin();
		     i != EMpairs.end(); ++i)
		  res->push_back(binop::instance(binop::EConcatMarked,
						 i->first->clone(),
						 i->second->clone()));
		for (pset::const_iterator i = Epairs.begin();
		     i != Epairs.end(); ++i)
		  if (EMpairs.find(*i) == EMpairs.end())
		    res->push_back(binop::instance(binop::EConcat,
						   i->first->clone(),
						   i->second->clone()));
	      }
	    }
	  result_ = multop::instance(mo->op(), res);
	}

	void
	visit(binop* bo)
	{
	  switch (bo->op())
	    {
	    case binop::EConcatMarked:
	      has_mark_ = true;
	      /* fall through */
	    case binop::Xor:
	    case binop::Implies:
	    case binop::Equiv:
	    case binop::U:
	    case binop::W:
	    case binop::M:
	    case binop::R:
	    case binop::EConcat:
	    case binop::UConcat:
	      result_ = bo->clone();
	      return;
	    }
	  /* Unreachable code. */
	  assert(0);
	}

	formula*
	recurse(const formula* f)
	{
	  formula* g = f->clone();
	  has_mark_ |= simplify_mark(g);
	  return g;
	}
      };


      class mark_visitor : public visitor
      {
	formula* result_;
      public:
	mark_visitor()
	{
	}
	~mark_visitor()
	{
	}

	formula*
	result()
	{
	  return result_;
	}

	void
	visit(atomic_prop* ap)
	{
	  result_ = ap->clone();
	}

	void
	visit(constant* c)
	{
	  result_ = c->clone();
	}

	void
	visit(unop* uo)
	{
	  result_ = uo->clone();
	}

	void
	visit(automatop* ao)
	{
	  result_ = ao->clone();
	}

	void
	visit(multop* mo)
	{
	  multop::vec* res = new multop::vec;
	  unsigned mos = mo->size();
	  for (unsigned i = 0; i < mos; ++i)
	    res->push_back(recurse(mo->nth(i)));
	  result_ = multop::instance(mo->op(), res);
	}

	void
	visit(binop* bo)
	{
	  switch (bo->op())
	    {
	    case binop::Xor:
	    case binop::Implies:
	    case binop::Equiv:
	      assert(!"mark no defined on logic abbreviations");
	    case binop::U:
	    case binop::W:
	    case binop::M:
	    case binop::R:
	    case binop::UConcat:
	      result_ = bo->clone();
	      return;
	    case binop::EConcatMarked:
	    case binop::EConcat:
	      {
		formula* f1 = bo->first()->clone();
		formula* f2 = recurse(bo->second());
		result_ = binop::instance(binop::EConcatMarked, f1, f2);
		return;
	      }
	    }
	  /* Unreachable code. */
	  assert(0);
	}

	formula*
	recurse(formula* f)
	{
	  return mark_concat_ops(f);
	}
      };

    }

    formula*
    mark_concat_ops(const formula* f)
    {
      mark_visitor v;
      const_cast<formula*>(f)->accept(v);
      return v.result();
    }

    bool
    simplify_mark(formula*& f)
    {
      simplify_mark_visitor v;
      const_cast<formula*>(f)->accept(v);
      f->destroy();
      f = v.result();
      return v.has_mark();
    }

    bool
    has_mark(const formula* f)
    {
      has_mark_visitor v;
      const_cast<formula*>(f)->accept(v);
      return v.result();
    }



  }
}
