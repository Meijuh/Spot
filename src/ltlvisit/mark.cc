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
#include "ltlvisit/tostring.hh"
#include "misc/casts.hh"

namespace spot
{
  namespace ltl
  {
    namespace
    {
      class simplify_mark_visitor : public visitor
      {
	formula* result_;
	mark_tools* tools_;

      public:
	simplify_mark_visitor(mark_tools* t)
	  : tools_(t)
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
	visit(bunop* bo)
	{
	  result_ = bo->clone();
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
	    case multop::AndNLM:
	      {
		typedef std::set<std::pair<formula*, formula*> > pset;
		pset Epairs, EMpairs;

		for (unsigned i = 0; i < mos; ++i)
		  {
		    formula* f = mo->nth(i);

		    if (f->kind() != formula::BinOp)
		      {
			res->push_back(recurse(f));
		      }
		    else
		      {
			binop* bo = static_cast<binop*>(f);
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
	  result_ = bo->clone();
	}

	formula*
	recurse(formula* f)
	{
	  return tools_->simplify_mark(f);
	}
      };


      class mark_visitor : public visitor
      {
	formula* result_;
	mark_tools* tools_;

      public:
	mark_visitor(mark_tools* t)
	  : tools_(t)
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
	visit(bunop* bo)
	{
	  result_ = bo->clone();
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
	      assert(!"mark not defined on logic abbreviations");
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
	  return tools_->mark_concat_ops(f);
	}
      };

    }

    mark_tools::mark_tools()
      : simpvisitor_(new simplify_mark_visitor(this)),
	markvisitor_(new mark_visitor(this))
    {
    }


    mark_tools::~mark_tools()
    {
      delete simpvisitor_;
      delete markvisitor_;
      {
	f2f_map::iterator i = simpmark_.begin();
	f2f_map::iterator end = simpmark_.end();
	while (i != end)
	  {
	    f2f_map::iterator old = i++;
	    old->second->destroy();
	    old->first->destroy();
	  }
      }
      {
	f2f_map::iterator i = markops_.begin();
	f2f_map::iterator end = markops_.end();
	while (i != end)
	  {
	    f2f_map::iterator old = i++;
	    old->second->destroy();
	    old->first->destroy();
	  }
      }
    }

    formula*
    mark_tools::mark_concat_ops(const formula* f)
    {
      f2f_map::iterator i = markops_.find(f);
      if (i != markops_.end())
	return i->second->clone();

      const_cast<formula*>(f)->accept(*markvisitor_);

      formula* r = down_cast<mark_visitor*>(markvisitor_)->result();
      markops_[f->clone()] = r->clone();
      return r;
    }

    formula*
    mark_tools::simplify_mark(const formula* f)
    {
      if (!f->is_marked())
	return f->clone();

      f2f_map::iterator i = simpmark_.find(f);
      if (i != simpmark_.end())
	return i->second->clone();

      const_cast<formula*>(f)->accept(*simpvisitor_);

      formula* r = down_cast<simplify_mark_visitor*>(simpvisitor_)->result();
      simpmark_[f->clone()] = r->clone();
      return r;
    }

  }
}
