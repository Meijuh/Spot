// Copyright (C) 2009, 2010, 2011 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
// Copyright (C) 2004, 2005 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include "syntimpl.hh"
#include "ltlast/allnodes.hh"
#include <cassert>

#include "lunabbrev.hh"
#include "simpfg.hh"
#include "nenoform.hh"

namespace spot
{
  namespace ltl
  {
    namespace
    {

      class inf_right_recurse_visitor: public const_visitor
      {
      public:

	inf_right_recurse_visitor(const formula *f,
				  syntactic_implication_cache* c)
	  : result_(false), f(f), c(c)
	{
	}

	virtual
	~inf_right_recurse_visitor()
	{
	}

	int
	result() const
	{
	  return result_;
	}

	void
	visit(const atomic_prop* ap)
	{
	  if (f == ap)
	    result_ = true;
	}

	void
	visit(const constant* c)
	{
	  switch (c->val())
	    {
	    case constant::True:
	      result_ = true;
	      return;
	    case constant::False:
	      result_ = false;
	      return;
	    case constant::EmptyWord:
	      result_ = false;
	    }
	}

	void
	visit(const bunop*)
	{
	}

	void
	visit(const unop* uo)
	{
	  const formula* f1 = uo->child();
	  switch (uo->op())
	    {
	    case unop::Not:
	      if (uo == f)
		result_ = true;
	      return;
	    case unop::X:
	      {
		if (f->kind() != formula::UnOp)
		  return;
		const unop* op = static_cast<const unop*>(f);
		if (op->op() == unop::X)
		  result_ = c->syntactic_implication(op->child(), f1);
	      }
	      return;
	    case unop::F:
	      /* F(a) = true U a */
	      result_ = c->syntactic_implication(f, f1);
	      return;
	    case unop::G:
	      /* G(a) = false R a */
	      if (c->syntactic_implication(f, constant::false_instance()))
		result_ = true;
	      return;
	    case unop::Finish:
	    case unop::Closure:
	    case unop::NegClosure:
	      return;
	    }
	  /* Unreachable code.  */
	  assert(0);
	}

	void
	visit(const binop* bo)
	{
	  const formula* f1 = bo->first();
	  const formula* f2 = bo->second();
	  switch (bo->op())
	    {
	    case binop::Xor:
	    case binop::Equiv:
	    case binop::Implies:
	    case binop::UConcat:
	    case binop::EConcat:
	    case binop::EConcatMarked:
	      return;
	    case binop::U:
	    case binop::W:
	      if (c->syntactic_implication(f, f2))
		result_ = true;
	      return;
	    case binop::R:
	      if (f->kind() == formula::BinOp)
		{
		  const binop* fb = static_cast<const binop*>(f);
		  if (fb->op() == binop::R
		      && c->syntactic_implication(fb->first(), f1)
		      && c->syntactic_implication(fb->second(), f2))
		    {
		      result_ = true;
		      return;
		    }
		}
	      if (f->kind() == formula::UnOp)
		{
		  const unop* fu = static_cast<const unop*>(f);
		  if (fu->op() == unop::G
		      && f1 == constant::false_instance()
		      && c->syntactic_implication(fu->child(), f2))
		    {
		      result_ = true;
		      return;
		    }
		}
	      if (c->syntactic_implication(f, f1)
		  && c->syntactic_implication(f, f2))
		result_ = true;
	      return;
	    case binop::M:
	      if (f->kind() == formula::BinOp)
		{
		  const binop* fb = static_cast<const binop*>(f);
		  if (fb->op() == binop::M
		      && c->syntactic_implication(fb->first(), f1)
		      && c->syntactic_implication(fb->second(), f2))
		    {
		      result_ = true;
		      return;
		    }
		}
	      if (f->kind() == formula::UnOp)
		{
		  const unop* fu = static_cast<const unop*>(f);
		  if (fu->op() == unop::F
		      && f2 == constant::true_instance()
		      && c->syntactic_implication(fu->child(), f1))
		  {
		    result_ = true;
		    return;
		  }
		}
	      if (c->syntactic_implication(f, f1)
		  && c->syntactic_implication(f, f2))
		result_ = true;
	      return;
	    }
	  /* Unreachable code.  */
	  assert(0);
	}

	void
	visit(const automatop*)
	{
	  assert(0);
	}

	void
	visit(const multop* mo)
	{
	  multop::type op = mo->op();
	  unsigned mos = mo->size();
	  switch (op)
	    {
	    case multop::And:
	      for (unsigned i = 0; i < mos; ++i)
		if (!c->syntactic_implication(f, mo->nth(i)))
		  return;
	      result_ = true;
	      break;
	    case multop::Or:
	      for (unsigned i = 0; i < mos && !result_; ++i)
		if (c->syntactic_implication(f, mo->nth(i)))
		  result_ = true;
	      break;
	    case multop::Concat:
	    case multop::Fusion:
	    case multop::AndNLM:
	      break;
	    }
	}

      protected:
	bool result_; /* true if f < f1, false otherwise. */
	const formula* f;
	syntactic_implication_cache* c;
      };

      /////////////////////////////////////////////////////////////////////////

      class inf_left_recurse_visitor: public const_visitor
      {
      public:

	inf_left_recurse_visitor(const formula *f,
				 syntactic_implication_cache* c)
	  : result_(false), f(f), c(c)
	{
	}

	virtual
	~inf_left_recurse_visitor()
	{
	}

	bool
	special_case(const binop* f2)
	{
	  if (f->kind() != formula::BinOp)
	    return false;
	  const binop* fb = static_cast<const binop*>(f);
	  if (fb->op() == f2->op()
	      && c->syntactic_implication(f2->first(), fb->first())
	      && c->syntactic_implication(f2->second(), fb->second()))
	    return true;
	  return false;
	}

	bool
	special_case_check(const formula* f2)
	{
	  if (f2->kind() != formula::BinOp)
	    return false;
	  return special_case(static_cast<const binop*>(f2));
	}

	int
	result() const
	{
	  return result_;
	}

	void
	visit(const atomic_prop* ap)
	{
	  inf_right_recurse_visitor v(ap, c);
	  const_cast<formula*>(f)->accept(v);
	  result_ = v.result();
	}

	void
	visit(const bunop*)
	{
	}

	void
	visit(const constant* cst)
	{
	  inf_right_recurse_visitor v(cst, c);
	  switch (cst->val())
	    {
	    case constant::True:
	      const_cast<formula*>(f)->accept(v);
	      result_ = v.result();
	      return;
	    case constant::False:
	      result_ = true;
	      return;
	    case constant::EmptyWord:
	      result_ = true;
	      return;
	    }
	  /* Unreachable code.  */
	  assert(0);
	}

	void
	visit(const unop* uo)
	{
	  const formula* f1 = uo->child();
	  inf_right_recurse_visitor v(uo, c);
	  switch (uo->op())
	    {
	    case unop::Not:
	      if (uo == f)
		result_ = true;
	      return;
	    case unop::X:
	      if (f->kind() == formula::UnOp)
		{
		  const unop* op = static_cast<const unop*>(f);
		  if (op->op() == unop::X)
		    result_ = c->syntactic_implication(f1, op->child());
		}
	      return;
	    case unop::F:
	      {
		/* F(a) = true U a */
		const formula* tmp = binop::instance(binop::U,
						     constant::true_instance(),
						     f1->clone());
		if (special_case_check(tmp))
		  {
		    result_ = true;
		    tmp->destroy();
		    return;
		  }
		if (c->syntactic_implication(tmp, f))
		  result_ = true;
		tmp->destroy();
		return;
	      }
	    case unop::G:
	      {
		/* G(a) = false R a */
		const formula* tmp = binop::instance(binop::R,
						     constant::false_instance(),
						     f1->clone());
		if (special_case_check(tmp))
		  {
		    result_ = true;
		    tmp->destroy();
		    return;
		  }
		if (c->syntactic_implication(tmp, f))
		  result_ = true;
		tmp->destroy();
		return;
	      }
	    case unop::Finish:
	    case unop::Closure:
	    case unop::NegClosure:
	      return;
	    }
	  /* Unreachable code.  */
	  assert(0);
	}

	void
	visit(const binop* bo)
	{
	  if (special_case(bo))
	    {
	      result_ = true;
	      return;
	    }

	  const formula* f1 = bo->first();
	  const formula* f2 = bo->second();
	  switch (bo->op())
	    {
	    case binop::Xor:
	    case binop::Equiv:
	    case binop::Implies:
	    case binop::UConcat:
	    case binop::EConcat:
	    case binop::EConcatMarked:
	      return;
	    case binop::U:
	      /* (a < c) && (c < d) => a U b < c U d */
	      if (f->kind() == formula::BinOp)
		{
		  const binop* fb = static_cast<const binop*>(f);
		  if (fb->op() == binop::U
		      && c->syntactic_implication(f1, fb->first())
		      && c->syntactic_implication(f2, fb->second()))
		    {
		      result_ = true;
		      return;
		    }
		}
	      if (f->kind() == formula::UnOp)
		{
		  const unop* fu = static_cast<const unop*>(f);
		  if (fu->op() == unop::F
		      && f1 == constant::true_instance()
		      && c->syntactic_implication(f2, fu->child()))
		    {
		      result_ = true;
		      return;
		    }
		}
	      if (c->syntactic_implication(f1, f)
		  && c->syntactic_implication(f2, f))
		result_ = true;
	      return;
	    case binop::W:
	      /* (a < c) && (c < d) => a W b < c W d */
	      if (f->kind() == formula::BinOp)
		{
		  const binop* fb = static_cast<const binop*>(f);
		  if (fb->op() == binop::W
		      && c->syntactic_implication(f1, fb->first())
		      && c->syntactic_implication(f2, fb->second()))
		    {
		      result_ = true;
		      return;
		    }
		}
	      if (f->kind() == formula::UnOp)
		{
		  const unop* fu = static_cast<const unop*>(f);
		  if (fu && fu->op() == unop::G
		      && f2 == constant::false_instance()
		      && c->syntactic_implication(f1, fu->child()))
		    {
		      result_ = true;
		      return;
		    }
		}
	      if (c->syntactic_implication(f1, f)
		  && c->syntactic_implication(f2, f))
		result_ = true;
	      return;
	    case binop::R:
	      if (f->kind() == formula::UnOp)
		{
		  const unop* fu = static_cast<const unop*>(f);
		  if (fu->op() == unop::G
		      && f1 == constant::false_instance()
		      && c->syntactic_implication(f2, fu->child()))
		  {
		    result_ = true;
		    return;
		  }
		}
	      if (c->syntactic_implication(f2, f))
		result_ = true;
	      return;
	    case binop::M:
	      if (f->kind() == formula::UnOp)
		{
		  const unop* fu = static_cast<const unop*>(f);
		  if (fu->op() == unop::F
		      && f2 == constant::true_instance()
		      && c->syntactic_implication(f1, fu->child()))
		  {
		    result_ = true;
		    return;
		  }
		}
	      if (c->syntactic_implication(f2, f))
		result_ = true;
	      return;
	    }
	  /* Unreachable code.  */
	  assert(0);
	}

	void
	visit(const automatop*)
	{
	  assert(0);
	}

	void
	visit(const multop* mo)
	{
	  multop::type op = mo->op();
	  unsigned mos = mo->size();
	  switch (op)
	    {
	    case multop::And:
	      for (unsigned i = 0; (i < mos) && !result_; ++i)
		if (c->syntactic_implication(mo->nth(i), f))
		  result_ = true;
	      break;
	    case multop::Or:
	      for (unsigned i = 0; i < mos; ++i)
		if (!c->syntactic_implication(mo->nth(i), f))
		  return;
	      result_ = true;
	      break;
	    case multop::Concat:
	    case multop::Fusion:
	    case multop::AndNLM:
	      break;
	    }
	}

      protected:
	bool result_; /* true if f1 < f, 1 otherwise. */
	const formula* f;
	syntactic_implication_cache* c;
      };

    } // anonymous

    // This is called by syntactic_implication() after the
    // formulae have been normalized.
    bool
    syntactic_implication_cache::syntactic_implication(const formula* f1,
						       const formula* f2)
    {
      if (f1 == f2)
	return true;
      if (f2 == constant::true_instance()
	  || f1 == constant::false_instance())
	return true;

      // Cache lookup
      {
	pairf p(f1, f2);
	cache_t::const_iterator i = cache_.find(p);
	if (i != cache_.end())
	  return i->second;
      }

      bool result = false;

      inf_left_recurse_visitor v1(f2, this);
      const_cast<formula*>(f1)->accept(v1);
      if (v1.result())
	{
	  result = true;
	}
      else
	{
	  inf_right_recurse_visitor v2(f1, this);
	  const_cast<formula*>(f2)->accept(v2);
	  if (v2.result())
	    result = true;
	}

      // Cache result
      {
	pairf p(f1->clone(), f2->clone());
	cache_[p] = result;
      }

      return result;
    }

    bool
    syntactic_implication_cache::syntactic_implication_neg(const formula* f1,
							   const formula* f2,
							   bool right)
    {
      formula* l = f1->clone();
      formula* r = f2->clone();
      if (right)
	r = unop::instance(unop::Not, r);
      else
	l = unop::instance(unop::Not, l);

      // Cache lookup
      {
	pairf p(l, r);
	cache_t::const_iterator i = cache_.find(p);
	if (i != cache_.end())
	  {
	    l->destroy();
	    r->destroy();
	    return i->second;
	  }
      }
      // Save the cache key for latter.
      pairf p(l->clone(), r->clone());

      formula* tmp = unabbreviate_logic(l);
      l->destroy();
      l = simplify_f_g(tmp);
      tmp->destroy();
      tmp = negative_normal_form(l);
      l->destroy();
      l = tmp;

      tmp = unabbreviate_logic(r);
      r->destroy();
      r = simplify_f_g(tmp);
      tmp->destroy();
      tmp = negative_normal_form(r);
      r->destroy();
      r = tmp;

      bool result = syntactic_implication(l, r);
      l->destroy();
      r->destroy();

      // Cache result if is has not be done by syntactic_implication() already.
      if (l != p.first || r != p.second)
	{
	  cache_[p] = result;
	}
      else
	{
	  p.first->destroy();
	  p.second->destroy();
	}
      return result;
    }

    syntactic_implication_cache::~syntactic_implication_cache()
    {
      cache_t::const_iterator i = cache_.begin();
      while (i != cache_.end())
	{
	  // Advance the iterator before deleting the key.
	  pairf p = i->first;
	  ++i;

	  p.first->destroy();
	  p.second->destroy();
	}
    }

  }
}
