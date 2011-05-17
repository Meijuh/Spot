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


#include "simplify.hh"
#include "misc/hash.hh"
#include "tgba/bdddict.hh"
#include "ltlast/allnodes.hh"
#include "ltlast/visitor.hh"
#include <cassert>

namespace spot
{
  namespace ltl
  {

    // The name of this class is public, but not its contents.
    class ltl_simplifier_cache
    {
      typedef Sgi::hash_map<const formula*, const formula*,
			    ptr_hash<formula> > f2f_map;
      typedef Sgi::hash_map<const formula*, bdd,
			    ptr_hash<formula> > f2b_map;
    public:
      ltl_simplifier_options options;

      ~ltl_simplifier_cache()
      {
	{
	  f2f_map::iterator i = simplified_.begin();
	  f2f_map::iterator end = simplified_.end();
	  while (i != end)
	    {
	      f2f_map::iterator old = i++;
	      old->second->destroy();
	      old->first->destroy();
	    }
	}
	{
	  f2f_map::iterator i = nenoform_.begin();
	  f2f_map::iterator end = nenoform_.end();
	  while (i != end)
	    {
	      f2f_map::iterator old = i++;
	      old->second->destroy();
	      old->first->destroy();
	    }
	}
	{
	  f2b_map::iterator i = as_bdd_.begin();
	  f2b_map::iterator end = as_bdd_.end();
	  while (i != end)
	    {
	      f2b_map::iterator old = i++;
	      old->first->destroy();
	    }
	}

	dict_.unregister_all_my_variables(this);
      }

      ltl_simplifier_cache()
      {
      }

      ltl_simplifier_cache(ltl_simplifier_options opt) : options(opt)
      {
      }

      // Convert a Boolean formula into a BDD for easier comparison.
      bdd
      as_bdd(const formula* f)
      {
	// Lookup the result in case it has already been computed.
	f2b_map::const_iterator it = as_bdd_.find(f);
	if (it != as_bdd_.end())
	  return it->second;

	bdd result = bddfalse;

	switch (f->kind())
	  {
	  case formula::Constant:
	    if (f == constant::true_instance())
	      result = bddtrue;
	    else if (f == constant::false_instance())
	      result = bddtrue;
	    else
	      assert(!"Unsupported operator");
	    break;
	  case formula::AtomicProp:
	    result = bdd_ithvar(dict_.register_proposition(f, this));
	    break;
	  case formula::UnOp:
	    {
	      const unop* uo = static_cast<const unop*>(f);
	      assert(uo->op() == unop::Not);
	      result = !as_bdd(uo->child());
	      break;
	    }
	  case formula::BinOp:
	    {
	      const binop* bo = static_cast<const binop*>(f);
	      int op = 0;
	      switch (bo->op())
		{
		case binop::Xor:
		  op = bddop_xor;
		  break;
		case binop::Implies:
		  op = bddop_imp;
		  break;
		case binop::Equiv:
		  op = bddop_biimp;
		  break;
		default:
		  assert(!"Unsupported operator");
		}
	      result = bdd_apply(as_bdd(bo->first()), as_bdd(bo->second()), op);
	      break;
	    }
	  case formula::MultOp:
	    {
	      const multop* mo = static_cast<const multop*>(f);
	      switch (mo->op())
		{
		case multop::And:
		  {
		    result = bddtrue;
		    unsigned s = mo->size();
		    for (unsigned n = 0; n < s; ++n)
		      result &= as_bdd(mo->nth(n));
		    break;
		  }
		case multop::Or:
		  {
		    result = bddfalse;
		    unsigned s = mo->size();
		    for (unsigned n = 0; n < s; ++n)
		      result |= as_bdd(mo->nth(n));
		    break;
		  }
		case multop::Concat:
		case multop::Fusion:
		case multop::AndNLM:
		  assert(!"Unsupported operator");
		  break;
		}
	      break;
	    }
	  case formula::BUnOp:
	  case formula::AutomatOp:
	    assert(!"Unsupported operator");
	    break;
	  }

	// Cache the result before returning.
	as_bdd_[f->clone()] = result;
	return result;
      }

      const formula*
      lookup_nenoform(const formula* f)
      {
	f2f_map::const_iterator i = nenoform_.find(f);
	if (i == nenoform_.end())
	  return 0;
	return i->second->clone();
      }

      void
      cache_nenoform(const formula* orig, const formula* nenoform)
      {
	nenoform_[orig->clone()] = nenoform->clone();
      }

      const formula*
      lookup_simplified(const formula* f)
      {
	f2f_map::const_iterator i = simplified_.find(f);
	if (i == simplified_.end())
	  return 0;
	return i->second->clone();
      }

      void
      cache_simplified(const formula* orig, const formula* simplified)
      {
	simplified_[orig->clone()] = simplified->clone();
      }

    private:
      bdd_dict dict_;
      f2b_map as_bdd_;
      f2f_map simplified_;
      f2f_map nenoform_;
    };


    namespace
    {
      // Forward declaration.
      const formula*
      nenoform_recursively(const formula* f,
			   bool negated,
			   ltl_simplifier_cache* c);

      class negative_normal_form_visitor: public visitor
      {
      public:
	negative_normal_form_visitor(bool negated, ltl_simplifier_cache* c)
	  : negated_(negated), cache_(c)
	{
	}

	virtual
	~negative_normal_form_visitor()
	{
	}

	formula* result() const
	{
	  return result_;
	}

	void
	visit(atomic_prop* ap)
	{
	  formula* f = ap->clone();
	  if (negated_)
	    result_ = unop::instance(unop::Not, f);
	  else
	    result_ = f;
	}

	void
	visit(constant* c)
	{
	  // Negation of constants is taken care of in the constructor
	  // of unop::Not, so these cases should be caught by
	  // nenoform_recursively().
	  assert(!negated_);
	  result_ = c;
	  return;
	}

	void
	visit(unop* uo)
	{
	  formula* f = uo->child();
	  switch (uo->op())
	    {
	    case unop::Not:
	      // "Not"s should be caught by nenoform_recursively().
	      assert(!"Not should not occur");
	      //result_ = recurse_(f, negated_ ^ true);
	      return;
	    case unop::X:
	      /* !Xa == X!a */
	      result_ = unop::instance(unop::X, recurse(f));
	      return;
	    case unop::F:
	      /* !Fa == G!a */
	      result_ = unop::instance(negated_ ? unop::G : unop::F,
				       recurse(f));
	      return;
	    case unop::G:
	      /* !Ga == F!a */
	      result_ = unop::instance(negated_ ? unop::F : unop::G,
				       recurse(f));
	      return;
	    case unop::Closure:
	      result_ = unop::instance(negated_ ?
				       unop::NegClosure : unop::Closure,
				       recurse_(f, false));
	      return;
	    case unop::NegClosure:
	      result_ = unop::instance(negated_ ?
				       unop::Closure : uo->op(),
				       recurse_(f, false));
	      return;
	      /* !Finish(x), is not simplified */
	    case unop::Finish:
	      result_ = unop::instance(uo->op(), recurse_(f, false));
	      if (negated_)
		result_ = unop::instance(unop::Not, result_);
	      return;
	    }
	  /* Unreachable code.  */
	  assert(0);
	}

	void
	visit(bunop* bo)
	{
	  // !(a*) is not simplified
	  result_ = bunop::instance(bo->op(), recurse_(bo->child(), false),
				    bo->min(), bo->max());
	  if (negated_)
	    result_ = unop::instance(unop::Not, result_);
	}

	void
	visit(binop* bo)
	{
	  formula* f1 = bo->first();
	  formula* f2 = bo->second();
	  switch (bo->op())
	    {
	    case binop::Xor:
	      /* !(a ^ b) == a <=> b */
	      result_ = binop::instance(negated_ ? binop::Equiv : binop::Xor,
					recurse_(f1, false),
					recurse_(f2, false));
	      return;
	    case binop::Equiv:
	      /* !(a <=> b) == a ^ b */
	      result_ = binop::instance(negated_ ? binop::Xor : binop::Equiv,
					recurse_(f1, false),
					recurse_(f2, false));
	      return;
	    case binop::Implies:
	      if (negated_)
		/* !(a => b) == a & !b */
		result_ = multop::instance(multop::And,
					   recurse_(f1, false),
					   recurse_(f2, true));
	      else
		result_ = binop::instance(binop::Implies,
					  recurse(f1), recurse(f2));
	      return;
	    case binop::U:
	      /* !(a U b) == !a R !b */
	      result_ = binop::instance(negated_ ? binop::R : binop::U,
					recurse(f1), recurse(f2));
	      return;
	    case binop::R:
	      /* !(a R b) == !a U !b */
	      result_ = binop::instance(negated_ ? binop::U : binop::R,
					recurse(f1), recurse(f2));
	      return;
	    case binop::W:
	      /* !(a W b) == !a M !b */
	      result_ = binop::instance(negated_ ? binop::M : binop::W,
					recurse(f1), recurse(f2));
	      return;
	    case binop::M:
	      /* !(a M b) == !a W !b */
	      result_ = binop::instance(negated_ ? binop::W : binop::M,
					recurse(f1), recurse(f2));
	      return;
	    case binop::UConcat:
	      /* !(a []-> b) == a<>-> !b */
	      result_ = binop::instance(negated_ ?
					binop::EConcat : binop::UConcat,
					recurse_(f1, false), recurse(f2));
	      return;
	    case binop::EConcat:
	      /* !(a <>-> b) == a[]-> !b */
	      result_ = binop::instance(negated_ ?
					binop::UConcat : binop::EConcat,
					recurse_(f1, false), recurse(f2));
	      return;
	    case binop::EConcatMarked:
	      /* !(a <>-> b) == a[]-> !b */
	      result_ = binop::instance(negated_ ?
					binop::UConcat :
					binop::EConcatMarked,
					recurse_(f1, false), recurse(f2));
	      return;
	    }
	  /* Unreachable code.  */
	  assert(0);
	}

	void
	visit(automatop* ao)
	{
	  bool negated = negated_;
	  negated_ = false;
	  automatop::vec* res = new automatop::vec;
	  unsigned aos = ao->size();
	  for (unsigned i = 0; i < aos; ++i)
	    res->push_back(recurse(ao->nth(i)));
	  result_ = automatop::instance(ao->get_nfa(), res, negated);
	}

	void
	visit(multop* mo)
	{
	  multop::type op = mo->op();
	  /* !(a & b & c) == !a | !b | !c  */
	  /* !(a | b | c) == !a & !b & !c  */
	  if (negated_)
	    switch (op)
	      {
	      case multop::And:
		op = multop::Or;
		break;
	      case multop::Or:
		op = multop::And;
		break;
	      case multop::Concat:
	      case multop::Fusion:
	      case multop::AndNLM:
		break;
	      }
	  multop::vec* res = new multop::vec;
	  unsigned mos = mo->size();
	  switch (op)
	    {
	    case multop::And:
	    case multop::Or:
	      {
		for (unsigned i = 0; i < mos; ++i)
		  res->push_back(recurse(mo->nth(i)));
		result_ = multop::instance(op, res);
		break;
	      }
	    case multop::Concat:
	    case multop::Fusion:
	    case multop::AndNLM:
	      {
		for (unsigned i = 0; i < mos; ++i)
		  res->push_back(recurse_(mo->nth(i), false));
		result_ = multop::instance(op, res);
		assert(!negated_);
	      }
	    }
	}

	formula*
	recurse_(formula* f, bool negated)
	{
	  return const_cast<formula*>(nenoform_recursively(f, negated, cache_));
	}

	formula*
	recurse(formula* f)
	{
	  return recurse_(f, negated_);
	}

      protected:
	formula* result_;
	bool negated_;
	ltl_simplifier_cache* cache_;
      };


      const formula*
      nenoform_recursively(const formula* f,
			   bool negated,
			   ltl_simplifier_cache* c)
      {
	if (f->kind() == formula::UnOp)
	  {
	    const unop* uo = static_cast<const unop*>(f);
	    if (uo->op() == unop::Not)
	      {
		negated = !negated;
		f = uo->child();
	      }
	  }

	const formula* key = f;
	if (negated)
	  key = unop::instance(unop::Not, f->clone());
	const formula* result = c->lookup_nenoform(key);
	if (result)
	  goto done;

	if (key->is_in_nenoform()
	    || (c->options.nenoform_stop_on_boolean && key->is_boolean()))
	  {
	    result = key->clone();
	  }
	else
	  {
	    negative_normal_form_visitor v(negated, c);
	    const_cast<formula*>(f)->accept(v);
	    result = v.result();
	  }

	c->cache_nenoform(key, result);
      done:
	if (negated)
	  key->destroy();

	return result;
      }

    }



    const formula*
    simplify_recursively(const formula* f,
			 ltl_simplifier_cache* c)
    {
      const formula* result = c->lookup_simplified(f);
      if (result)
	return result;

      result = 0;// XXX

      c->cache_simplified(f, result);
      return result;
    }


    //////////////////////////////////////////////////////////////////////
    // ltl_simplifier

    ltl_simplifier::ltl_simplifier()
      : cache_(new ltl_simplifier_cache)
    {
    }

    ltl_simplifier::ltl_simplifier(ltl_simplifier_options& opt)
      : cache_(new ltl_simplifier_cache(opt))
    {
    }

    ltl_simplifier::~ltl_simplifier()
    {
      delete cache_;
    }

    formula*
    ltl_simplifier::simplify(const formula* f)
    {
      return const_cast<formula*>(simplify_recursively(f, cache_));
    }

    formula*
    ltl_simplifier::negative_normal_form(const formula* f, bool negated)
    {
      return const_cast<formula*>(nenoform_recursively(f, negated, cache_));
    }


  }
}
