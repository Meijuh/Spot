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

#include <iostream>
//#define TRACE
#ifdef TRACE
#define trace std::cerr
#else
#define trace while (0) std::cerr
#endif


#include "simplify.hh"
#include "misc/hash.hh"
#include "tgba/bdddict.hh"
#include "ltlast/allnodes.hh"
#include "ltlast/visitor.hh"
#include "ltlvisit/syntimpl.hh"
#include "ltlvisit/contain.hh"
#include "ltlvisit/tostring.hh"
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
      bdd_dict dict;
      ltl_simplifier_options options;
      syntactic_implication_cache syntimpl;
      language_containment_checker lcc;

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
	: lcc(&dict, true, true, false, false)
      {
      }

      ltl_simplifier_cache(ltl_simplifier_options opt)
	: options(opt), lcc(&dict, true, true, false, false)
      {
	opt.containment_checks |= opt.containment_checks_stronger;
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

      // Return true iff the option set (syntactic implication
      // or containment checks) allow to prove that f1 => f2.
      bool
      implication(const formula* f1, const formula* f2)
      {
	return (options.synt_impl && syntactic_implication(f1, f2))
	  || (options.containment_checks && contained(f1, f2));
      }

      // Return true if f1 => f2 syntactically
      bool
      syntactic_implication(const formula* f1, const formula* f2)
      {
	// We cannot run syntactic_implication on SERE formulae,
	// except on Boolean formulae.
	if (f1->is_sere_formula() && !f1->is_boolean())
	  return false;
	if (f2->is_sere_formula() && !f2->is_boolean())
	  return false;
	return syntimpl.syntactic_implication(f1, f2);
      }

      // Return true if f1 => f2
      bool
      contained(const formula* f1, const formula* f2)
      {
	if (!f1->is_psl_formula() || !f2->is_psl_formula())
	  return false;
	return lcc.contained(f1, f2);
      }

      // If right==false, true if !f1 => f2, false otherwise.
      // If right==true, true if f1 => !f2, false otherwise.
      bool
      syntactic_implication_neg(const formula* f1, const formula* f2,
				bool right)
      {
	// We cannot run syntactic_implication_neg on SERE formulae,
	// except on Boolean formulae.
	if (f1->is_sere_formula() && !f1->is_boolean())
	  return false;
	if (f2->is_sere_formula() && !f2->is_boolean())
	  return false;
	trace << "[SIN] Does " << (right ? "(" : "!(")
	      << to_string(f1) << ") implies "
	      << (right ? "!(" : "(") << to_string(f2) << ") ?"
	      << std::endl;
	if (syntimpl.syntactic_implication_neg(f1, f2, right))
	  {
	    trace << "[SIN] Yes" << std::endl;
	    return true;
	  }
	else
	  {
	    trace << "[SIN] No" << std::endl;
	    return false;
	  }
      }

      // Return true if f1 => !f2
      bool contained_neg(const formula* f1, const formula* f2)
      {
	if (!f1->is_psl_formula() || !f2->is_psl_formula())
	  return false;
	trace << "[CN] Does (" << to_string(f1) << ") implies !("
	      << to_string(f2) << ") ?" << std::endl;
	if (lcc.contained_neg(f1, f2))
	  {
	    trace << "[CN] Yes" << std::endl;
	    return true;
	  }
	else
	  {
	    trace << "[CN] No" << std::endl;
	    return false;
	  }
      }

      // Return true if f1 => !f2
      bool neg_contained(const formula* f1, const formula* f2)
      {
	if (!f1->is_psl_formula() || !f2->is_psl_formula())
	  return false;
	trace << "[NC] Does (" << to_string(f1) << ") implies !("
	      << to_string(f2) << ") ?" << std::endl;
	if (lcc.neg_contained(f1, f2))
	  {
	    trace << "[NC] Yes" << std::endl;
	    return true;
	  }
	else
	  {
	    trace << "[NC] No" << std::endl;
	    return false;
	  }
      }

      // Return true iff the option set (syntactic implication
      // or containment checks) allow to prove that
      //   - !f2 => f2   (case where right=false)
      //   - f1 => !f2   (case where right=true)
      bool
      implication_neg(const formula* f1, const formula* f2, bool right)
      {
	trace << "[IN] Does " << (right ? "(" : "!(")
	      << to_string(f1) << ") implies "
	      << (right ? "!(" : "(") << to_string(f2) << ") ?"
	      << std::endl;
	if ((options.synt_impl && syntactic_implication_neg(f1, f2, right))
	    || (options.containment_checks && right && contained_neg(f1, f2))
	    || (options.containment_checks && !right && neg_contained(f1, f2)))
	  {
	    trace << "[IN] Yes" << std::endl;
	    return true;
	  }
	else
	  {
	    trace << "[IN] No" << std::endl;
	    return false;
	  }
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
      //////////////////////////////////////////////////////////////////////
      //
      //  NEGATIVE_NORMAL_FORM_VISITOR
      //
      //////////////////////////////////////////////////////////////////////

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

      //////////////////////////////////////////////////////////////////////
      //
      //  SIMPLIFY_VISITOR
      //
      //////////////////////////////////////////////////////////////////////

      // Forward declaration.
      formula*
      simplify_recursively(const formula* f, ltl_simplifier_cache* c);

      constant*
      is_constant(formula* f)
      {
	if (f->kind() != formula::Constant)
	  return 0;
	return static_cast<constant*>(f);
      }

      unop*
      is_unop(formula* f, unop::type op)
      {
	if (f->kind() != formula::UnOp)
	  return 0;
	unop* uo = static_cast<unop*>(f);
	if (uo->op() != op)
	  return 0;
	return uo;
      }

      unop*
      is_X(formula* f)
      {
	return is_unop(f, unop::X);
      }

      unop*
      is_F(formula* f)
      {
	return is_unop(f, unop::F);
      }

      unop*
      is_G(formula* f)
      {
	return is_unop(f, unop::G);
      }

      unop*
      is_GF(formula* f)
      {
	unop* op = is_G(f);
	if (!op)
	  return 0;
	return is_F(op->child());
      }

      unop*
      is_FG(formula* f)
      {
	unop* op = is_F(f);
	if (!op)
	  return 0;
	return is_G(op->child());
      }

      binop*
      is_binop(formula* f, binop::type op)
      {
	if (f->kind() != formula::BinOp)
	  return 0;
	binop* bo = static_cast<binop*>(f);
	if (bo->op() != op)
	  return 0;
	return bo;
      }

      binop*
      is_U(formula* f)
      {
	return is_binop(f, binop::U);
      }

      formula*
      unop_multop(unop::type uop, multop::type mop, multop::vec* v)
      {
	return unop::instance(uop, multop::instance(mop, v));
      }

      formula*
      unop_unop_multop(unop::type uop1, unop::type uop2, multop::type mop,
		       multop::vec* v)
      {
	return unop::instance(uop1, unop_multop(uop2, mop, v));
      }

      formula*
      unop_unop(unop::type uop1, unop::type uop2, formula* f)
      {
	return unop::instance(uop1, unop::instance(uop2, f));
      }

      struct mospliter
      {
	enum what { Split_GF = (1 << 0),
		    Strip_GF = (1 << 1) | (1 << 0),
		    Split_FG = (1 << 2),
		    Strip_FG = (1 << 3) | (1 << 2),
		    Split_F = (1 << 4),
		    Strip_F = (1 << 5) | (1 << 4),
		    Split_G = (1 << 6),
		    Strip_G = (1 << 7) | (1 << 6),
		    Strip_X = (1 << 8),
		    Split_U_or_W = (1 << 9),
		    Split_R_or_M = (1 << 10),
		    Split_EventUniv = (1 << 11),
		    Split_Event = (1 << 12),
		    Split_Univ = (1 << 13),
		    Split_Bool = (1 << 14)
	};

	void init()
	{
	  res_GF = (split_ & Split_GF) ? new multop::vec : 0;
	  res_FG = (split_ & Split_FG) ? new multop::vec : 0;
	  res_F = (split_ & Split_F) ? new multop::vec : 0;
	  res_G = (split_ & Split_G) ? new multop::vec : 0;
	  res_X = (split_ & Strip_X) ? new multop::vec : 0;
	  res_U_or_W = (split_ & Split_U_or_W) ? new multop::vec : 0;
	  res_R_or_M = (split_ & Split_R_or_M) ? new multop::vec : 0;
	  res_EventUniv = (split_ & Split_EventUniv) ? new multop::vec : 0;
	  res_Event = (split_ & Split_Event) ? new multop::vec : 0;
	  res_Univ = (split_ & Split_Univ) ? new multop::vec : 0;
	  res_Bool = (split_ & Split_Bool) ? new multop::vec : 0;
	  res_other = new multop::vec;
	}

	void process(formula* f)
	{
	  switch (f->kind())
	    {
	    case formula::UnOp:
	      {
		unop* uo = static_cast<unop*>(f);
		formula* c = uo->child();
		switch (uo->op())
		  {
		  case unop::X:
		    if (res_X)
		      {
			res_X->push_back(c->clone());
			return;
		      }
		    break;
		  case unop::F:
		    if (res_FG)
		      {
			unop* cc = is_G(c);
			if (cc)
			  {
			    res_FG->push_back(((split_ & Strip_FG) == Strip_FG
					       ? cc->child() : f)->clone());
			    return;
			  }
		      }
		    if (res_F)
		      {
			res_F->push_back(((split_ & Strip_F) == Strip_F
					  ? c : f)->clone());
			return;
		      }
		    break;
		  case unop::G:
		    if (res_GF)
		      {
			unop* cc = is_F(c);
			if (cc)
			  {
			    res_GF->push_back(((split_ & Strip_GF) == Strip_GF
					       ? cc->child() : f)->clone());
			    return;
			  }
		      }
		    if (res_G)
		      {
			res_G->push_back(((split_ & Strip_G) == Strip_G
					  ? c : f)->clone());
			return;
		      }
		    break;
		  default:
		    break;
		  }
	      }
	      break;
	    case formula::BinOp:
	      {
		binop* bo = static_cast<binop*>(f);
		switch (bo->op())
		  {
		  case binop::U:
		  case binop::W:
		    if (res_U_or_W)
		      {
			res_U_or_W->push_back(bo->clone());
			return;
		      }
		    break;
		  case binop::R:
		  case binop::M:
		    if (res_R_or_M)
		      {
			res_R_or_M->push_back(bo->clone());
			return;
		      }
		    break;
		  default:
		    break;
		  }
	      }
	      break;
	    default:
	      if (res_Bool && f->is_boolean())
		{
		  res_Bool->push_back(f->clone());
		  return;
		}
	      break;
	    }
	  if (c_->options.event_univ)
	    {
	      bool e = f->is_eventual();
	      bool u = f->is_universal();
	      if (res_EventUniv && e && u)
		{
		  res_EventUniv->push_back(f->clone());
		  return;
		}
	      if (res_Event && e)
		{
		  res_Event->push_back(f->clone());
		  return;
		}
	      if (res_Univ && u)
		{
		  res_Univ->push_back(f->clone());
		  return;
		}
	    }

	  res_other->push_back(f->clone());
	}

	mospliter(unsigned split, multop::vec* v, ltl_simplifier_cache* cache)
	  : split_(split), c_(cache)
	{
	  init();
	  multop::vec::const_iterator end = v->end();
	  for (multop::vec::const_iterator i = v->begin(); i < end; ++i)
	    {
	      if (*i) // skip null pointers left by previous simplifications
		{
		  process(*i);
		  (*i)->destroy();
		}
	    }
	  delete v;
	}

	mospliter(unsigned split, multop* mo, ltl_simplifier_cache* cache)
	  : split_(split), c_(cache)
	{
	  init();
	  unsigned mos = mo->size();
	  for (unsigned i = 0; i < mos; ++i)
	    {
	      formula* f = simplify_recursively(mo->nth(i), cache);
	      process(f);
	      f->destroy();
	    }
	  mo->destroy();
	}

	multop::vec* res_GF;
	multop::vec* res_FG;
	multop::vec* res_F;
	multop::vec* res_G;
	multop::vec* res_X;
	multop::vec* res_U_or_W;
	multop::vec* res_R_or_M;
	multop::vec* res_Event;
	multop::vec* res_Univ;
	multop::vec* res_EventUniv;
	multop::vec* res_Bool;
	multop::vec* res_other;
	unsigned split_;
	ltl_simplifier_cache* c_;
      };

      class simplify_visitor: public visitor
      {
      public:

	simplify_visitor(ltl_simplifier_cache* cache)
	  : c_(cache), opt_(cache->options)
	{
	}

	virtual ~simplify_visitor()
	{
	}

	formula*
	result() const
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
	  result_ = c;
	}

	void
	visit(bunop* bo)
	{
	  result_ = bunop::instance(bo->op(), recurse(bo->child()),
				    bo->min(), bo->max());
	}

	void
	visit(unop* uo)
	{
	  result_ = recurse(uo->child());

	  unop::type op = uo->op();
	  switch (op)
	    {
	    case unop::Not:
	      break;

	    case unop::X:
	      // X(constant) = constant is a trivial identity, but if
	      // the constant has been constructed by recurse() this
	      // identity has not been applied.
	      if (is_constant(result_))
		  return;

	      // Xf = f if f is both eventual and universal.
	      if (result_->is_universal() && result_->is_eventual())
		{
		  if (opt_.event_univ)
		    return;
		  // If EventUniv simplification is disabled, use
		  // only the following basic rewriting rules:
		  //   XGF(f) = GF(f) and XFG(f) = FG(f)
		  // The former comes from Somenzi&Bloem (CAV'00).
		  // It's not clear why they do not list the second.
		  if (opt_.reduce_basics &&
		      (is_GF(result_) || is_FG(result_)))
		    return;
		}


	      // If Xa = a, keep only a.
	      if (opt_.containment_checks_stronger
		  && c_->lcc.equal(result_, uo))
		return;

	      // Disabled: X(f1 & GF(f2)) = X(f1) & GF(f2)
	      // Disabled: X(f1 | GF(f2)) = X(f1) | GF(f2)
	      // Disabled: X(f1 & FG(f2)) = X(f1) & FG(f2)
	      // Disabled: X(f1 | FG(f2)) = X(f1) | FG(f2)
	      // The above make more sense when reversed,
	      // so see them in the And and Or rewritings.
	      break;

	    case unop::F:
	      // F(constant) = constant is a trivial identity, but if
	      // the constant has been constructed by recurse() this
	      // identity has not been applied.
	      if (is_constant(result_))
		  return;

	      // If f is a pure eventuality formula then F(f)=f.
	      if (opt_.event_univ && result_->is_eventual())
		return;

	      if (opt_.reduce_basics)
		{
		  // F(a U b) = F(b)
		  binop* bo = is_U(result_);
		  if (bo)
		    {
		      formula* r =
			unop::instance(unop::F, bo->second()->clone());
		      bo->destroy();
		      result_ = recurse_destroy(r);
		      return;
		    }

		  // FX(a) = XF(a)
		  {
		    unop* u = is_X(result_);
		    if (u)
		      {
			formula* res =
			  unop_unop(unop::X, unop::F, u->child()->clone());
			u->destroy();
			// FXX(a) = XXF(a) ...
			// FXG(a) = XFG(a) = FG(a) ...
			result_ = recurse_destroy(res);
			return;
		      }
		  }
		}

	      // if Fa => a, keep a.
	      if (opt_.containment_checks_stronger
		  && c_->lcc.contained(uo, result_))
		return;

	      // Disabled: F(f1 & GF(f2)) = F(f1) & GF(f2)
	      //
	      // As is, these two formulae are translated into
	      // equivalent Büchi automata so the rewriting is
	      // useless.
	      //
	      // However when taken in a larger formula such as F(f1
	      // & GF(f2)) | F(a & GF(b)), this rewriting used to
	      // produce (F(f1) & GF(f2)) | (F(a) & GF(b)), missing
	      // the opportunity to apply the F(E1)|F(E2) = F(E1|E2)
	      // rule which really helps the translation. F((f1 &
	      // GF(f2)) | (a & GF(b))) is indeed easier to translate.
	      //
	      // So let's not consider this rewriting rule.
	      break;

	    case unop::G:
	      // G(constant) = constant is a trivial identity, but if
	      // the constant has been constructed by recurse() this
	      // identity has not been applied.
	      if (is_constant(result_))
		  return;

	      // If f is a pure universality formula then G(f)=f.
	      if (opt_.event_univ && result_->is_universal())
		return;

	      if (opt_.reduce_basics)
		{

		  // G(a R b) = G(b)
		  if (result_->kind() == formula::BinOp)
		    {
		      binop* bo = static_cast<binop*>(result_);
		      if (bo->op() == binop::R)
			{
			  formula* r =
			    unop::instance(unop::G, bo->second()->clone());
			  bo->destroy();
			  result_ = recurse_destroy(r);
			  return;
			}
		    }

		  // GX(a) = XG(a)
		  if (result_->kind() == formula::UnOp)
		    {
		      unop* u = static_cast<unop*>(result_);
		      if (u->op() == unop::X)
			{
			  formula* res =
			    unop_unop(unop::X, unop::G, u->child()->clone());
			  u->destroy();
			  // GXX(a) = XXG(a) ...
			  // GXF(a) = XGF(a) = GF(a) ...
			  result_ = recurse_destroy(res);
			  return;
			}
		    }

		  // G(f1|f2|GF(f3)|GF(f4)|f5|f6) =
		  //                        G(f1|f2) | GF(f3|f4) | f5 | f6
		  // if f5 and f6 are both eventual and universal.
		  if (result_->kind() == formula::MultOp)
		    {
		      multop* mo = static_cast<multop*>(result_);
		      if (mo->op() == multop::Or)
			{
			  mo->clone();
			  mospliter s(mospliter::Strip_GF |
				      mospliter::Split_EventUniv,
				      mo, c_);
			  s.res_EventUniv->
			    push_back(unop_multop(unop::G, multop::Or,
						  s.res_other));
			  s.res_EventUniv->
			    push_back(unop_unop_multop(unop::G, unop::F,
						       multop::Or, s.res_GF));
			  result_ = multop::instance(multop::Or,
						     s.res_EventUniv);
			  if (result_ != uo)
			    {
			      mo->destroy();
			      result_ = recurse_destroy(result_);
			      return;
			    }
			  else
			    {
			      // Revert to the previous value of result_,
			      // for the next simplification.
			      result_->destroy();
			      result_ = mo;
			    }
			}
		    }
		}
	      // if a => Ga, keep a.
	      if (opt_.containment_checks_stronger
		  && c_->lcc.contained(result_, uo))
		return;
	      break;
	    case unop::Finish:
	    case unop::Closure:
	    case unop::NegClosure:
	      // No simplification
	      break;
	    }
	  result_ = unop::instance(op, result_);
	}

	void
	visit(binop* bo)
	{
	  binop::type op = bo->op();

	  formula* b = recurse(bo->second());

	  if (opt_.event_univ)
	    {
	      /* If b is a pure eventuality formula then a U b = b.
		 If b is a pure universality formula a R b = b. */
	      if ((b->is_eventual() && (op == binop::U))
		  || (b->is_universal() && (op == binop::R)))
		{
		  result_ = b;
		  return;
		}
	    }

	  formula* a = recurse(bo->first());

	  if (opt_.event_univ)
	    {
	      /* If a is a pure eventuality formula then a M b = a & b.
		 If a is a pure universality formula a W b = a|b. */
	      if (a->is_eventual() && (op == binop::M))
		{
		  formula* tmp = multop::instance(multop::And, a, b);
		  result_ = recurse(tmp);
		  tmp->destroy();
		  return;
		}
	      if (a->is_universal() && (op == binop::W))
		{
		  formula* tmp = multop::instance(multop::Or, a, b);
		  result_ = recurse(tmp);
		  tmp->destroy();
		  return;
		}
	    }

	  // Inclusion-based rules
	  if (opt_.synt_impl | opt_.containment_checks)
	    {
	      switch (op)
		{
		case binop::Xor:
		case binop::Equiv:
		case binop::Implies:
		  assert(!"operator not supported for implication rules");
		  return;
		case binop::UConcat:
		case binop::EConcat:
		case binop::EConcatMarked:
		  break;

		case binop::U:
		  // if a => b, then a U b = b
		  // if (a U b) => b, then a U b = b (for stronger containment)
		  if (c_->implication(a, b)
		      || (opt_.containment_checks_stronger
			  && c_->contained(bo, b)))
		    {
		      a->destroy();
		      result_ = b;
		      return;
		    }
		  // if !a => b, then a U b = Fb
		  if (c_->implication_neg(a, b, false))
		    {
		      a->destroy();
		      result_ =
			recurse_destroy(unop::instance(unop::F, b));
		      return;
		    }
		  // if a => b, then a U (b U c) = (b U c)
		  // if a => b, then a U (b W c) = (b W c)
		  if (b->kind() == formula::BinOp)
		    {
		      binop* bo = static_cast<binop*>(b);
		      if ((bo->op() == binop::U || bo->op() == binop::W)
			  && c_->implication(a, bo->first()))
			{
			  a->destroy();
			  result_ = b;
			  return;
			}
		    }
		  break;

		case binop::R:
		  // if b => a, then a R b = b
		  if (c_->implication(b, a))
		    {
		      a->destroy();
		      result_ = b;
		      return;
		    }
		  // if b => !a, then a R b = Gb
		  if (c_->implication_neg(b, a, true))
		    {
		      a->destroy();
		      result_ = unop::instance(unop::G, b);
		      return;
		    }
		  if (b->kind() == formula::BinOp)
		    {
		      // if b => a, then a R (b R c) = b R c
		      // if b => a, then a R (b M c) = b M c
		      binop* bo = static_cast<binop*>(b);
		      if ((bo->op() == binop::R || bo->op() == binop::M)
			  && c_->implication(bo->first(), a))
			{
			  a->destroy();
			  result_ = b;
			  return;
			}

		      // if a => b, then a R (b R c) = a R c
		      if (bo->op() == binop::R
			  && c_->implication(a, bo->first()))
			{
			  b->destroy();
			  result_ = recurse_destroy
			    (binop::instance(binop::R, a,
					     bo->second()->clone()));
			  return;
			}
		    }
		  break;

		case binop::W:
		  // if a => b, then a W b = b
		  // if a W b => b, then a W b = b (for stronger containment)
		  if (c_->implication(a, b)
		      || (opt_.containment_checks_stronger
			  && c_->contained(bo, b)))
		    {
		      a->destroy();
		      result_ = b;
		      return;
		    }
		  // if !a => b then a W b = 1
		  if (c_->implication_neg(a, b, false))
		    {
		      a->destroy();
		      b->destroy();
		      result_ = constant::true_instance();
		      return;
		    }
		  // if a => b, then a W (b W c) = (b W c)
		  if (b->kind() == formula::BinOp)
		    {
		      binop* bo = static_cast<binop*>(b);
		      if (bo->op() == binop::W
			  && c_->implication(a, bo->first()))
			{
			  a->destroy();
			  result_ = b;
			  return;
			}
		    }
		  break;

		case binop::M:
		  // if b => a, then a M b = b
		  if (c_->implication(b, a))
		    {
		      a->destroy();
		      result_ = b;
		      return;
		    }
		  // if b => !a, then a M b = 0
		  if (c_->implication_neg(b, a, true))
		    {
		      a->destroy();
		      b->destroy();
		      result_ = constant::false_instance();
		      return;
		    }
		  if (b->kind() == formula::BinOp)
		    {
		      // if b => a, then a M (b M c) = b M c
		      binop* bo = static_cast<binop*>(b);
		      if (bo->op() == binop::M
			  && c_->implication(bo->first(), a))
			{
			  result_ = b;
			  a->destroy();
			  return;
			}

		      // if a => b, then a M (b M c) = a M c
		      // if a => b, then a M (b R c) = a M c
		      if ((bo->op() == binop::M || bo->op() == binop::R)
			  && c_->implication(a, bo->first()))
			{
			  b->destroy();
			  result_ = recurse_destroy
			    (binop::instance(binop::M, a,
					     bo->second()->clone()));
			  return;
			}
		    }
		  break;
		}
	    }

	  if (!opt_.reduce_basics)
	    {
	      result_ = binop::instance(op, a, b);
	      return;
	    }

	  // Rewrite U,R,W,M as F or G when possible.
	  switch (op)
	    {
	    case binop::U:
	      // true U b == F(b)
	      if (a == constant::true_instance())
		{
		  result_ = recurse_destroy(unop::instance(unop::F, b));
		  return;
		}
	      break;
	    case binop::R:
	      // false R b == G(b)
	      if (a == constant::false_instance())
		{
		  result_ = recurse_destroy(unop::instance(unop::G, b));
		  return;
		}
	      break;
	    case binop::W:
	      // a W false == G(a)
	      if (b == constant::false_instance())
		{
		  result_ = recurse_destroy(unop::instance(unop::G, a));
		  return;
		}
	      break;
	    case binop::M:
	      // a M true == F(a)
	      if (b == constant::false_instance())
		{
		  result_ = recurse_destroy(unop::instance(unop::F, a));
		  return;
		}
	      break;
	    default:
	      break;
	    }

	  switch (op)
	    {
	    case binop::W:
	    case binop::M:
	    case binop::U:
	    case binop::R:
	      {
		// These are trivial identities:
		// a U false = false
		// a U true = true
		// a R false = false
		// a R true = true
		// a W true = true
		// a M false = false
		if (is_constant(b))
		  {
		    result_ = b;
		    a->destroy();
		    return;
		  }

		// Same effect as dynamic_cast<unop*>, only faster.
		unop* fu1 =
		  (a->kind() == formula::UnOp) ? static_cast<unop*>(a) : 0;
		unop* fu2 =
		  (b->kind() == formula::UnOp) ? static_cast<unop*>(b) : 0;

		// X(a) U X(b) = X(a U b)
		// X(a) R X(b) = X(a R b)
		// X(a) W X(b) = X(a W b)
		// X(a) M X(b) = X(a M b)
		if (fu1 && fu2
		    && fu1->op() == unop::X
		    && fu2->op() == unop::X)
		  {
		    formula* bin = binop::instance(op,
						   fu1->child()->clone(),
						   fu2->child()->clone());
		    a->destroy();
		    b->destroy();
		    result_ = recurse_destroy(unop::instance(unop::X, bin));
		    return;
		  }

		if (op == binop::U || op == binop::W)
		  {
		    // a U Ga = Ga
		    // a W Ga = Ga
		    if (fu2 && fu2->op() == unop::G && fu2->child() == a)
		      {
			a->destroy();
			result_ = b;
			return;
		      }

		    // a U (b | c | G(a)) = a W (b | c)
		    // a W (b | c | G(a)) = a W (b | c)
		    if (b->kind() == formula::MultOp)
		      {
			multop* fm2 = static_cast<multop*>(b);
			if (fm2->op() == multop::Or)
			  {
			    int s = fm2->size();
			    for (int i = 0; i < s; ++i)
			      {
				if (fm2->nth(i)->kind() != formula::UnOp)
				  continue;
				unop* c = static_cast<unop*>(fm2->nth(i));
				if (c->op() == unop::G && c->child() == a)
				  {
				    multop::vec* v = new multop::vec;
				    v->reserve(s - 1);
				    int j;
				    for (j = 0; j < i; ++j)
				      v->push_back(fm2->nth(j)->clone());
				    // skip j=i
				    for (++j; j < s; ++j)
				      v->push_back(fm2->nth(j)->clone());
				    b->destroy();
				    result_ = recurse_destroy(binop::instance
				      (binop::W, a,
				       multop::instance(multop::Or, v)));
				    return;
				  }
			      }
			  }
		      }
		  }
		else if (op == binop::M || op == binop::R)
		  {
		    // a R Fa = Fa
		    // a M Fa = Fa
		    if (fu2 && fu2->op() == unop::F && fu2->child() == a)
		      {
			a->destroy();
			result_ = b;
			return;
		      }

		    // a R (b & c & F(a)) = a M b
		    // a M (b & c & F(a)) = a M b
		    if (b->kind() == formula::MultOp)
		      {
			multop* fm2 = static_cast<multop*>(b);
			if (fm2->op() == multop::And)
			  {
			    int s = fm2->size();
			    for (int i = 0; i < s; ++i)
			      {
				if (fm2->nth(i)->kind() != formula::UnOp)
				  continue;
				unop* c = static_cast<unop*>(fm2->nth(i));
				if (c->op() == unop::F && c->child() == a)
				  {
				    multop::vec* v = new multop::vec;
				    v->reserve(s - 1);
				    int j;
				    for (j = 0; j < i; ++j)
				      v->push_back(fm2->nth(j)->clone());
				    // skip j=i
				    for (++j; j < s; ++j)
				      v->push_back(fm2->nth(j)->clone());
				    b->destroy();
				    result_ = recurse_destroy(binop::instance
				      (binop::M, a,
				       multop::instance(multop::And, v)));
				    return;
				  }
			      }
			  }
		      }
		  }
	      }
	    case binop::Xor:
	    case binop::Equiv:
	    case binop::Implies:
	    case binop::EConcat:
	    case binop::UConcat:
	    case binop::EConcatMarked:
	      // No simplification... Yet?
	      break;
	    }

	  result_ = binop::instance(op, a, b);
	}

	void
	visit(automatop*)
	{
	  assert(0);
	}

	void
	visit(multop* mo)
	{
	  unsigned mos = mo->size();
	  multop::vec* res = new multop::vec;

	  for (unsigned i = 0; i < mos; ++i)
	    res->push_back(recurse(mo->nth(i)));

	  multop::type op = mo->op();

	  if ((opt_.synt_impl | opt_.containment_checks)
	      && (op != multop::Concat)
	      && (op != multop::Fusion))
	    {
	      bool is_and = op != multop::Or; // And or AndNLM
	      constant* neutral = is_and
		? constant::false_instance() : constant::true_instance();

	      multop::vec::iterator f1 = res->begin();

	      while (f1 != res->end())
		{
		  multop::vec::iterator f2 = f1;
		  ++f2
;
		  while (f2 != res->end())
		    {
		      assert(f1 != f2);
		      // if f1 => f2, then f1 | f2 = f2
		      // if f2 => f1, then f1 & f2 = f2
		      if ((op == multop::Or && c_->implication(*f1, *f2))
			  || (op == multop::And && c_->implication(*f2, *f1)))
			{
			  // Remove f1.
			  (*f1)->destroy();
			  *f1 = 0;
			  ++f1;
			  break;
			}
		      // if f2 => f1, then f1 | f2 = f1
		      // if f1 => f2, then f1 & f2 = f1
		      else if ((op == multop::Or && c_->implication(*f2, *f1))
			       || (op == multop::And
				   && c_->implication(*f1, *f2)))
			{
			  // Remove f2.
			  (*f2)->destroy();
			  // replace it by the last element from the array.
			  // and start again at the current position.
			  if (f2 != --res->end())
			    {
			      *f2 = res->back();
			      res->pop_back();
			      continue;
			    }
			  else
			    {
			      res->pop_back();
			      break;
			    }
			}
		      // if f1 => !f2, then f1 & f2 = false
		      // if !f1 => f2, then f1 | f2 = true
		      else if (c_->implication_neg(*f1, *f2, is_and))
			{
			  for (multop::vec::iterator j = res->begin();
			       j != res->end(); j++)
			    if (*j)
			      (*j)->destroy();
			  delete res;
			  result_ = neutral;
			  return;
			}
		      else
			++f2;
		    }
		  ++f1;
		}
	    }

	  assert(!res->empty());

	  if (opt_.reduce_basics)
	    {
	      switch (op)
		{
		case multop::And:
		  {
		    // Gather all operands by type.
		    mospliter s(mospliter::Strip_X |
				mospliter::Strip_FG |
				mospliter::Strip_G |
				mospliter::Split_F |
				mospliter::Split_U_or_W |
				mospliter::Split_R_or_M |
				mospliter::Split_EventUniv,
				res, c_);
		    // FG(a) & FG(b) = FG(a & b)
		    formula* allFG = unop_unop_multop(unop::F, unop::G,
						      multop::And, s.res_FG);
		    // Xa & Xb = X(a & b)
		    // Xa & Xb & FG(c) = X(a & b & FG(c))
		    // For Universal&Eventual formulae f1...fn we also have:
		    // Xa & Xb & f1...fn = X(a & b & f1...fn)
		    if (!s.res_X->empty())
		      {
			s.res_X->push_back(allFG);
			allFG = 0;
			s.res_X->insert(s.res_X->begin(),
					s.res_EventUniv->begin(),
					s.res_EventUniv->end());
		      }
		    else
		      // We don't rewrite Ga & f1...fn = G(a & f1..fn)
		      // similarly to what we do in the unop::Or case
		      // as it is not clear what we'd gain by doing so.
		      {
			s.res_other->insert(s.res_other->begin(),
					    s.res_EventUniv->begin(),
					    s.res_EventUniv->end());
		      }
		    delete s.res_EventUniv;

		    // Xa & Xb & f1...fn = X(a & b & f1...fn)
		    // is built at the end of this multop::And case.
		    // G(a) & F(b) = G(a & b)
		    // is built at the end of this multop::And case.

		    // The following three loops perform these rewritings:
		    // (a U b) & (c U b) = (a & c) U b
		    // (a U b) & (c W b) = (a & c) U b
		    // (a W b) & (c W b) = (a & c) W b
		    // (a R b) & (a R c) = a R (b & c)
		    // (a R b) & (a M c) = a M (b & c)
		    // (a M b) & (a M c) = a M (b & c)
		    // F(a) & (a R b) = a M b
		    // F(a) & (a M b) = a M b
		    // F(b) & (a W b) = a U b
		    // F(b) & (a U b) = a U b
		    typedef Sgi::hash_map<formula*, multop::vec::iterator,
					  ptr_hash<formula> > fmap_t;
		    fmap_t uwmap; // associates "b" to "a U b" or "a W b"
		    fmap_t rmmap; // associates "a" to "a R b" or "a M b"
		    // (a U b) & (c U b) = (a & c) U b
		    // (a U b) & (c W b) = (a & c) U b
		    // (a W b) & (c W b) = (a & c) W b
		    for (multop::vec::iterator i = s.res_U_or_W->begin();
			 i != s.res_U_or_W->end(); ++i)
		      {
			binop* bo = static_cast<binop*>(*i);
			formula* b = bo->second();
			fmap_t::iterator j = uwmap.find(b);
			if (j == uwmap.end())
			  {
			    // First occurrence.
			    uwmap[b] = i;
			    continue;
			  }
			// We already have one occurrence.  Merge them.
			binop* old = static_cast<binop*>(*j->second);
			binop::type op = binop::W;
			if (bo->op() == binop::U
			    || old->op() == binop::U)
			  op = binop::U;
			formula* fst_arg =
			  multop::instance(multop::And,
					   old->first()->clone(),
					   bo->first()->clone());
			*j->second = binop::instance(op, fst_arg, b->clone());
			assert((*j->second)->kind() == formula::BinOp);
			*i = 0;
			old->destroy();
			bo->destroy();
		      }
		    // (a R b) & (a R c) = a R (b & c)
		    // (a R b) & (a M c) = a M (b & c)
		    // (a M b) & (a M c) = a M (b & c)
		    for (multop::vec::iterator i = s.res_R_or_M->begin();
			 i != s.res_R_or_M->end(); ++i)
		      {
			binop* bo = static_cast<binop*>(*i);
			formula* a = bo->first();
			fmap_t::iterator j = rmmap.find(a);
			if (j == rmmap.end())
			  {
			    // First occurrence.
			    rmmap[a] = i;
			    continue;
			  }
			// We already have one occurrence.  Merge them.
			binop* old = static_cast<binop*>(*j->second);
			binop::type op = binop::R;
			if (bo->op() == binop::M
			    || old->op() == binop::M)
			  op = binop::M;
			formula* snd_arg =
			  multop::instance(multop::And,
					   old->second()->clone(),
					   bo->second()->clone());
			*j->second = binop::instance(op, a->clone(), snd_arg);
			assert((*j->second)->kind() == formula::BinOp);
			*i = 0;
			old->destroy();
			bo->destroy();
		      }
		    // F(a) & (a R b) = a M b
		    // F(a) & (a M b) = a M b
		    // F(b) & (a W b) = a U b
		    // F(b) & (a U b) = a U b
		    for (multop::vec::iterator i = s.res_F->begin();
			 i != s.res_F->end(); ++i)
		      {
			bool superfluous = false;
			unop* uo = static_cast<unop*>(*i);
			formula* c = uo->child();

			fmap_t::iterator j = uwmap.find(c);
			if (j != uwmap.end())
			  {
			    superfluous = true;
			    binop* bo = static_cast<binop*>(*j->second);
			    if (bo->op() == binop::W)
			      {
				*j->second =
				  binop::instance(binop::U,
						  bo->first()->clone(),
						  bo->second()->clone());
				assert((*j->second)->kind() == formula::BinOp);
				bo->destroy();
			      }
			  }
			j = rmmap.find(c);
			if (j != rmmap.end())
			  {
			    superfluous = true;
			    binop* bo = static_cast<binop*>(*j->second);
			    if (bo->op() == binop::R)
			      {
				*j->second =
				  binop::instance(binop::M,
						  bo->first()->clone(),
						  bo->second()->clone());
				assert((*j->second)->kind() == formula::BinOp);
				bo->destroy();
			      }
			  }
			if (superfluous)
			  {
			    (*i)->destroy();
			    *i = 0;
			  }
		      }

		    s.res_other->reserve(s.res_other->size()
					 + s.res_F->size()
					 + s.res_U_or_W->size()
					 + s.res_R_or_M->size()
					 + 3);
		    s.res_other->insert(s.res_other->end(),
					s.res_F->begin(),
					s.res_F->end());
		    delete s.res_F;
		    s.res_other->insert(s.res_other->end(),
					s.res_U_or_W->begin(),
					s.res_U_or_W->end());
		    delete s.res_U_or_W;
		    s.res_other->insert(s.res_other->end(),
					s.res_R_or_M->begin(),
					s.res_R_or_M->end());
		    delete s.res_R_or_M;

		    // Those "G" formulae that are eventual can be
		    // postponed inside the X term if there is one.
		    //
		    // In effect we rewrite
		    //   Xa&Xb&GFc&GFd&Ge as X(a&b&G(Fc&Fd))&Ge
		    if (!s.res_X->empty())
		      {
			multop::vec* event = new multop::vec;
			for (multop::vec::iterator i = s.res_G->begin();
			     i != s.res_G->end(); ++i)
			  if ((*i)->is_eventual())
			    {
			      event->push_back(*i);
			      *i = 0; // Remove it from res_G.
			    }
			s.res_X->push_back(unop_multop(unop::G,
						       multop::And, event));
		      }

		    // G(a) & G(b) & ... = G(a & b & ...)
		    formula* allG = unop_multop(unop::G, multop::And, s.res_G);
		    // Xa & Xb & ... = X(a & b & ...)
		    formula* allX = unop_multop(unop::X, multop::And, s.res_X);

		    s.res_other->push_back(allX);
		    s.res_other->push_back(allG);
		    s.res_other->push_back(allFG);
		    result_ = multop::instance(multop::And, s.res_other);
		    // If we altered the formula in some way, process
		    // it another time.
		    if (result_ != mo)
		      result_ = recurse_destroy(result_);
		    return;
		  }
		case multop::Or:
		  {
		    // Gather all operand by type.
		    mospliter s(mospliter::Strip_X |
				mospliter::Strip_GF |
				mospliter::Strip_F |
				mospliter::Split_G |
				mospliter::Split_U_or_W |
				mospliter::Split_R_or_M |
				mospliter::Split_EventUniv,
				res, c_);
		    // GF(a) | GF(b) = GF(a | b)
		    formula* allGF = unop_unop_multop(unop::G, unop::F,
						      multop::Or, s.res_GF);
		    // Xa | Xb = X(a | b)
		    // Xa | Xb | GF(c) = X(a | b | GF(c))
		    // For Universal&Eventual formula f1...fn we also have:
		    // Xa | Xb | f1...fn = X(a | b | f1...fn)
		    if (!s.res_X->empty())
		      {
			s.res_X->push_back(allGF);
			allGF = 0;
			s.res_X->insert(s.res_X->end(),
					s.res_EventUniv->begin(),
					s.res_EventUniv->end());
		      }
		    else if (!s.res_F->empty()
			     && s.res_G->empty()
			     && s.res_U_or_W->empty()
			     && s.res_R_or_M->empty()
			     && s.res_other->empty())
		      {
			// If there is no X but some F and only
			// eventual&universal formula, do:
			// Fa|Fb|f1...fn|GF(c) = F(a|b|f1...fn|GF(c))
			//
			// The reasoning here is that if we should
			// move f1...fn|GF(c) inside the "F" only
			// if it allows us to move all terms under F,
			// allowing a nice initial self-loop.
			//
			// For instance:
			//   F(a|GFb)  3st.6tr. with initial self-loop
			//   Fa|GFb    4st.8tr. without initial self-loop
			//
			// However, if other term are presents they will
			// prevent the formation of a self-loop, and the
			// rewriting is unwelcome:
			//   F(a|GFb)|Gc  5st.11tr.  without initial self-loop
			//   Fa|GFb|Gc    5st.10tr.  without initial self-loop
			// (counting the number of "subtransitions"
			// or, degeneralizing the automaton amplify
			// these differences)
			s.res_F->push_back(allGF);
			allGF = 0;
			s.res_F->insert(s.res_F->end(),
					s.res_EventUniv->begin(),
					s.res_EventUniv->end());
		      }
		    else
		      {
			s.res_other->insert(s.res_other->end(),
					    s.res_EventUniv->begin(),
					    s.res_EventUniv->end());
		      }
		    delete s.res_EventUniv;
		    // Xa | Xb | f1...fn = X(a | b | f1...fn)
		    // is built at the end of this multop::Or case.
		    // F(a) | F(b) = F(a | b)
		    // is built at the end of this multop::Or case.

		    // The following three loops perform these rewritings:
		    // (a U b) | (a U c) = a U (b | c)
		    // (a W b) | (a U c) = a W (b | c)
		    // (a W b) | (a W c) = a W (b | c)
		    // (a R b) | (c R b) = (a | c) R b
		    // (a R b) | (c M b) = (a | c) R b
		    // (a M b) | (c M b) = (a | c) M b
		    // G(a) | (a U b) = a W b
		    // G(a) | (a W b) = a W b
		    // G(b) | (a R b) = a R b.
		    // G(b) | (a M b) = a R b.
		    typedef Sgi::hash_map<formula*, multop::vec::iterator,
					  ptr_hash<formula> > fmap_t;
		    fmap_t uwmap; // associates "a" to "a U b" or "a W b"
		    fmap_t rmmap; // associates "b" to "a R b" or "a M b"
		    // (a U b) | (a U c) = a U (b | c)
		    // (a W b) | (a U c) = a W (b | c)
		    // (a W b) | (a W c) = a W (b | c)
		    for (multop::vec::iterator i = s.res_U_or_W->begin();
			 i != s.res_U_or_W->end(); ++i)
		      {
			binop* bo = static_cast<binop*>(*i);
			formula* a = bo->first();
			fmap_t::iterator j = uwmap.find(a);
			if (j == uwmap.end())
			  {
			    // First occurrence.
			    uwmap[a] = i;
			    continue;
			  }
			// We already have one occurrence.  Merge them.
			binop* old = static_cast<binop*>(*j->second);
			binop::type op = binop::U;
			if (bo->op() == binop::W
			    || old->op() == binop::W)
			  op = binop::W;
			formula* snd_arg =
			  multop::instance(multop::Or,
					   old->second()->clone(),
					   bo->second()->clone());
			*j->second = binop::instance(op, a->clone(), snd_arg);
			assert((*j->second)->kind() == formula::BinOp);
			*i = 0;
			old->destroy();
			bo->destroy();
		      }
		    // (a R b) | (c R b) = (a | c) R b
		    // (a R b) | (c M b) = (a | c) R b
		    // (a M b) | (c M b) = (a | c) M b
		    for (multop::vec::iterator i = s.res_R_or_M->begin();
			 i != s.res_R_or_M->end(); ++i)
		      {
			binop* bo = static_cast<binop*>(*i);
			formula* b = bo->second();
			fmap_t::iterator j = rmmap.find(b);
			if (j == rmmap.end())
			  {
			    // First occurrence.
			    rmmap[b] = i;
			    continue;
			  }
			// We already have one occurrence.  Merge them.
			binop* old = static_cast<binop*>(*j->second);
			binop::type op = binop::M;
			if (bo->op() == binop::R
			    || old->op() == binop::R)
			  op = binop::R;
			formula* fst_arg =
			  multop::instance(multop::Or,
					   old->first()->clone(),
					   bo->first()->clone());
			*j->second = binop::instance(op, fst_arg, b->clone());
			assert((*j->second)->kind() == formula::BinOp);
			*i = 0;
			old->destroy();
			bo->destroy();
		      }
		    // G(a) | (a U b) = a W b
		    // G(a) | (a W b) = a W b
		    // G(b) | (a R b) = a R b.
		    // G(b) | (a M b) = a R b.
		    for (multop::vec::iterator i = s.res_G->begin();
			 i != s.res_G->end(); ++i)
		      {
			bool superfluous = false;
			unop* uo = static_cast<unop*>(*i);
			formula* c = uo->child();

			fmap_t::iterator j = uwmap.find(c);
			if (j != uwmap.end())
			  {
			    superfluous = true;
			    binop* bo = static_cast<binop*>(*j->second);
			    if (bo->op() == binop::U)
			      {
				*j->second =
				  binop::instance(binop::W,
						  bo->first()->clone(),
						  bo->second()->clone());
				assert((*j->second)->kind() == formula::BinOp);
				bo->destroy();
			      }
			  }
			j = rmmap.find(c);
			if (j != rmmap.end())
			  {
			    superfluous = true;
			    binop* bo = static_cast<binop*>(*j->second);
			    if (bo->op() == binop::M)
			      {
				*j->second =
				  binop::instance(binop::R,
						  bo->first()->clone(),
						  bo->second()->clone());
				assert((*j->second)->kind() == formula::BinOp);
				bo->destroy();
			      }
			  }
			if (superfluous)
			  {
			    (*i)->destroy();
			    *i = 0;
			  }
		      }



		    s.res_other->reserve(s.res_other->size()
					 + s.res_G->size()
					 + s.res_U_or_W->size()
					 + s.res_R_or_M->size()
					 + 3);
		    s.res_other->insert(s.res_other->end(),
					s.res_G->begin(),
					s.res_G->end());
		    delete s.res_G;
		    s.res_other->insert(s.res_other->end(),
					s.res_U_or_W->begin(),
					s.res_U_or_W->end());
		    delete s.res_U_or_W;
		    s.res_other->insert(s.res_other->end(),
					s.res_R_or_M->begin(),
					s.res_R_or_M->end());
		    delete s.res_R_or_M;

		    // Those "F" formulae that are universal can be
		    // postponed inside the X term if there is one.
		    //
		    // In effect we rewrite
		    //   Xa|Xb|FGc|FGd|Fe as X(a|b|F(Gc|Gd))|Fe
		    if (!s.res_X->empty())
		      {
			multop::vec* univ = new multop::vec;
			for (multop::vec::iterator i = s.res_F->begin();
			     i != s.res_F->end(); ++i)
			  if ((*i)->is_universal())
			    {
			      univ->push_back(*i);
			      *i = 0; // Remove it from res_F.
			    }
			s.res_X->push_back(unop_multop(unop::F,
						       multop::Or, univ));
		      }

		    // F(a) | F(b) | ... = F(a | b | ...)
		    formula* allF = unop_multop(unop::F, multop::Or, s.res_F);
		    // Xa | Xb | ... = X(a | b | ...)
		    formula* allX = unop_multop(unop::X, multop::Or, s.res_X);

		    s.res_other->push_back(allX);
		    s.res_other->push_back(allF);
		    s.res_other->push_back(allGF);
		    result_ = multop::instance(multop::Or, s.res_other);
		    // If we altered the formula in some way, process
		    // it another time.
		    if (result_ != mo)
		      result_ = recurse_destroy(result_);
		    return;
		  }
		case multop::Concat:
		case multop::AndNLM:
		case multop::Fusion:
		  break;
		}
	    }
	  result_ = multop::instance(mo->op(), res);
	}

	formula*
	recurse(formula* f)
	{
	  return simplify_recursively(f, c_);
	}

	formula*
	recurse_destroy(formula* f)
	{
	  formula* tmp = recurse(f);
	  f->destroy();
	  return tmp;
	}

      protected:
	formula* result_;
	ltl_simplifier_cache* c_;
	const ltl_simplifier_options& opt_;
      };


      formula*
      simplify_recursively(const formula* f,
			   ltl_simplifier_cache* c)
      {
	formula* result = const_cast<formula*>(c->lookup_simplified(f));
	if (result)
	  return result;

	simplify_visitor v(c);
	const_cast<formula*>(f)->accept(v);
	result = v.result();

	c->cache_simplified(f, result);
	return result;
      }

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
