// Copyright (C) 2008, 2009, 2010, 2011 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004, 2005, 2006 Laboratoire
// d'Informatique de Paris 6 (LIP6), département Systèmes Répartis
// Coopératifs (SRC), Université Pierre et Marie Curie.
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

#include "misc/hash.hh"
#include "misc/bddalloc.hh"
#include "misc/bddlt.hh"
#include "misc/minato.hh"
#include "ltlast/visitor.hh"
#include "ltlast/allnodes.hh"
#include "ltlvisit/nenoform.hh"
#include "ltlvisit/tostring.hh"
#include "ltlvisit/postfix.hh"
#include "ltlvisit/apcollect.hh"
#include "ltlvisit/mark.hh"
#include "ltlvisit/tostring.hh"
#include <cassert>
#include <memory>
#include "ltl2tgba_fm.hh"
#include "tgba/bddprint.hh"

namespace spot
{
  using namespace ltl;

  namespace
  {

    // Helper dictionary.  We represent formulae using BDDs to
    // simplify them, and then translate BDDs back into formulae.
    //
    // The name of the variables are inspired from Couvreur's FM paper.
    //   "a" variables are promises (written "a" in the paper)
    //   "next" variables are X's operands (the "r_X" variables from the paper)
    //   "var" variables are atomic propositions.
    class translate_dict
    {
    public:

      translate_dict(bdd_dict* dict)
	: dict(dict),
	  a_set(bddtrue),
	  var_set(bddtrue),
	  next_set(bddtrue)
      {
      }

      ~translate_dict()
      {
	fv_map::iterator i;
	for (i = next_map.begin(); i != next_map.end(); ++i)
	  i->first->destroy();
	dict->unregister_all_my_variables(this);
      }

      bdd_dict* dict;

      typedef bdd_dict::fv_map fv_map;
      typedef bdd_dict::vf_map vf_map;

      fv_map next_map;	       ///< Maps "Next" variables to BDD variables
      vf_map next_formula_map; ///< Maps BDD variables to "Next" variables

      bdd a_set;
      bdd var_set;
      bdd next_set;

      int
      register_proposition(const formula* f)
      {
	int num = dict->register_proposition(f, this);
	var_set &= bdd_ithvar(num);
	return num;
      }

      int
      register_a_variable(const formula* f)
      {
	int num = dict->register_acceptance_variable(f, this);
	a_set &= bdd_ithvar(num);
	return num;
      }

      int
      register_next_variable(const formula* f)
      {
	int num;
	// Do not build a Next variable that already exists.
	fv_map::iterator sii = next_map.find(f);
	if (sii != next_map.end())
	  {
	    num = sii->second;
	  }
	else
	  {
	    f = f->clone();
	    num = dict->register_anonymous_variables(1, this);
	    next_map[f] = num;
	    next_formula_map[num] = f;
	  }
	next_set &= bdd_ithvar(num);
	return num;
      }

      std::ostream&
      dump(std::ostream& os) const
      {
	fv_map::const_iterator fi;
	os << "Next Variables:" << std::endl;
	for (fi = next_map.begin(); fi != next_map.end(); ++fi)
	{
	  os << "  " << fi->second << ": Next[";
	  to_string(fi->first, os) << "]" << std::endl;
	}
	os << "Shared Dict:" << std::endl;
	dict->dump(os);
	return os;
      }

      formula*
      var_to_formula(int var) const
      {
	vf_map::const_iterator isi = next_formula_map.find(var);
	if (isi != next_formula_map.end())
	  return isi->second->clone();
	isi = dict->acc_formula_map.find(var);
	if (isi != dict->acc_formula_map.end())
	  return isi->second->clone();
	isi = dict->var_formula_map.find(var);
	if (isi != dict->var_formula_map.end())
	  return isi->second->clone();
	assert(0);
	// Never reached, but some GCC versions complain about
	// a missing return otherwise.
	return 0;
      }

      formula*
      conj_bdd_to_formula(bdd b, multop::type op = multop::And) const
      {
	if (b == bddfalse)
	  return constant::false_instance();
	multop::vec* v = new multop::vec;
	while (b != bddtrue)
	  {
	    int var = bdd_var(b);
	    formula* res = var_to_formula(var);
	    bdd high = bdd_high(b);
	    if (high == bddfalse)
	      {
		res = unop::instance(unop::Not, res);
		b = bdd_low(b);
	      }
	    else
	      {
		assert(bdd_low(b) == bddfalse);
		b = high;
	      }
	    assert(b != bddfalse);
	    v->push_back(res);
	  }
	return multop::instance(op, v);
      }

      formula*
      bdd_to_formula(bdd f)
      {
	if (f == bddfalse)
	  return constant::false_instance();

	multop::vec* v = new multop::vec;

	minato_isop isop(f);
	bdd cube;
	while ((cube = isop.next()) != bddfalse)
	  v->push_back(conj_bdd_to_formula(cube));

	return multop::instance(multop::Or, v);
      }

      void
      conj_bdd_to_acc(tgba_explicit_formula* a, bdd b,
		      state_explicit_formula::transition* t)
      {
	assert(b != bddfalse);
	while (b != bddtrue)
	  {
	    int var = bdd_var(b);
	    bdd high = bdd_high(b);
	    if (high == bddfalse)
	      {
		// Simply ignore negated acceptance variables.
		b = bdd_low(b);
	      }
	    else
	      {
		formula* ac = var_to_formula(var);

		if (!a->has_acceptance_condition(ac))
		  a->declare_acceptance_condition(ac->clone());
		a->add_acceptance_condition(t, ac);
		b = high;
	      }
	    assert(b != bddfalse);
	  }
      }
    };


    // Debugging function.
    std::ostream&
    trace_ltl_bdd(const translate_dict& d, bdd f)
    {
      std::cerr << "Displaying BDD ";
      bdd_print_set(std::cerr, d.dict, f) << ":" << std::endl;

      minato_isop isop(f);
      bdd cube;
      while ((cube = isop.next()) != bddfalse)
	{
	  bdd label = bdd_exist(cube, d.next_set);
	  bdd dest_bdd = bdd_existcomp(cube, d.next_set);
	  const formula* dest = d.conj_bdd_to_formula(dest_bdd);
	  bdd_print_set(std::cerr, d.dict, label) << " => ";
	  bdd_print_set(std::cerr, d.dict, dest_bdd) << " = "
						     << to_string(dest)
						     << std::endl;
	  dest->destroy();
	}
      return std::cerr;
    }



    // Gather all promises of a formula.  These are the
    // right-hand sides of U or F operators.
    class ltl_promise_visitor: public postfix_visitor
    {
    public:
      ltl_promise_visitor(translate_dict& dict)
	: dict_(dict), res_(bddtrue)
      {
      }

      virtual
      ~ltl_promise_visitor()
      {
      }

      bdd
      result() const
      {
	return res_;
      }

      using postfix_visitor::doit;

      virtual void
      doit(unop* node)
      {
	if (node->op() == unop::F)
	  res_ &= bdd_ithvar(dict_.register_a_variable(node->child()));
      }

      virtual void
      doit(binop* node)
      {
	if (node->op() == binop::U)
	  res_ &= bdd_ithvar(dict_.register_a_variable(node->second()));
      }

    private:
      translate_dict& dict_;
      bdd res_;
    };

    // Rewrite rule for rational operators.
    class ratexp_trad_visitor: public const_visitor
    {
    public:
      // negated should only be set for constants or atomic properties
      ratexp_trad_visitor(translate_dict& dict,
			  formula* to_concat = 0,
			  bool negated = false)
	: dict_(dict), to_concat_(to_concat), negated_(negated)
      {
      }

      virtual
      ~ratexp_trad_visitor()
      {
	if (to_concat_)
	  to_concat_->destroy();
      }

      bdd
      result() const
      {
	return res_;
      }

      bdd next_to_concat()
      {
	if (!to_concat_)
	  to_concat_ = constant::empty_word_instance();
	int x = dict_.register_next_variable(to_concat_);
	return bdd_ithvar(x);
      }

      bdd now_to_concat()
      {
	if (to_concat_ && to_concat_ != constant::empty_word_instance())
	  return recurse(to_concat_);

	return bddfalse;
      }

      void
      visit(const atomic_prop* node)
      {
	if (negated_)
	  res_ = bdd_nithvar(dict_.register_proposition(node));
	else
	  res_ = bdd_ithvar(dict_.register_proposition(node));
	res_ &= next_to_concat();
      }

      void
      visit(const constant* node)
      {

	if (negated_)
	  {
	    switch (node->val())
	      {
	      case constant::True:
		res_ = bddfalse;
		return;
	      case constant::False:
		res_ = next_to_concat();
		return;
	      case constant::EmptyWord:
		assert(!"EmptyWord should not be negated");
		return;
	      }
	  }

	switch (node->val())
	  {
	  case constant::True:
	    res_ = next_to_concat();
	    return;
	  case constant::False:
	    res_ = bddfalse;
	    return;
	  case constant::EmptyWord:
	    res_ = now_to_concat();
	    return;
	  }
	/* Unreachable code.  */
	assert(0);
      }

      void
      visit(const unop* node)
      {
	switch (node->op())
	  {
	  case unop::F:
	  case unop::G:
	  case unop::X:
	  case unop::Finish:
	  case unop::Closure:
	  case unop::NegClosure:
	    assert(!"not a rational operator");
	    return;
	  case unop::Not:
	    {
	      // Not can only appear in front of Boolean
	      // expressions.
	      // propositions.
	      const formula* f = node->child();
	      assert(f->is_boolean());
	      res_ = recurse_and_concat(f, true);
	      return;
	    }
	  }
	/* Unreachable code.  */
	assert(0);
      }

      void
      visit(const bunop* bo)
      {
	formula* f;
	unsigned min = bo->min();
	unsigned max = bo->max();

	assert(max > 0);

	unsigned min2 = (min == 0) ? 0 : (min - 1);
	unsigned max2 =
	  (max == bunop::unbounded) ? bunop::unbounded : (max - 1);

	bunop::type op = bo->op();
	switch (op)
	  {
	  case bunop::Star:
	    f = bunop::instance(op, bo->child()->clone(), min2, max2);

	    if (to_concat_)
	      f = multop::instance(multop::Concat, f, to_concat_->clone());

	    if (!bo->child()->accepts_eword())
	      {
		//   f*;g  ->  f;f*;g | g
		//
		// If f does not accept the empty word, we can easily
		// add "f*;g" as to_concat_ when translating f.
		res_ = recurse(bo->child(), f);
		if (min == 0)
		  res_ |= now_to_concat();
	      }
	    else
	      {
		// if "f" accepts the empty words, doing the above would
		// lead to an infinite loop:
		//   f*;g -> f;f*;g | g
		//   f;f*;g -> f*;g | ...
		//
		// So we do in two steps:
		//  1. translate f,
		//  2. append f*;g to all destinations
		//  3. add |g
		res_ = recurse(bo->child());

		//   f*;g  ->  f;f*;g
		minato_isop isop(res_);
		bdd cube;
		res_ = bddfalse;
		while ((cube = isop.next()) != bddfalse)
		  {
		    bdd label = bdd_exist(cube, dict_.next_set);
		    bdd dest_bdd = bdd_existcomp(cube, dict_.next_set);
		    formula* dest =
		      dict_.conj_bdd_to_formula(dest_bdd);
		    formula* dest2;
		    int x;
		    if (dest == constant::empty_word_instance())
		      {
			x = dict_.register_next_variable(f);
			res_ |= label & bdd_ithvar(x);
		      }
		    else
		      {
			dest2 = multop::instance(multop::Concat, dest,
						 f->clone());
			if (dest2 != constant::false_instance())
			  {
			    x = dict_.register_next_variable(dest2);
			    dest2->destroy();
			    res_ |= label & bdd_ithvar(x);
			  }
		      }
		  }
		f->destroy();
		res_ |= now_to_concat();
	      }
	    return;
	  case bunop::Equal:
	  case bunop::Goto:
	    {
	      // b[=min..max] == (!b;b[=min..max]) | (b;b[=min-1..max-1])
	      // b[=0..max]   == [*0] | (!b;b[=0..max]) | (b;b[=0..max-1])
	      // Note: b[=0] == (!b)[*] is a trivial identity, so it will
	      // never occur here.

	      // b[->min..max] == (!b;b[->min..max]) | (b;b[->min-1..max-1])
	      // b[->0..max]   == [*0] | (!b;b[->0..max]) | (b;b[->0..max-1])
	      // Note: b[->0] == [*0] is a trivial identity, so it will
	      // never occur here.

	      formula* f1 = // !b;b[=min..max]  or  !b;b[->min..max]
		multop::instance(multop::Concat,
				 unop::instance(unop::Not,
						bo->child()->clone()),
				 bo->clone());

	      formula* f2 = // b;b[=min-1..max-1]  or  b;b[->min-1..max-1]
		multop::instance(multop::Concat,
				 bo->child()->clone(),
				 bunop::instance(op,
						 bo->child()->clone(),
						 min2, max2));
	      f = multop::instance(multop::Or, f1, f2);
	      res_ = recurse_and_concat(f);
	      f->destroy();
	      if (min == 0)
		res_ |= now_to_concat();
	      return;
	    }
	  }
	/* Unreachable code.  */
	assert(0);
      }

      void
      visit(const binop*)
      {
	assert(!"not a rational operator");
      }

      void
      visit(const automatop*)
      {
	assert(!"not a rational operator");
      }

      void
      visit(const multop* node)
      {
	multop::type op = node->op();
	switch (op)
	  {
	  case multop::AndNLM:
	  case multop::And:
	    {
	      unsigned s = node->size();

	      if (op == multop::AndNLM)
		{
		  multop::vec* final = new multop::vec;
		  multop::vec* non_final = new multop::vec;

		  for (unsigned n = 0; n < s; ++n)
		    {
		      const formula* f = node->nth(n);
		      if (f->accepts_eword())
			final->push_back(f->clone());
		      else
			non_final->push_back(f->clone());
		    }

		  if (non_final->empty())
		    {
		      delete non_final;
		      // (a* & b*);c = (a*|b*);c
		      formula* f = multop::instance(multop::Or, final);
		      res_ = recurse_and_concat(f);
		      f->destroy();
		      break;
		    }
		  if (!final->empty())
		    {
		      // let F_i be final formulae
		      //     N_i be non final formula
		      // (F_1 & ... & F_n & N_1 & ... & N_m)
		      // =   (F_1 | ... | F_n);[*] && (N_1 & ... & N_m)
		      //   | (F_1 | ... | F_n) && (N_1 & ... & N_m);[*]
		      formula* f = multop::instance(multop::Or, final);
		      formula* n = multop::instance(multop::AndNLM, non_final);
		      formula* t = bunop::instance(bunop::Star,
						   constant::true_instance());
		      formula* ft = multop::instance(multop::Concat,
						     f->clone(), t->clone());
		      formula* nt = multop::instance(multop::Concat,
						     n->clone(), t);
		      formula* ftn = multop::instance(multop::And, ft, n);
		      formula* fnt = multop::instance(multop::And, f, nt);
		      formula* all = multop::instance(multop::Or, ftn, fnt);
		      res_ = recurse_and_concat(all);
		      all->destroy();
		      break;
		    }
		  // No final formula.
		  // Apply same rule as &&, until we reach a point where
		  // we have final formulae.
		  delete final;
		  for (unsigned n = 0; n < s; ++n)
		    (*non_final)[n]->destroy();
		  delete non_final;
		}

	      res_ = bddtrue;
	      for (unsigned n = 0; n < s; ++n)
		{
		  bdd res = recurse(node->nth(n));
		  // trace_ltl_bdd(dict_, res);
		  res_ &= res;
		}

	      //std::cerr << "Pre-Concat:" << std::endl;
	      //trace_ltl_bdd(dict_, res_);

	      if (to_concat_)
		{
		  // If we have translated (a* && b*) in (a* && b*);c, we
		  // have to append ";c" to all destinations.

		  minato_isop isop(res_);
		  bdd cube;
		  res_ = bddfalse;
		  while ((cube = isop.next()) != bddfalse)
		    {
		      bdd label = bdd_exist(cube, dict_.next_set);
		      bdd dest_bdd = bdd_existcomp(cube, dict_.next_set);
		      formula* dest =
			dict_.conj_bdd_to_formula(dest_bdd, op);
		      formula* dest2;
		      int x;
		      if (dest == constant::empty_word_instance())
			{
			  res_ |= label & next_to_concat();
			}
		      else
			{
			  dest2 = multop::instance(multop::Concat, dest,
						   to_concat_->clone());
			  if (dest2 != constant::false_instance())
			    {
			      x = dict_.register_next_variable(dest2);
			      dest2->destroy();
			      res_ |= label & bdd_ithvar(x);
			    }
			  if (node->accepts_eword())
			    res_ |= label & next_to_concat();
			}
		    }
		}
	      if (node->accepts_eword())
		res_ |= now_to_concat();

	      break;
	    }
	  case multop::Or:
	    {
	      res_ = bddfalse;
	      unsigned s = node->size();
	      for (unsigned n = 0; n < s; ++n)
		res_ |= recurse_and_concat(node->nth(n));
	      break;
	    }
	  case multop::Concat:
	    {
	      multop::vec* v = new multop::vec;
	      unsigned s = node->size();
	      v->reserve(s);
	      for (unsigned n = 1; n < s; ++n)
		v->push_back(node->nth(n)->clone());
	      if (to_concat_)
		v->push_back(to_concat_->clone());
	      res_ = recurse(node->nth(0),
			     multop::instance(multop::Concat, v));
	      break;
	    }
	  case multop::Fusion:
	    {
	      assert(node->size() >= 2);

	      // the head
	      bdd res = recurse(node->nth(0));

	      // the tail
	      multop::vec* v = new multop::vec;
	      unsigned s = node->size();
	      v->reserve(s - 1);
	      for (unsigned n = 1; n < s; ++n)
		v->push_back(node->nth(n)->clone());
	      formula* tail = multop::instance(multop::Fusion, v);
	      bdd tail_bdd;
	      bool tail_computed = false;

	      //trace_ltl_bdd(dict_, res);

	      minato_isop isop(res);
	      bdd cube;
	      res_ = bddfalse;
	      while ((cube = isop.next()) != bddfalse)
		{
		  bdd label = bdd_exist(cube, dict_.next_set);
		  bdd dest_bdd = bdd_existcomp(cube, dict_.next_set);
		  formula* dest = dict_.conj_bdd_to_formula(dest_bdd);

		  if (dest->accepts_eword())
		    {
		      // The destination is a final state.  Make sure we
		      // can also exit if tail is satisfied.
		      if (!tail_computed)
			{
			  tail_bdd = recurse_and_concat(tail);
			  tail_computed = true;
			}
		      res_ |= label & tail_bdd;
		    }

		  if (dynamic_cast<constant*>(dest) == 0)
		    {
		      // If the destination is not a constant, it
		      // means it can have successors.  Fusion the
		      // tail and append anything to concatenate.
		      formula* dest2 = multop::instance(multop::Fusion, dest,
							tail->clone());
		      if (to_concat_)
			 dest2 = multop::instance(multop::Concat, dest2,
						 to_concat_->clone());
		      if (dest2 != constant::false_instance())
			{
			  int x = dict_.register_next_variable(dest2);
			  dest2->destroy();
			  res_ |= label & bdd_ithvar(x);
			}
		    }
		}

	      tail->destroy();
	      break;
	    }
	  }
      }

      bdd
      recurse(const formula* f, formula* to_concat = 0, bool negated = false)
      {
	ratexp_trad_visitor v(dict_, to_concat, negated);
	f->accept(v);
	return v.result();
      }

      bdd
      recurse_and_concat(const formula* f, bool negated = false)
      {
	return recurse(f, to_concat_ ? to_concat_->clone() : 0, negated);
      }

    private:
      translate_dict& dict_;
      bdd res_;
      formula* to_concat_;
      bool negated_;
    };


    // The rewrite rules used here are adapted from Jean-Michel
    // Couvreur's FM paper, augmented to support rational operators.
    class ltl_trad_visitor: public const_visitor
    {
    public:
      ltl_trad_visitor(translate_dict& dict, bool mark_all = false,
		       bool exprop = false)
	: dict_(dict), rat_seen_(false), has_marked_(false),
	  mark_all_(mark_all), exprop_(exprop)
      {
      }

      virtual
      ~ltl_trad_visitor()
      {
      }

      void
      reset(bool mark_all)
      {
	rat_seen_ = false;
	has_marked_ = false;
	mark_all_ = mark_all;
      }

      bdd
      result() const
      {
	return res_;
      }

      const translate_dict&
      get_dict() const
      {
	return dict_;
      }

      bool
      has_rational() const
      {
	return rat_seen_;
      }

      bool
      has_marked() const
      {
	return has_marked_;
      }

      void
      visit(const atomic_prop* node)
      {
	res_ = bdd_ithvar(dict_.register_proposition(node));
      }

      void
      visit(const constant* node)
      {
	switch (node->val())
	  {
	  case constant::True:
	    res_ = bddtrue;
	    return;
	  case constant::False:
	    res_ = bddfalse;
	    return;
	  case constant::EmptyWord:
	    assert(!"Not an LTL operator");
	    return;
	  }
	/* Unreachable code.  */
	assert(0);
      }

      void
      visit(const unop* node)
      {
	unop::type op = node->op();

	switch (op)
	  {
	  case unop::F:
	    {
	      // r(Fy) = r(y) + a(y)r(XFy)
	      const formula* child = node->child();
	      bdd y = recurse(child);
	      int a = dict_.register_a_variable(child);
	      int x = dict_.register_next_variable(node);
	      res_ = y | (bdd_ithvar(a) & bdd_ithvar(x));
	      break;
	    }
	  case unop::G:
	    {
	      // The paper suggests that we optimize GFy
	      // as
	      //   r(GFy) = (r(y) + a(y))r(XGFy)
	      // instead of
	      //   r(GFy) = (r(y) + a(y)r(XFy)).r(XGFy)
	      // but this is just a particular case
	      // of the "merge all states with the same
	      // symbolic rewriting" optimization we do later.
	      // (r(Fy).r(GFy) and r(GFy) have the same symbolic
	      // rewriting.)  Let's keep things simple here.

	      // r(Gy) = r(y)r(XGy)
	      const formula* child = node->child();
	      int x = dict_.register_next_variable(node);
	      bdd y = recurse(child);
	      res_ = y & bdd_ithvar(x);
	      break;
	    }
	  case unop::Not:
	    {
	      // r(!y) = !r(y)
	      res_ = bdd_not(recurse(node->child()));
	      break;
	    }
	  case unop::X:
	    {
	      // r(Xy) = Next[y]
	      int x = dict_.register_next_variable(node->child());
	      res_ = bdd_ithvar(x);
	      break;
	    }
	  case unop::Closure:
	    {
	      rat_seen_ = true;
	      if (node->child()->accepts_eword())
		{
		  res_ = bddtrue;
		  return;
		}

	      ratexp_trad_visitor v(dict_);
	      node->child()->accept(v);
	      bdd f1 = v.result();
	      res_ = bddfalse;


	      if (exprop_)
		{
		  bdd var_set = bdd_existcomp(bdd_support(f1), dict_.var_set);
		  bdd all_props = bdd_existcomp(f1, dict_.var_set);
		  while (all_props != bddfalse)
		    {
		      bdd label = bdd_satoneset(all_props, var_set, bddtrue);
		      all_props -= label;

		      formula* dest =
			dict_.bdd_to_formula(bdd_exist(f1 & label,
						       dict_.var_set));

		      const formula* dest2;
		      if (dest->accepts_eword())
			{
			  dest->destroy();
			  res_ |= label;
			}
		      else
			{
			  dest2 = unop::instance(op, dest);
			  if (dest2 == constant::false_instance())
			    continue;
			  int x = dict_.register_next_variable(dest2);
			  dest2->destroy();
			  res_ |= label & bdd_ithvar(x);
			}
		    }
		}
	      else
		{
		  minato_isop isop(f1);
		  bdd cube;
		  while ((cube = isop.next()) != bddfalse)
		    {
		      bdd label = bdd_exist(cube, dict_.next_set);
		      bdd dest_bdd = bdd_existcomp(cube, dict_.next_set);
		      formula* dest = dict_.conj_bdd_to_formula(dest_bdd);

		      const formula* dest2;
		      if (dest->accepts_eword())
			{
			  dest->destroy();
			  res_ |= label;
			}
		      else
			{
			  dest2 = unop::instance(op, dest);
			  if (dest2 == constant::false_instance())
			    continue;
			  int x = dict_.register_next_variable(dest2);
			  dest2->destroy();
			  res_ |= label & bdd_ithvar(x);
			}
		    }
		}
	    }
	    break;

	  case unop::NegClosure:
	    {
	      rat_seen_ = true;
	      has_marked_ = true;

	      if (node->child()->accepts_eword())
		{
		  res_ = bddfalse;
		  return;
		}

	      ratexp_trad_visitor v(dict_);
	      node->child()->accept(v);
	      bdd f1 = v.result();

	      // trace_ltl_bdd(dict_, f1);

	      bdd var_set = bdd_existcomp(bdd_support(f1), dict_.var_set);
	      bdd all_props = bdd_existcomp(f1, dict_.var_set);

	      res_ = !all_props &
		// stick X(1) to preserve determinism.
		bdd_ithvar(dict_.register_next_variable
			   (constant::true_instance()));

	      while (all_props != bddfalse)
		{
		  bdd label = bdd_satoneset(all_props, var_set, bddtrue);
		  all_props -= label;

		  formula* dest =
		    dict_.bdd_to_formula(bdd_exist(f1 & label,
						   dict_.var_set));

		  // !{ Exp } is false if Exp accepts the empty word.
		  if (dest->accepts_eword())
		    {
		      dest->destroy();
		      continue;
		    }

		  const formula* dest2 = unop::instance(op, dest);

		  if (dest == constant::false_instance())
		    continue;

		  int x = dict_.register_next_variable(dest2);
		  dest2->destroy();
		  res_ |= label & bdd_ithvar(x);
		}
	    }
	    break;

	  case unop::Finish:
	    assert(!"unsupported operator");
	    break;
	  }
      }

      void
      visit(const bunop*)
      {
	assert(!"Not an LTL operator");
      }

      void
      visit(const binop* node)
      {
	binop::type op = node->op();

	switch (op)
	  {
	    // r(f1 logical-op f2) = r(f1) logical-op r(f2)
	  case binop::Xor:
	    {
	      bdd f1 = recurse(node->first());
	      bdd f2 = recurse(node->second());
	      res_ = bdd_apply(f1, f2, bddop_xor);
	      return;
	    }
	  case binop::Implies:
	    {
	      bdd f1 = recurse(node->first());
	      bdd f2 = recurse(node->second());
	      res_ = bdd_apply(f1, f2, bddop_imp);
	      return;
	    }
	  case binop::Equiv:
	    {
	      bdd f1 = recurse(node->first());
	      bdd f2 = recurse(node->second());
	      res_ = bdd_apply(f1, f2, bddop_biimp);
	      return;
	    }
	  case binop::U:
	    {
	      bdd f1 = recurse(node->first());
	      bdd f2 = recurse(node->second());
	      // r(f1 U f2) = r(f2) + a(f2)r(f1)r(X(f1 U f2))
	      int a = dict_.register_a_variable(node->second());
	      int x = dict_.register_next_variable(node);
	      res_ = f2 | (bdd_ithvar(a) & f1 & bdd_ithvar(x));
	      break;
	    }
	  case binop::W:
	    {
	      bdd f1 = recurse(node->first());
	      bdd f2 = recurse(node->second());
	      // r(f1 W f2) = r(f2) + r(f1)r(X(f1 U f2))
	      int x = dict_.register_next_variable(node);
	      res_ = f2 | (f1 & bdd_ithvar(x));
	      break;
	    }
	  case binop::R:
	    {
	      bdd f1 = recurse(node->first());
	      bdd f2 = recurse(node->second());
	      // r(f1 R f2) = r(f1)r(f2) + r(f2)r(X(f1 U f2))
	      int x = dict_.register_next_variable(node);
	      res_ = (f1 & f2) | (f2 & bdd_ithvar(x));
	      break;
	    }
	  case binop::M:
	    {
	      bdd f1 = recurse(node->first());
	      bdd f2 = recurse(node->second());
	      // r(f1 M f2) = r(f1)r(f2) + a(f1)r(f2)r(X(f1 M f2))
	      int a = dict_.register_a_variable(node->first());
	      int x = dict_.register_next_variable(node);
	      res_ = (f1 & f2) | (bdd_ithvar(a) & f2 & bdd_ithvar(x));
	      break;
	    }
	  case binop::EConcatMarked:
	    has_marked_ = true;
	    /* fall through */
	  case binop::EConcat:
	    rat_seen_ = true;
	    {
	      // Recognize f2 on transitions going to destinations
	      // that accept the empty word.
	      bdd f2 = recurse(node->second());
	      ratexp_trad_visitor v(dict_);
	      node->first()->accept(v);
	      bdd f1 = v.result();
	      res_ = bddfalse;

	      if (mark_all_)
		{
		  op = binop::EConcatMarked;
		  has_marked_ = true;
		}

	      if (exprop_)
		{
		  bdd var_set = bdd_existcomp(bdd_support(f1), dict_.var_set);
		  bdd all_props = bdd_existcomp(f1, dict_.var_set);
		  while (all_props != bddfalse)
		    {
		      bdd label = bdd_satoneset(all_props, var_set, bddtrue);
		      all_props -= label;

		      formula* dest =
			dict_.bdd_to_formula(bdd_exist(f1 & label,
						       dict_.var_set));

		      const formula* dest2 =
			binop::instance(op, dest, node->second()->clone());

		      if (dest2 != constant::false_instance())
			{
			  int x = dict_.register_next_variable(dest2);
			  dest2->destroy();
			  res_ |= label & bdd_ithvar(x);
			}
		      if (dest->accepts_eword())
			res_ |= label & f2;
		    }
		}
	      else
		{
		  minato_isop isop(f1);
		  bdd cube;
		  while ((cube = isop.next()) != bddfalse)
		    {
		      bdd label = bdd_exist(cube, dict_.next_set);
		      bdd dest_bdd = bdd_existcomp(cube, dict_.next_set);
		      formula* dest = dict_.conj_bdd_to_formula(dest_bdd);

		      if (dest == constant::empty_word_instance())
			{
			  res_ |= label & f2;
			}
		      else
			{
			  formula* dest2 = binop::instance(op, dest,
						  node->second()->clone());
			  if (dest2 != constant::false_instance())
			    {
			      int x = dict_.register_next_variable(dest2);
			      dest2->destroy();
			      res_ |= label & bdd_ithvar(x);
			    }
			  if (dest->accepts_eword())
			    res_ |= label & f2;
			}
		    }
		}
	    }
	    break;

	  case binop::UConcat:
	    {
	      // Transitions going to destinations accepting the empty
	      // word should recognize f2, and the automaton for f1
	      // should be understood as universal.
	      bdd f2 = recurse(node->second());
	      ratexp_trad_visitor v(dict_);
	      node->first()->accept(v);
	      bdd f1 = v.result();
	      res_ = bddtrue;

	      bdd var_set = bdd_existcomp(bdd_support(f1), dict_.var_set);
	      bdd all_props = bdd_existcomp(f1, dict_.var_set);
	      while (all_props != bddfalse)
		{

		  bdd one_prop_set = bddtrue;
		  if (exprop_)
		    one_prop_set = bdd_satoneset(all_props, var_set, bddtrue);
		  all_props -= one_prop_set;

		  minato_isop isop(f1 & one_prop_set);
		  bdd cube;
		  while ((cube = isop.next()) != bddfalse)
		    {
		      bdd label = bdd_exist(cube, dict_.next_set);
		      bdd dest_bdd = bdd_existcomp(cube, dict_.next_set);
		      formula* dest = dict_.conj_bdd_to_formula(dest_bdd);
		      formula* dest2 =
			binop::instance(op, dest, node->second()->clone());

		      bdd udest =
			bdd_ithvar(dict_.register_next_variable(dest2));

		      if (dest->accepts_eword())
			udest &= f2;

		      dest2->destroy();

		      res_ &= bdd_apply(label, udest, bddop_imp);
		    }
		}
	    }
	    break;
	  }
      }

      void
      visit(const automatop*)
      {
	assert(!"unsupported operator");
      }

      void
      visit(const multop* node)
      {
	switch (node->op())
	  {
	  case multop::And:
	    {
	      res_ = bddtrue;
	      unsigned s = node->size();
	      for (unsigned n = 0; n < s; ++n)
		{
		  bdd res = recurse(node->nth(n));
		  //std::cerr << "== in And (" << to_string(node->nth(n))
		  // << ")" << std::endl;
		  // trace_ltl_bdd(dict_, res);
		  res_ &= res;
		}
	      //std::cerr << "=== And final" << std::endl;
	      // trace_ltl_bdd(dict_, res_);
	      break;
	    }
	  case multop::Or:
	    {
	      res_ = bddfalse;
	      unsigned s = node->size();
	      for (unsigned n = 0; n < s; ++n)
		res_ |= recurse(node->nth(n));
	      break;
	    }
	  case multop::Concat:
	  case multop::Fusion:
	  case multop::AndNLM:
	    assert(!"Not an LTL operator");
	    break;
	  }

      }

      bdd
      recurse(const formula* f)
      {
	ltl_trad_visitor v(dict_, mark_all_, exprop_);
	f->accept(v);
	rat_seen_ |= v.has_rational();
	has_marked_ |= v.has_marked();
	return v.result();
      }


    private:
      translate_dict& dict_;
      bdd res_;
      bool rat_seen_;
      bool has_marked_;
      bool mark_all_;
      bool exprop_;
    };


    // Check whether a formula has a R, W, or G operator at its
    // top-level (preceding logical operators do not count).
    class ltl_possible_fair_loop_visitor: public const_visitor
    {
    public:
      ltl_possible_fair_loop_visitor()
	: res_(false)
      {
      }

      virtual
      ~ltl_possible_fair_loop_visitor()
      {
      }

      bool
      result() const
      {
	return res_;
      }

      void
      visit(const atomic_prop*)
      {
      }

      void
      visit(const constant*)
      {
      }

      void
      visit(const unop* node)
      {
	if (node->op() == unop::G)
	  res_ = true;
      }

      void
      visit(const binop* node)
      {
	switch (node->op())
	  {
	    // r(f1 logical-op f2) = r(f1) logical-op r(f2)
	  case binop::Xor:
	  case binop::Implies:
	  case binop::Equiv:
	    node->first()->accept(*this);
	    if (!res_)
	      node->second()->accept(*this);
	    return;
	  case binop::U:
	  case binop::M:
	    return;
	  case binop::R:
	  case binop::W:
	    res_ = true;
	    return;
	  case binop::UConcat:
	  case binop::EConcat:
	  case binop::EConcatMarked:
	    node->second()->accept(*this);
	    // FIXME: we might need to add Acc[1]
	    return;
	  }
	/* Unreachable code.  */
	assert(0);
      }

      void
      visit(const automatop*)
      {
	assert(!"unsupported operator");
      }

      void
      visit(const bunop*)
      {
	assert(!"unsupported operator");
      }

      void
      visit(const multop* node)
      {
	unsigned s = node->size();
	for (unsigned n = 0; n < s && !res_; ++n)
	  {
	    node->nth(n)->accept(*this);
	  }
      }

    private:
      bool res_;
    };

    // Check whether a formula can be part of a fair loop.
    // Cache the result for efficiency.
    class possible_fair_loop_checker
    {
    public:
      bool
      check(const formula* f)
      {
	pfl_map::const_iterator i = pfl_.find(f);
	if (i != pfl_.end())
	  return i->second;
	ltl_possible_fair_loop_visitor v;
	f->accept(v);
	bool rel = v.result();
	pfl_[f] = rel;
	return rel;
      }

    private:
      typedef Sgi::hash_map<const formula*, bool, formula_ptr_hash> pfl_map;
      pfl_map pfl_;
    };

    class formula_canonizer
    {
    public:
      formula_canonizer(translate_dict& d,
			bool fair_loop_approx, bdd all_promises, bool exprop)
	: v_(d, false, exprop),
	  fair_loop_approx_(fair_loop_approx),
	  all_promises_(all_promises),
	  d_(d)
      {
	// For cosmetics, register 1 initially, so the algorithm will
	// not register an equivalent formula first.
	b2f_[bddtrue] = constant::true_instance();
      }

      ~formula_canonizer()
      {
	while (!f2b_.empty())
	  {
	    formula_to_bdd_map::iterator i = f2b_.begin();
	    const formula* f = i->first;
	    f2b_.erase(i);
	    f->destroy();
	  }
      }

      struct translated
      {
	bdd symbolic;
	bool has_rational:1;
	bool has_marked:1;
      };

      const translated&
      translate(const formula* f, bool* new_flag = 0)
      {
	// Use the cached result if available.
	formula_to_bdd_map::const_iterator i = f2b_.find(f);
	if (i != f2b_.end())
	  return i->second;

	if (new_flag)
	  *new_flag = true;

	// Perform the actual translation.
	v_.reset(!f->is_marked());
	f->accept(v_);
	translated t;
	t.symbolic = v_.result();
	t.has_rational = v_.has_rational();
	t.has_marked = v_.has_marked();

//	std::cerr << "-----" << std::endl;
//	std::cerr << "Formula: " << to_string(f) << std::endl;
//	std::cerr << "Rational: " << t.has_rational << std::endl;
//	std::cerr << "Marked: " << t.has_marked << std::endl;
//	std::cerr << "Mark all: " << !has_mark(f) << std::endl;
//	std::cerr << "Transitions:" << std::endl;
//	trace_ltl_bdd(v_.get_dict(), t.symbolic);

	if (t.has_rational)
	  {
	    bdd res = bddfalse;

	    minato_isop isop(t.symbolic);
	    bdd cube;
	    while ((cube = isop.next()) != bddfalse)
	      {
		bdd label = bdd_exist(cube, d_.next_set);
		bdd dest_bdd = bdd_existcomp(cube, d_.next_set);
		formula* dest =
		  d_.conj_bdd_to_formula(dest_bdd);

		// Handle a Miyano-Hayashi style unrolling for
		// rational operators.  Marked nodes correspond to
		// subformulae in the Miyano-Hayashi set.
		if (simplify_mark(dest))
		  {
		    // Make the promise that we will exit marked sets.
		    int a =
		      d_.register_a_variable(constant::true_instance());
		    label &= bdd_ithvar(a);
		  }
		else
		  {
		    // We have left marked operators, but still
		    // have other rational operator to check.
		    // Start a new marked cycle.
		    formula* dest2 = mark_concat_ops(dest);
		    dest->destroy();
		    dest = dest2;
		  }
		// Note that simplify_mark may have changed dest.
		dest_bdd = bdd_ithvar(d_.register_next_variable(dest));
		dest->destroy();
		res |= label & dest_bdd;
	      }
	    t.symbolic = res;
//	    std::cerr << "Marking rewriting:" << std::endl;
//	    trace_ltl_bdd(v_.get_dict(), t.symbolic);
	  }

	// Apply the fair-loop approximation if requested.
	if (fair_loop_approx_)
	  {
	    // If the source cannot possibly be part of a fair
	    // loop, make all possible promises.
	    if (fair_loop_approx_
		&& f != constant::true_instance()
		&& !pflc_.check(f))
	      t.symbolic &= all_promises_;
	  }

	// Register the reverse mapping if it is not already done.
	if (b2f_.find(t.symbolic) == b2f_.end())
	  b2f_[t.symbolic] = f;

	return f2b_[f->clone()] = t;
      }

      const formula*
      canonize(const formula* f)
      {
	bool new_variable = false;
	bdd b = translate(f, &new_variable).symbolic;

	bdd_to_formula_map::iterator i = b2f_.find(b);
	// Since we have just translated the formula, it is
	// necessarily in b2f_.
	assert(i != b2f_.end());

	if (i->second != f)
	  {
	    // The translated bdd maps to an already seen formula.
	    f->destroy();
	    f = i->second->clone();
	  }
	return f;
      }

    private:
      ltl_trad_visitor v_;
      // Map each formula to its associated bdd.  This speed things up when
      // the same formula is translated several times, which especially
      // occurs when canonize() is called repeatedly inside exprop.
      typedef std::map<bdd, const formula*, bdd_less_than> bdd_to_formula_map;
      bdd_to_formula_map b2f_;
      // Map a representation of successors to a canonical formula.
      // We do this because many formulae (such as `aR(bRc)' and
      // `aR(bRc).(bRc)') are equivalent, and are trivially identified
      // by looking at the set of successors.
      typedef std::map<const formula*, translated> formula_to_bdd_map;
      formula_to_bdd_map f2b_;

      possible_fair_loop_checker pflc_;
      bool fair_loop_approx_;
      bdd all_promises_;
      translate_dict& d_;
    };

  }

  typedef std::map<bdd, bdd, bdd_less_than> prom_map;
  typedef Sgi::hash_map<const formula*, prom_map, formula_ptr_hash> dest_map;

  static void
  fill_dests(translate_dict& d, dest_map& dests, bdd label, const formula* dest)
  {
    bdd conds = bdd_existcomp(label, d.var_set);
    bdd promises = bdd_existcomp(label, d.a_set);

    dest_map::iterator i = dests.find(dest);
    if (i == dests.end())
      {
	dests[dest][promises] = conds;
      }
    else
      {
	i->second[promises] |= conds;
	dest->destroy();
      }
  }


  tgba_explicit_formula*
  ltl_to_tgba_fm(const formula* f, bdd_dict* dict,
		 bool exprop, bool symb_merge, bool branching_postponement,
		 bool fair_loop_approx, const atomic_prop_set* unobs,
		 ltl_simplifier* simplifier)
  {
    formula* f2;

    // Simplify the formula, if requested.
    if (simplifier)
      {
	// This will normalize the formula regardless of the
	// configuration of the simplifier.
	f2 = simplifier->simplify(f);
      }
    else
      {
	// Otherwise, at least normalize the formula.  We want all the
	// negations on the atomic propositions.  We also suppress
	// logic abbreviations such as <=>, =>, or XOR, since they
	// would involve negations at the BDD level.
	ltl_simplifier s;
	f2 = s.negative_normal_form(f, false);
      }

    typedef std::set<const formula*, formula_ptr_less_than> set_type;
    set_type formulae_to_translate;

    translate_dict d(dict);

    // Compute the set of all promises that can possibly occur
    // inside the formula.
    bdd all_promises = bddtrue;
    if (fair_loop_approx || unobs)
      {
	ltl_promise_visitor pv(d);
	f2->accept(pv);
	all_promises = pv.result();
      }

    formula_canonizer fc(d, fair_loop_approx, all_promises, exprop);

    // These are used when atomic propositions are interpreted as
    // events.  There are two kinds of events: observable events are
    // those used in the formula, and unobservable events or other
    // events that can occur at anytime.  All events exclude each
    // other.
    bdd observable_events = bddfalse;
    bdd unobservable_events = bddfalse;
    if (unobs)
      {
	bdd neg_events = bddtrue;
	std::auto_ptr<atomic_prop_set> aps(atomic_prop_collect(f));
	for (atomic_prop_set::const_iterator i = aps->begin();
	     i != aps->end(); ++i)
	  {
	    int p = d.register_proposition(*i);
	    bdd pos = bdd_ithvar(p);
	    bdd neg = bdd_nithvar(p);
	    observable_events = (observable_events & neg) | (neg_events & pos);
	    neg_events &= neg;
	  }
	for (atomic_prop_set::const_iterator i = unobs->begin();
	     i != unobs->end(); ++i)
	  {
	    int p = d.register_proposition(*i);
	    bdd pos = bdd_ithvar(p);
	    bdd neg = bdd_nithvar(p);
	    unobservable_events = ((unobservable_events & neg)
				   | (neg_events & pos));
	    observable_events &= neg;
	    neg_events &= neg;
	  }
      }
    bdd all_events = observable_events | unobservable_events;


    tgba_explicit_formula* a = new tgba_explicit_formula(dict);

    // This is in case the initial state is equivalent to true...
    if (symb_merge)
      f2 = const_cast<formula*>(fc.canonize(f2));

    formulae_to_translate.insert(f2);
    a->set_init_state(f2);

    while (!formulae_to_translate.empty())
      {
	// Pick one formula.
	const formula* now = *formulae_to_translate.begin();
	formulae_to_translate.erase(formulae_to_translate.begin());

	// Translate it into a BDD to simplify it.
	const formula_canonizer::translated& t = fc.translate(now);
	bdd res = t.symbolic;

	// Handle exclusive events.
	if (unobs)
	  {
	    res &= observable_events;
	    int n = d.register_next_variable(now);
	    res |= unobservable_events & bdd_ithvar(n) & all_promises;
	  }

	// We used to factor only Next and A variables while computing
	// prime implicants, with
	//    minato_isop isop(res, d.next_set & d.a_set);
	// in order to obtain transitions with formulae of atomic
	// proposition directly, but unfortunately this led to strange
	// factorizations.  For instance f U g was translated as
	//     r(f U g) = g + a(g).r(X(f U g)).(f + g)
	// instead of just
	//     r(f U g) = g + a(g).r(X(f U g)).f
	// Of course both formulae are logically equivalent, but the
	// latter is "more deterministic" than the former, so it should
	// be preferred.
	//
	// Therefore we now factor all variables.  This may lead to more
	// transitions than necessary (e.g.,  r(f + g) = f + g  will be
	// coded as two transitions), but we later merge all transitions
	// with same source/destination and acceptance conditions.  This
	// is the goal of the `dests' hash.
	//
	// Note that this is still not optimal.  For instance it is
	// better to encode `f U g' as
	//     r(f U g) = g + a(g).r(X(f U g)).f.!g
	// because that leads to a deterministic automaton.  In order
	// to handle this, we take the conditions of any transition
	// going to true (it's `g' here), and remove it from the other
	// transitions.
	//
	// In `exprop' mode, considering all possible combinations of
	// outgoing propositions generalizes the above trick.
	dest_map dests;

	// Compute all outgoing arcs.

	// If EXPROP is set, we will refine the symbolic
	// representation of the successors for all combinations of
	// the atomic properties involved in the formula.
	// VAR_SET is the set of these properties.
	bdd var_set = bdd_existcomp(bdd_support(res), d.var_set);
	// ALL_PROPS is the combinations we have yet to consider.
	// We used to start with `all_props = bddtrue', but it is
	// more efficient to start with the set of all satisfiable
	// variables combinations.
	bdd all_props = bdd_existcomp(res, d.var_set);
	while (all_props != bddfalse)
	  {
	    bdd one_prop_set = bddtrue;
	    if (exprop)
	      one_prop_set = bdd_satoneset(all_props, var_set, bddtrue);
	    all_props -= one_prop_set;

	    typedef std::map<bdd, const formula*, bdd_less_than> succ_map;
	    succ_map succs;

	    // Compute prime implicants.
	    // The reason we use prime implicants and not bdd_satone()
	    // is that we do not want to get any negation in front of Next
	    // or Acc variables.  We wouldn't know what to do with these.
	    // We never added negations in front of these variables when
	    // we built the BDD, so prime implicants will not "invent" them.
	    //
	    // FIXME: minato_isop is quite expensive, and I (=adl)
	    // don't think we really care that much about getting the
	    // smalled sum of products that minato_isop strives to
	    // compute.  Given that Next and Acc variables should
	    // always be positive, maybe there is a faster way to
	    // compute the successors?  E.g. using bdd_satone() and
	    // ignoring negated Next and Acc variables.
	    minato_isop isop(res & one_prop_set);
	    bdd cube;
	    while ((cube = isop.next()) != bddfalse)
	      {
		bdd label = bdd_exist(cube, d.next_set);
		bdd dest_bdd = bdd_existcomp(cube, d.next_set);
		const formula* dest = d.conj_bdd_to_formula(dest_bdd);

		// Simplify the formula, if requested.
		if (simplifier)
		  {
		    formula* tmp = simplifier->simplify(dest);
		    dest->destroy();
		    dest = tmp;
		    // Ignore the arc if the destination reduces to false.
		    if (dest == constant::false_instance())
		      continue;
		  }

		// If we already know a state with the same
		// successors, use it in lieu of the current one.
		if (symb_merge)
		  dest = fc.canonize(dest);

		// If we are not postponing the branching, we can
		// declare the outgoing transitions immediately.
		// Otherwise, we merge transitions with identical
		// label, and declare the outgoing transitions in a
		// second loop.
		if (!branching_postponement)
		  {
		    fill_dests(d, dests, label, dest);
		  }
		else
		  {
		    succ_map::iterator si = succs.find(label);
		    if (si == succs.end())
		      succs[label] = dest;
		    else
		      si->second =
			multop::instance(multop::Or,
					 const_cast<formula*>(si->second),
					 const_cast<formula*>(dest));
		  }
	      }
	    if (branching_postponement)
	      for (succ_map::const_iterator si = succs.begin();
		   si != succs.end(); ++si)
		fill_dests(d, dests, si->first, si->second);
	  }

	// Check for an arc going to 1 (True).  Register it first, that
	// way it will be explored before others during model checking.
	dest_map::const_iterator i = dests.find(constant::true_instance());
	// COND_FOR_TRUE is the conditions of the True arc, so we
	// can remove them from all other arcs.  It might sounds that
	// this is not needed when exprop is used, but in fact it is
	// complementary.
	//
	// Consider
	//   f = r(X(1) R p) = p.(1 + r(X(1) R p))
	// with exprop the two outgoing arcs would be
        //         p               p
	//     f ----> 1       f ----> f
	//
	// where in fact we could output
        //         p
	//     f ----> 1
	//
	// because there is no point in looping on f if we can go to 1.
	bdd cond_for_true = bddfalse;
	if (i != dests.end())
	  {
	    // When translating LTL for an event-based logic with
	    // unobservable events, the 1 state should accept all events,
	    // even unobservable events.
	    if (unobs && now == constant::true_instance())
	      cond_for_true = all_events;
	    else
	      {
		// There should be only one transition going to 1 (true) ...
		assert(i->second.size() == 1);
		prom_map::const_iterator j = i->second.begin();
		// ... and it is not expected to make any promises (unless
		// fair loop approximations are used).
		assert(fair_loop_approx || j->first == bddtrue);
		cond_for_true = j->second;
	      }
	    if (!a->has_state(constant::true_instance()))
	      formulae_to_translate.insert(constant::true_instance());
	    state_explicit_formula::transition* t =
	      a->create_transition(now, constant::true_instance());
	    a->add_condition(t, d.bdd_to_formula(cond_for_true));
	  }
	// Register other transitions.
	for (i = dests.begin(); i != dests.end(); ++i)
	  {
	    const formula* dest = i->first;
	    // The cond_for_true optimization can cause some
	    // transitions to be removed.  So we have to remember
	    // whether a formula is actually reachable.
	    bool reachable = false;

	    // Will this be a new state?
	    bool seen = a->has_state(dest);

	    if (dest != constant::true_instance())
	      {
		for (prom_map::const_iterator j = i->second.begin();
		     j != i->second.end(); ++j)
		  {
		    bdd cond = j->second - cond_for_true;
		    if (cond == bddfalse) // Skip false transitions.
		      continue;
		    state_explicit_formula::transition* t =
		      a->create_transition(now, dest);
		    a->add_condition(t, d.bdd_to_formula(cond));
		    d.conj_bdd_to_acc(a, j->first, t);
		    reachable = true;
		  }
	      }
	    else
	      {
		// "1" is reachable.
		reachable = true;
	      }
	    if (reachable && !seen)
	      formulae_to_translate.insert(dest);
	    else
	      dest->destroy();
	  }
      }

    // Turn all promises into real acceptance conditions.
    a->complement_all_acceptance_conditions();
    return a;
  }

}
