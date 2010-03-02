// Copyright (C) 2009, 2010 Laboratoire de Recherche et Dï¿½veloppement
// de l'Epita (LRDE).
// Copyright (C) 2003, 2004, 2005 Laboratoire d'Informatique de
// Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
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
#include <utility>
#include <algorithm>
#include <iostream>
#include "multop.hh"
#include "constant.hh"
#include "visitor.hh"
#include "ltlvisit/consterm.hh"

namespace spot
{
  namespace ltl
  {
    multop::multop(type op, vec* v)
      : op_(op), children_(v)
    {
    }

    multop::~multop()
    {
      // Get this instance out of the instance map.
      pair p(op(), children_);
      map::iterator i = instances.find(p);
      assert (i != instances.end());
      instances.erase(i);

      // Dereference children.
      for (unsigned n = 0; n < size(); ++n)
	nth(n)->destroy();

      delete children_;
    }

    std::string
    multop::dump() const
    {
      std::string r = "multop(";
      r += op_name();
      unsigned max = size();
      for (unsigned n = 0; n < max; ++n)
	r += ", " + nth(n)->dump();
      r += ")";
      return r;
    }

    void
    multop::accept(visitor& v)
    {
      v.visit(this);
    }

    void
    multop::accept(const_visitor& v) const
    {
      v.visit(this);
    }

    unsigned
    multop::size() const
    {
      return children_->size();
    }

    const formula*
    multop::nth(unsigned n) const
    {
      return (*children_)[n];
    }

    formula*
    multop::nth(unsigned n)
    {
      return (*children_)[n];
    }

    multop::type
    multop::op() const
    {
      return op_;
    }

    const char*
    multop::op_name() const
    {
      switch (op_)
	{
	case And:
	  return "And";
	case Or:
	  return "Or";
	case Concat:
	  return "Concat";
	case Fusion:
	  return "Fusion";
	}
      // Unreachable code.
      assert(0);
      return 0;
    }

    multop::map multop::instances;

    // We match equivalent formulae modulo "ACI rules"
    // (i.e. associativity, commutativity and idempotence of the
    // operator).  For instance If `+' designate the OR operator and
    // `0' is false (the neutral element for `+') , then `f+f+0' is
    // equivalent to `f'.
    formula*
    multop::instance(type op, vec* v)
    {
      // Inline children of same kind.
      //
      // When we construct a formula such as Multop(Op,X,Multop(Op,Y,Z))
      // we will want to inline it as Multop(Op,X,Y,Z).
      {
	vec inlined;
	vec::iterator i = v->begin();
	while (i != v->end())
	  {
	    multop* p = dynamic_cast<multop*>(*i);
	    if (p && p->op() == op)
	      {
		unsigned ps = p->size();
		for (unsigned n = 0; n < ps; ++n)
		  inlined.push_back(p->nth(n)->clone());
		(*i)->destroy();
		i = v->erase(i);
	      }
	    else
	      {
		// All operator except "Concat" and "Fusion" are
		// commutative, so we just keep a list of the inlined
		// arguments that should later be added to the vector.
		// For concat we have to keep track of the order of
		// all the arguments.
		if (op == Concat || op == Fusion)
		  inlined.push_back(*i);
		++i;
	      }
	  }
	if (op == Concat || op == Fusion)
	  *v = inlined;
	else
	  v->insert(v->end(), inlined.begin(), inlined.end());
      }

      if (op != Concat && op != Fusion)
	std::sort(v->begin(), v->end(), formula_ptr_less_than());

      formula* neutral;
      formula* abs;
      formula* abs2;
      formula* weak_abs;
      switch (op)
	{
	case And:
	  neutral = constant::true_instance();
	  abs = constant::false_instance();
	  abs2 = 0;
	  weak_abs = constant::empty_word_instance();
	  break;
	case Or:
	  neutral = constant::false_instance();
	  abs = constant::true_instance();
	  abs2 = 0;
	  weak_abs = 0;
	  break;
	case Concat:
	  neutral = constant::empty_word_instance();
	  abs = constant::false_instance();
	  abs2 = 0;
	  weak_abs = 0;
	  break;
	case Fusion:
	  neutral = constant::true_instance();
	  abs = constant::false_instance();
	  abs2 = constant::empty_word_instance();
	  weak_abs = 0;
	  break;

	default:
	  neutral = 0;
	  abs = 0;
	  abs2 = 0;
	  weak_abs = 0;
	  break;
	}

      // Remove duplicates (except for Concat).  We can't use
      // std::unique(), because we must destroy() any formula we drop.
      // Also ignore neutral elements and handle absorbent elements.
      {
	formula* last = 0;
	vec::iterator i = v->begin();
	bool weak_abs_seen = false;
	while (i != v->end())
	  {
	    if ((*i == neutral) || (*i == last))
	      {
		(*i)->destroy();
		i = v->erase(i);
	      }
	    else if (*i == abs || *i == abs2)
	      {
		for (i = v->begin(); i != v->end(); ++i)
		  (*i)->destroy();
		delete v;
		return abs;
	      }
	    else
	      {
		if (*i == weak_abs)
		  weak_abs_seen = true;
		if (op != Concat) // Don't remove duplicates for Concat.
		  last = *i;
		++i;
	      }
	  }
	// We have    a* & #e & 0  = 0  // already checked above
	//     but    a* & #e & c*  = #e
	// So if #e has been seen, check if all term recognize the
	// empty word.
	if (weak_abs_seen)
	  {
	    bool acc_empty = true;
	    for (i = v->begin(); i != v->end(); ++i)
	      {
		if (acc_empty)
		  acc_empty = constant_term_as_bool(*i);
		(*i)->destroy();
	      }
	    delete v;
	    if (acc_empty)
	      return weak_abs;
	    else
	      return constant::false_instance();
	  }
      }

      vec::size_type s = v->size();
      if (s == 0)
	{
	  delete v;
	  assert(neutral != 0);
	  return neutral;
	}
      else if (s == 1)
	{
	  // Simply replace Multop(Op,X) by X.
	  formula* res = (*v)[0];
	  delete v;
	  return res;
	}

      // The hash key.
      pair p(op, v);

      map::iterator i = instances.find(p);
      if (i != instances.end())
	{
	  // The instance already exists.
	  for (vec::iterator vi = v->begin(); vi != v->end(); ++vi)
	    (*vi)->destroy();
	  delete v;
	  return static_cast<multop*>(i->second->clone());
	}

      // This is the first instance of this formula.

      // Record the instance in the map,
      multop* ap = new multop(op, v);
      instances[p] = ap;
      return ap->clone();
    }

    formula*
    multop::instance(type op, formula* first, formula* second)
    {
      vec* v = new vec;
      v->push_back(first);
      v->push_back(second);
      return instance(op, v);
    }

    unsigned
    multop::instance_count()
    {
      return instances.size();
    }

    std::ostream&
    multop::dump_instances(std::ostream& os)
    {
      for (map::iterator i = instances.begin(); i != instances.end(); ++i)
	{
	  os << i->second << " = "
	     << i->second->ref_count_() << " * "
	     << i->second->dump()
	     << std::endl;
	}
      return os;
    }

  }
}
