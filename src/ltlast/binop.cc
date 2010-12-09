// Copyright (C) 2009, 2010 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
// Copyright (C) 2003, 2005 Laboratoire d'Informatique de Paris
// 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
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
#include "binop.hh"
#include "unop.hh"
#include "constant.hh"
#include "visitor.hh"
#include <iostream>

namespace spot
{
  namespace ltl
  {
    binop::binop(type op, formula* first, formula* second)
      : op_(op), first_(first), second_(second)
    {
      // Beware: (f U g) is purely eventual if both operands
      // are purely eventual, unlike in the proceedings of
      // Concur'00.  (The revision of the paper available at
      // http://www.bell-labs.com/project/TMP/ is fixed.)  See
      // also http://arxiv.org/abs/1011.4214 for a discussion
      // about this problem.  (Which we fixed in 2005 thanks
      // to LBTT.)

      // This means that we can use the following line to handle
      // all cases of (f U g), (f R g), (f W g), (f M g) for
      // universality and eventuality.
      props = first->get_props() & second->get_props();

      switch (op)
	{
	case Xor:
	case Implies:
	case Equiv:
	  is.sugar_free_boolean = false;
	  is.in_nenoform = false;
	  is.accepting_eword = false;
	  break;
	case EConcatMarked:
	  is.not_marked = false;
	  // fall through
	case EConcat:
	case UConcat:
	  is.ltl_formula = false;
	  is.boolean = false;
	  is.eltl_formula = false;
	  is.accepting_eword = false;
	  break;
	case U:
	  // 1 U a = Fa
	  if (first == constant::true_instance())
	    is.eventual = 1;
	  is.boolean = false;
	  is.eltl_formula = false;
	  is.accepting_eword = false;
	  break;
	case W:
	  // a W 0 = Ga
	  if (second == constant::false_instance())
	    is.universal = 1;
	  is.boolean = false;
	  is.eltl_formula = false;
	  is.accepting_eword = false;
	  break;
	case R:
	  // 0 R a = Ga
	  if (first == constant::false_instance())
	    is.universal = 1;
	  is.boolean = false;
	  is.eltl_formula = false;
	  is.accepting_eword = false;
	  break;
	case M:
	  // a M 1 = Fa
	  if (second == constant::true_instance())
	    is.eventual = 1;
	  is.boolean = false;
	  is.eltl_formula = false;
	  is.accepting_eword = false;
	  break;
	}
    }

    binop::~binop()
    {
      // Get this instance out of the instance map.
      pairf pf(first(), second());
      pair p(op(), pf);
      map::iterator i = instances.find(p);
      assert (i != instances.end());
      instances.erase(i);

      // Dereference children.
      first()->destroy();
      second()->destroy();
    }

    std::string
    binop::dump() const
    {
      return (std::string("binop(") + op_name()
	      + ", " + first()->dump()
	      + ", " + second()->dump() + ")");
    }

    void
    binop::accept(visitor& v)
    {
      v.visit(this);
    }

    void
    binop::accept(const_visitor& v) const
    {
      v.visit(this);
    }

    const formula*
    binop::first() const
    {
      return first_;
    }

    formula*
    binop::first()
    {
      return first_;
    }

    const formula*
    binop::second() const
    {
      return second_;
    }

    formula*
    binop::second()
    {
      return second_;
    }

    binop::type
    binop::op() const
    {
      return op_;
    }

    const char*
    binop::op_name() const
    {
      switch (op_)
	{
	case Xor:
	  return "Xor";
	case Implies:
	  return "Implies";
	case Equiv:
	  return "Equiv";
	case U:
	  return "U";
	case R:
	  return "R";
	case W:
	  return "W";
	case M:
	  return "M";
	case EConcat:
	  return "EConcat";
	case EConcatMarked:
	  return "EConcatMarked";
	case UConcat:
	  return "UConcat";
	}
      // Unreachable code.
      assert(0);
      return 0;
    }

    binop::map binop::instances;

    formula*
    binop::instance(type op, formula* first, formula* second)
    {
      // Sort the operands of commutative operators, so that for
      // example the formula instance for 'a xor b' is the same as
      // that for 'b xor a'.

      // Trivial identities:
      switch (op)
	{
	case Xor:
	  {
	    // Xor is commutative: sort operands.
	    formula_ptr_less_than cmp;
	    if (cmp(second, first) > 0)
	      std::swap(first, second);
	  }
	  //   - (1 ^ Exp) = !Exp
	  //   - (0 ^ Exp) = Exp
	  if (first == constant::true_instance())
	    return unop::instance(unop::Not, second);
	  if (first == constant::false_instance())
	    return second;
	  if (first == second)
	    {
	      first->destroy();
	      second->destroy();
	      return constant::false_instance();
	    }
	  // We expect constants to appear first, because they are
	  // instantiated first.
	  assert(second != constant::false_instance());
	  assert(second != constant::true_instance());
	  break;
	case Equiv:
	  {
	    // Equiv is commutative: sort operands.
	    formula_ptr_less_than cmp;
	    if (cmp(second, first) > 0)
	      std::swap(first, second);
	  }
	  //   - (0 <=> Exp) = !Exp
	  //   - (1 <=> Exp) = Exp
	  //   - (Exp <=> Exp) = 1
	  if (first == constant::false_instance())
	    return unop::instance(unop::Not, second);
	  if (first == constant::true_instance())
	    return second;
	  if (first == second)
	    {
	      first->destroy();
	      second->destroy();
	      return constant::true_instance();
	    }
	  // We expect constants to appear first, because they are
	  // instantiated first.
	  assert(second != constant::false_instance());
	  assert(second != constant::true_instance());
	  break;
	case Implies:
	  //   - (1 => Exp) = Exp
	  //   - (0 => Exp) = 1
	  //   - (Exp => 1) = 1
	  //   - (Exp => 0) = !Exp
	  //   - (Exp => Exp) = 1
	  if (first == constant::true_instance())
	    return second;
	  if (first == constant::false_instance())
	    {
	      second->destroy();
	      return constant::true_instance();
	    }
	  if (second == constant::true_instance())
	    {
	      first->destroy();
	      return second;
	    }
	  if (second == constant::false_instance())
	    return unop::instance(unop::Not, first);
	  if (first == second)
	    {
	      first->destroy();
	      second->destroy();
	      return constant::true_instance();
	    }
	  break;
	case U:
	  //   - (Exp U 1) = 1
	  //   - (Exp U 0) = 0
	  //   - (0 U Exp) = Exp
	  //   - (Exp U Exp) = Exp
	  if (second == constant::true_instance()
	      || second == constant::false_instance()
	      || first == constant::false_instance()
	      || first == second)
	    {
	      first->destroy();
	      return second;
	    }
	  break;
	case W:
	  //   - (Exp W 1) = 1
	  //   - (0 W Exp) = Exp
	  //   - (1 W Exp) = 1
	  //   - (Exp W Exp) = Exp
	  if (second == constant::true_instance()
	      || first == constant::false_instance()
	      || first == second)
	    {
	      first->destroy();
	      return second;
	    }
	  if (first == constant::true_instance())
	    {
	      second->destroy();
	      return first;
	    }
	  break;
	case R:
	  //   - (Exp R 1) = 1
	  //   - (Exp R 0) = 0
	  //   - (1 R Exp) = Exp
	  //   - (Exp R Exp) = Exp
	  if (second == constant::true_instance()
	      || second == constant::false_instance()
	      || first == constant::true_instance()
	      || first == second)
	    {
	      first->destroy();
	      return second;
	    }
	  break;
	case M:
	  //   - (Exp M 0) = 0
	  //   - (1 M Exp) = Exp
	  //   - (0 M Exp) = 0
	  //   - (Exp M Exp) = Exp
	  if (second == constant::false_instance()
	      || first == constant::true_instance()
	      || first == second)
	    {
	      first->destroy();
	      return second;
	    }
	  if (first == constant::false_instance())
	    {
	      second->destroy();
	      return first;
	    }
	  break;
	case EConcat:
	case EConcatMarked:
	  //   - 0 <>-> Exp = 0
	  //   - 1 <>-> Exp = Exp
	  //   - [*0] <>-> Exp = 0
	  //   - Exp <>-> 0 = 0
	  if (first == constant::true_instance())
	    return second;
	  if (first == constant::false_instance()
	      || first == constant::empty_word_instance())
	    {
	      second->destroy();
	      return constant::false_instance();
	    }
	  if (second == constant::false_instance())
	    {
	      first->destroy();
	      return second;
	    }
	  break;
	case UConcat:
	  //   - 0 []-> Exp = 1
	  //   - 1 []-> Exp = Exp
	  //   - [*0] []-> Exp = 1
	  //   - Exp []-> 1 = 1
	  if (first == constant::true_instance())
	    return second;
	  if (first == constant::false_instance()
	      || first == constant::empty_word_instance())
	    {
	      second->destroy();
	      return constant::true_instance();
	    }
	  if (second == constant::true_instance())
	    {
	      first->destroy();
	      return second;
	    }
	  break;
	}

      pairf pf(first, second);
      pair p(op, pf);
      map::iterator i = instances.find(p);
      if (i != instances.end())
	{
	  // This instance already exists.
	  first->destroy();
	  second->destroy();
	  return static_cast<binop*>(i->second->clone());
	}
      binop* ap = new binop(op, first, second);
      instances[p] = ap;
      return static_cast<binop*>(ap->clone());
    }

    unsigned
    binop::instance_count()
    {
      return instances.size();
    }

    std::ostream&
    binop::dump_instances(std::ostream& os)
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
