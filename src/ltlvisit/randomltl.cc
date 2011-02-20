// Copyright (C) 2008, 2009, 2010, 2011 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2005 Laboratoire d'Informatique de Paris 6
// (LIP6), département Systèmes Répartis Coopératifs (SRC), Université
// Pierre et Marie Curie.
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
#include <algorithm>
#include "randomltl.hh"
#include "ltlast/allnodes.hh"
#include "misc/random.hh"
#include <iostream>
#include <cstring>

namespace spot
{
  namespace ltl
  {
    namespace
    {
      static formula*
      ap_builder(const random_formula* rl, int n)
      {
	assert(n == 1);
	(void) n;
	atomic_prop_set::const_iterator i = rl->ap()->begin();
	std::advance(i, mrand(rl->ap()->size()));
	return (*i)->clone();
      }

      static formula*
      true_builder(const random_formula*, int n)
      {
	assert(n == 1);
	(void) n;
	return constant::true_instance();
      }

      static formula*
      boolform_builder(const random_formula* rl, int n)
      {
	assert(n >= 1);
	const random_sere* rs = static_cast<const random_sere*>(rl);
	return rs->rb.generate(n);
      }

      static formula*
      false_builder(const random_formula*, int n)
      {
	assert(n == 1);
	(void) n;
	return constant::false_instance();
      }

      static formula*
      eword_builder(const random_formula*, int n)
      {
	assert(n == 1);
	(void) n;
	return constant::empty_word_instance();
      }

      template <unop::type Op>
      static formula*
      unop_builder(const random_formula* rl, int n)
      {
	assert(n >= 2);
	return unop::instance(Op, rl->generate(n - 1));
      }

      static formula*
      closure_builder(const random_formula* rl, int n)
      {
	assert(n >= 2);
	const random_psl* rp = static_cast<const random_psl*>(rl);
	return unop::instance(unop::Closure, rp->rs.generate(n - 1));
      }

      template <binop::type Op>
      static formula*
      binop_builder(const random_formula* rl, int n)
      {
	assert(n >= 3);
	--n;
	int l = rrand(1, n - 1);
	return binop::instance(Op, rl->generate(l), rl->generate(n - l));
      }

      template <binop::type Op>
      static formula*
      binop_SERELTL_builder(const random_formula* rl, int n)
      {
	assert(n >= 3);
	--n;
	const random_psl* rp = static_cast<const random_psl*>(rl);
	int l = rrand(1, n - 1);
	return binop::instance(Op, rp->rs.generate(l), rl->generate(n - l));
      }

      template <bunop::type Op>
      static formula*
      bunop_unbounded_builder(const random_formula* rl, int n)
      {
	assert(n >= 2);
	return bunop::instance(Op, rl->generate(n - 1));
      }

      template <bunop::type Op>
      static formula*
      bunop_bounded_builder(const random_formula* rl, int n)
      {
	assert(n >= 2);
	int min = rrand(0, 3);
	int max = rrand(min, 4);
	return bunop::instance(Op, rl->generate(n - 1), min, max);
      }

      template <bunop::type Op>
      static formula*
      bunop_bool_bounded_builder(const random_formula* rl, int n)
      {
	assert(n >= 2);
	int min = rrand(0, 3);
	int max = rrand(min, 4);
	const random_sere* rp = static_cast<const random_sere*>(rl);
	return bunop::instance(Op, rp->rb.generate(n - 1), min, max);
      }


      template <multop::type Op>
      static formula*
      multop_builder(const random_formula* rl, int n)
      {
	assert(n >= 3);
	--n;
	int l = rrand(1, n - 1);
	return multop::instance(Op, rl->generate(l), rl->generate(n - l));
      }

    } // anonymous

    void
    random_formula::op_proba::setup(const char* name, int min_n, builder build)
    {
      this->name = name;
      this->min_n = min_n;
      this->proba = 1.0;
      this->build = build;
    }

    void
    random_formula::update_sums()
    {
      total_1_ = 0.0;
      total_2_ = 0.0;
      total_2_and_more_ = 0.0;
      for (unsigned i = 0; i < proba_size_; ++i)
	{
	  if (proba_[i].min_n == 1)
	    {
	      total_1_ += proba_[i].proba;
	      if (proba_ + i >= proba_2_)
		total_2_ += proba_[i].proba;
	      if (proba_ + i >= proba_2_or_more_)
		total_2_and_more_ += proba_[i].proba;
	    }
	  else if (proba_[i].min_n == 2)
	    {
	      total_2_ += proba_[i].proba;
	      if (proba_ + i >= proba_2_or_more_)
		  total_2_and_more_ += proba_[i].proba;
	    }
	  else if (proba_[i].min_n > 2)
	    total_2_and_more_ += proba_[i].proba;
	  else
	    assert(!"unexpected max_n");
	}
      assert(total_1_ != 0.0);
      assert(total_2_ != 0.0);
      assert(total_2_and_more_ != 0.0);
    }

    formula*
    random_formula::generate(int n) const
    {
      assert(n > 0);

      double r = drand();
      op_proba* p;

      if (n == 1)
	{
	  r *= total_1_;
	  p = proba_;
	}
      else if (n == 2)
	{
	  r *= total_2_;
	  p = proba_2_;
	}
      else
	{
	  r *= total_2_and_more_;
	  p = proba_2_or_more_;
	}

      double s = p->proba;
      while (s < r)
	{
	  ++p;
	  s += p->proba;
	}

      return p->build(this, n);
    }

    const char*
    random_formula::parse_options(char* options)
    {
      char* key = strtok(options, "=\t, :;");
      while (key)
	{
	  char* value = strtok(0, "=\t, :;");
	  if (value == 0)
	    return key;

	  char* endptr;
	  double res = strtod(value, &endptr);
	  if (*endptr)
	    return value;

	  unsigned i;
	  for (i = 0; i < proba_size_; ++i)
	    {
	      if (('a' <= *proba_[i].name && *proba_[i].name <= 'z'
		   && !strcasecmp(proba_[i].name, key))
		  || !strcmp(proba_[i].name, key))
		{
		  proba_[i].proba = res;
		  break;
		}
	    }
	  if (i == proba_size_)
	    return key;

	  key = strtok(0, "=\t, :;");
	}
      update_sums();
      return 0;
    }

    std::ostream&
    random_formula::dump_priorities(std::ostream& os) const
    {
      for (unsigned i = 0; i < proba_size_; ++i)
	os << proba_[i].name << "\t" << proba_[i].proba << std::endl;
      return os;
    }

    // SEREs
    random_sere::random_sere(const atomic_prop_set* ap)
      : random_formula(11, ap), rb(ap)
    {
      proba_[0].setup("eword",   1, eword_builder);
      proba_2_ = proba_ + 1;
      proba_2_or_more_ = proba_ + 1;
      proba_[1].setup("boolform", 1, boolform_builder);
      proba_[2].setup("star",    2, bunop_unbounded_builder<bunop::Star>);
      proba_[3].setup("star_b",  2, bunop_bounded_builder<bunop::Star>);
      proba_[4].setup("equal_b", 2, bunop_bool_bounded_builder<bunop::Equal>);
      proba_[5].setup("goto_b",  2, bunop_bool_bounded_builder<bunop::Goto>);
      proba_[6].setup("and",     3, multop_builder<multop::And>);
      proba_[7].setup("andNLM",  3, multop_builder<multop::AndNLM>);
      proba_[8].setup("or",      3, multop_builder<multop::Or>);
      proba_[9].setup("concat",  3, multop_builder<multop::Concat>);
      proba_[10].setup("fusion",  3, multop_builder<multop::Fusion>);

      update_sums();
    }

    // Boolean formulae
    random_boolean::random_boolean(const atomic_prop_set* ap)
      : random_formula(9, ap)
    {
      proba_[0].setup("ap",      1, ap_builder);
      proba_[0].proba = ap_->size();
      proba_[1].setup("false",   1, false_builder);
      proba_[2].setup("true",    1, true_builder);
      proba_2_or_more_ = proba_2_ = proba_ + 3;
      proba_[3].setup("not",     2, unop_builder<unop::Not>);
      proba_[4].setup("equiv",   3, binop_builder<binop::Equiv>);
      proba_[5].setup("implies", 3, binop_builder<binop::Implies>);
      proba_[6].setup("xor",     3, binop_builder<binop::Xor>);
      proba_[7].setup("and",     3, multop_builder<multop::And>);
      proba_[8].setup("or",      3, multop_builder<multop::Or>);

      update_sums();
    }

    // LTL formulae
    void
    random_ltl::setup_proba_()
    {
      proba_[0].setup("ap",      1, ap_builder);
      proba_[0].proba = ap_->size();
      proba_[1].setup("false",   1, false_builder);
      proba_[2].setup("true",    1, true_builder);
      proba_2_or_more_ = proba_2_ = proba_ + 3;
      proba_[3].setup("not",     2, unop_builder<unop::Not>);
      proba_[4].setup("F",       2, unop_builder<unop::F>);
      proba_[5].setup("G",       2, unop_builder<unop::G>);
      proba_[6].setup("X",       2, unop_builder<unop::X>);
      proba_[7].setup("equiv",   3, binop_builder<binop::Equiv>);
      proba_[8].setup("implies", 3, binop_builder<binop::Implies>);
      proba_[9].setup("xor",     3, binop_builder<binop::Xor>);
      proba_[10].setup("R",      3, binop_builder<binop::R>);
      proba_[11].setup("U",      3, binop_builder<binop::U>);
      proba_[12].setup("W",      3, binop_builder<binop::W>);
      proba_[13].setup("M",      3, binop_builder<binop::M>);
      proba_[14].setup("and",    3, multop_builder<multop::And>);
      proba_[15].setup("or",     3, multop_builder<multop::Or>);
    }

    random_ltl::random_ltl(const atomic_prop_set* ap)
      : random_formula(16, ap)
    {
      setup_proba_();
      update_sums();
    }

    random_ltl::random_ltl(int size, const atomic_prop_set* ap)
      : random_formula(size, ap)
    {
      setup_proba_();
      // No call to update_sums(), this functions is always
      // called by the random_psl constructor.
    }

    // PSL
    random_psl::random_psl(const atomic_prop_set* ap)
      : random_ltl(19, ap), rs(ap)
    {
      // FIXME: This looks very fragile.
      memmove(proba_ + 8, proba_ + 7,
	      ((proba_ + 16) - (proba_ + 7)) * sizeof(*proba_));

      proba_[7].setup("Closure", 2, closure_builder);
      proba_[17].setup("EConcat", 3, binop_SERELTL_builder<binop::EConcat>);
      proba_[18].setup("UConcat", 3, binop_SERELTL_builder<binop::UConcat>);
      update_sums();
    }

  } // ltl
} // spot
