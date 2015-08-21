// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.


#include "unabbrev.hh"
#include "ltlast/allnodes.hh"
#include <cassert>

namespace spot
{
  namespace ltl
  {
    unabbreviator::unabbreviator(const char* opt)
    {
      while (*opt)
	switch (char c = *opt++)
	  {
	  case 'e':
	    re_e_ = true;
	    re_some_bool_ = true;
	    break;
	  case 'F':
	    re_f_ = true;
	    re_some_f_g_ = true;
	    break;
	  case 'G':
	    re_g_ = true;
	    re_some_f_g_ = true;
	    break;
	  case 'i':
	    re_i_ = true;
	    re_some_bool_ = true;
	    break;
	  case 'M':
	    re_m_ = true;
	    re_some_other_ = true;
	    break;
	  case 'R':
	    re_r_ = true;
	    re_some_other_ = true;
	    break;
	  case 'W':
	    re_w_ = true;
	    re_some_other_ = true;
	    break;
	  case '^':
	    re_xor_ = true;
	    re_some_bool_ = true;
	    break;
	  default:
	    throw std::runtime_error
	      (std::string("unknown unabbreviation option: ")
	       + c);
	  }
    }

    unabbreviator::~unabbreviator()
    {
      auto i = cache_.begin();
      auto end = cache_.end();
      while (i != end)
	{
	  auto old = i++;
	  old->second->destroy();
	  old->first->destroy();
	}
    }


    const formula* unabbreviator::run(const formula* in)
    {
      auto entry = cache_.emplace(in, nullptr);
      if (!entry.second)
	return entry.first->second->clone();
      in->clone();

      // Skip recursion whenever possible
      bool no_boolean_rewrite = !re_some_bool_ || in->is_sugar_free_boolean();
      bool no_f_g_rewrite = !re_some_f_g_ || in->is_sugar_free_ltl();
      if (no_boolean_rewrite
	  && (in->is_boolean() || (no_f_g_rewrite && !re_some_other_)))
	{
	  entry.first->second = in->clone();
	  return in->clone();
	}

      const formula* out = nullptr;
      switch (in->kind())
	{
	case formula::AtomicProp:
	case formula::Constant:
	  out = in->clone();
	  break;
	case formula::UnOp:
	  {
	    const unop* uo = static_cast<const unop*>(in);
	    auto c = run(uo->child());
	    switch (auto op = uo->op())
	      {
		//  F f = true U f
	      case unop::F:
		if (!re_f_)
		  goto unop_clone;
		out = binop::instance(binop::U, constant::true_instance(), c);
		break;
		//  G f = false R f
		//  G f = f W false
		//  G f = !F!f
		//  G f = !(true U !f)
	      case unop::G:
		if (!re_g_)
		  goto unop_clone;
		if (!re_r_)
		  {
		    out = binop::instance(binop::R,
					  constant::false_instance(), c);
		    break;
		  }
		if (!re_w_)
		  {
		    out = binop::instance(binop::W,
					  c, constant::false_instance());
		    break;
		  }
		{
		  auto nc = unop::instance(unop::Not, c);
		  if (!re_f_)
		    {
		      out = unop::instance(unop::Not,
					   unop::instance(unop::F, nc));
		      break;
		    }
		  auto u = binop::instance(binop::U,
					   constant::true_instance(), nc);
		  out = unop::instance(unop::Not, u);
		  break;
		}
	      case unop::Not:
	      case unop::X:
	      case unop::Closure:
	      case unop::NegClosure:
	      case unop::NegClosureMarked:
		unop_clone:
		out = unop::instance(op, c);
		break;
	      }
	    break;
	  }
	case formula::BinOp:
	  {
	    const binop* bo = static_cast<const binop*>(in);
	    auto f1 = run(bo->first());
	    auto f2 = run(bo->second());
	    switch (auto op = bo->op())
	      {
		// f1 ^ f2  ==  !(f1 <-> f2)
		// f1 ^ f2  ==  (f1 & !f2) | (f2 & !f1)
	      case binop::Xor:
		{
		  if (!re_xor_)
		    goto binop_clone;
		  if (!re_e_)
		    {
		      out = unop::instance(unop::Not,
					   binop::instance(binop::Equiv,
							   f1, f2));
		    }
		  else
		    {
		      auto a = multop::instance(multop::And, f1->clone(),
						unop::instance(unop::Not,
							       f2->clone()));
		      auto b = multop::instance(multop::And, f2,
						unop::instance(unop::Not, f1));
		      out = multop::instance(multop::Or, a, b);
		    }
		  break;
		}
		// f1 => f2  ==  !f1 | f2
	      case binop::Implies:
		if (!re_i_)
		  goto binop_clone;
		out = multop::instance(multop::Or,
				       unop::instance(unop::Not, f1), f2);
		break;
		// f1 <=> f2  ==  (f1 & f2) | (!f1 & !f2)
	      case binop::Equiv:
		if (!re_e_)
		  goto binop_clone;
		{
		  auto nf1 = unop::instance(unop::Not, f1->clone());
		  auto nf2 = unop::instance(unop::Not, f2->clone());
		  auto term1 = multop::instance(multop::And, f1, f2);
		  auto term2 = multop::instance(multop::And, nf1, nf2);
		  out = multop::instance(multop::Or, term1, term2);
		  break;
		}
		// f1 W f2 = f2 R (f2 | f1)
		// f1 W f2 = f1 U (f2 | G f1)
		// f1 W f2 = f1 U (f2 | !F !f1)
		// f1 W f2 = f1 U (f2 | !(1 U !f1))
	      case binop::W:
		if (!re_w_)
		  goto binop_clone;
		if (!re_r_)
		  {
		    out = binop::instance(binop::R, f2,
					  multop::instance(multop::Or,
							   f2->clone(), f1));
		    break;
		  }
		f1->clone();
		out = unop::instance(unop::G, f1);
		if (re_g_)
		  {
		    auto tmp = out;
		    out = run(out);
		    tmp->destroy();
		  }
		out = binop::instance(binop::U, f1,
				      multop::instance(multop::Or, f2, out));
		break;
		// f1 M f2 = f2 U (g2 & f1)
	      case binop::M:
		if (!re_m_)
		  goto binop_clone;
		out = binop::instance(binop::U, f2,
				      multop::instance(multop::And,
						       f2->clone(), f1));
		break;
		// f1 R f2 = f2 W (f1 & f2)
		// f1 R f2 = f2 U ((f1 & f2) | Gf2)
		// f1 R f2 = f2 U ((f1 & f2) | !F!f2)
		// f1 R f2 = f2 U ((f1 & f2) | !(1 U !f2))
	      case binop::R:
		if (!re_r_)
		  goto binop_clone;
		{
		  auto f12 = multop::instance(multop::And, f1, f2->clone());
		  if (!re_w_)
		    {
		      out = binop::instance(binop::W, f2, f12);
		      break;
		    }
		  out = unop::instance(unop::G, f2->clone());
		  if (re_g_)
		    {
		      auto tmp = out;
		      out = run(tmp);
		      tmp->destroy();
		    }
		  out = binop::instance(binop::U, f2,
					multop::instance(multop::Or, f12, out));
		}
		break;
	      case binop::U:
	      case binop::UConcat:
	      case binop::EConcat:
	      case binop::EConcatMarked:
		binop_clone:
		out = binop::instance(op, f1, f2);
		break;
	      }
	    break;
	  }
	case formula::MultOp:
	  {
	    const multop* mo = static_cast<const multop*>(in);
	    multop::vec* res = new multop::vec;
	    unsigned mos = mo->size();
	    res->reserve(mos);
	    for (unsigned i = 0; i < mos; ++i)
	      res->push_back(run(mo->nth(i)));
	    out = multop::instance(mo->op(), res);
	    break;
	  }
	case formula::BUnOp:
	  {
	    const bunop* bo = static_cast<const bunop*>(in);
	    out = bunop::instance(bo->op(), run(bo->child()),
				  bo->min(), bo->max());
	    break;
	  }
      }

      assert(out != nullptr);

      entry.first->second = out;
      return out->clone();
    }

    const formula* unabbreviate(const formula* in, const char* opt)
    {
      unabbreviator un(opt);
      return un.run(in);
    }
  }
}
