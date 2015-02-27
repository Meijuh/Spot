// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement de
// l'Epita.
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


#include <iostream>
#include <set>
#include "acc.hh"

namespace spot
{
  std::ostream& operator<<(std::ostream& os, spot::acc_cond::mark_t m)
  {
    auto a = m.id;
    os << '{';
    unsigned level = 0;
    const char* comma = "";
    while (a)
      {
	if (a & 1)
	  {
	    os << comma << level;
	    comma = ",";
	  }
	a >>= 1;
	++level;
      }
    os << '}';
    return os;
  }

  namespace
  {
    static void
    print_code(std::ostream& os,
	       const acc_cond::acc_code& code, unsigned pos)
    {
      const char* op = " | ";
      auto& w = code[pos];
      const char* negated = "";
      bool top = pos == code.size() - 1;
      switch (w.op)
	{
	case acc_cond::acc_op::And:
	  op = " & ";
	case acc_cond::acc_op::Or:
	  {
	    unsigned sub = pos - w.size;
	    if (!top)
	      os << '(';
	    bool first = true;
	    while (sub < pos)
	      {
		--pos;
		if (first)
		  first = false;
		else
		  os << op;
		print_code(os, code, pos);
		pos -= code[pos].size;
	      }
	    if (!top)
	      os << ')';
	  }
	  break;
	case acc_cond::acc_op::InfNeg:
	  negated = "!";
	case acc_cond::acc_op::Inf:
	  {
	    auto a = code[pos - 1].mark.id;
	    if (a == 0U)
	      {
		os << 't';
	      }
	    else
	      {
		if (!top)
		  // Avoid extra parentheses if there is only one set
		  top = code[pos - 1].mark.count() == 1;
		unsigned level = 0;
		const char* and_ = "";
		if (!top)
		  os << '(';
		while (a)
		  {
		    if (a & 1)
		      {
			os << and_ << "Inf(" << negated << level << ')';
			and_ = "&";
		      }
		    a >>= 1;
		    ++level;
		  }
		if (!top)
		  os << ')';
	      }
	  }
	  break;
	case acc_cond::acc_op::FinNeg:
	  negated = "!";
	case acc_cond::acc_op::Fin:
	  {
	    auto a = code[pos - 1].mark.id;
	    if (a == 0U)
	      {
		os << 'f';
	      }
	    else
	      {
		if (!top)
		  // Avoid extra parentheses if there is only one set
		  top = code[pos - 1].mark.count() == 1;
		unsigned level = 0;
		const char* or_ = "";
		if (!top)
		  os << '(';
		while (a)
		  {
		    if (a & 1)
		      {
			os << or_ << "Fin(" << negated << level << ')';
			or_ = "|";
		      }
		    a >>= 1;
		    ++level;
		  }
		if (!top)
		  os << ')';
	      }
	  }
	  break;
	}
    }


    static bool
    eval(acc_cond::mark_t inf, const acc_cond::acc_word* pos)
    {
      switch (pos->op)
	{
	case acc_cond::acc_op::And:
	  {
	    auto sub = pos - pos->size;
	    while (sub < pos)
	      {
		--pos;
		if (!eval(inf, pos))
		  return false;
		pos -= pos->size;
	      }
	    return true;
	  }
	case acc_cond::acc_op::Or:
	  {
	    auto sub = pos - pos->size;
	    while (sub < pos)
	      {
		--pos;
		if (eval(inf, pos))
		  return true;
		pos -= pos->size;
	      }
	    return false;
	  }
	case acc_cond::acc_op::Inf:
	  return (pos[-1].mark & inf) == pos[-1].mark;
	case acc_cond::acc_op::Fin:
	  return (pos[-1].mark & inf) == 0U;
	case acc_cond::acc_op::FinNeg:
	case acc_cond::acc_op::InfNeg:
	  SPOT_UNREACHABLE();
	}
      SPOT_UNREACHABLE();
      return false;
    }

    static acc_cond::mark_t
    eval_sets(acc_cond::mark_t inf, const acc_cond::acc_word* pos)
    {
      switch (pos->op)
	{
	case acc_cond::acc_op::And:
	  {
	    auto sub = pos - pos->size;
	    acc_cond::mark_t m = 0U;
	    while (sub < pos)
	      {
		--pos;
		if (auto s = eval_sets(inf, pos))
		  m |= s;
		else
		  return 0U;
		pos -= pos->size;
	      }
	    return m;
	  }
	case acc_cond::acc_op::Or:
	  {
	    auto sub = pos - pos->size;
	    while (sub < pos)
	      {
		--pos;
		if (auto s = eval_sets(inf, pos))
		  return s;
		pos -= pos->size;
	      }
	    return 0U;
	  }
	case acc_cond::acc_op::Inf:
	  if ((pos[-1].mark & inf) == pos[-1].mark)
	    return pos[-1].mark;
	  else
	    return 0U;
	case acc_cond::acc_op::Fin:
	case acc_cond::acc_op::FinNeg:
	case acc_cond::acc_op::InfNeg:
	  SPOT_UNREACHABLE();
	}
      SPOT_UNREACHABLE();
      return false;
    }
  }

  bool acc_cond::accepting(mark_t inf) const
  {
    if (code_.empty())
      return true;
    return eval(inf, &code_.back());
  }

  acc_cond::mark_t acc_cond::accepting_sets(mark_t inf) const
  {
    if (uses_fin_acceptance())
      throw std::runtime_error
	("Fin acceptance is not supported by this code path.");
    if (code_.empty())
      return 0U;
    return eval_sets(inf, &code_.back());
  }

  bool acc_cond::check_fin_acceptance() const
  {
    if (code_.empty())
      return false;
    unsigned pos = code_.size();
    do
      {
	switch (code_[pos - 1].op)
	  {
	  case acc_cond::acc_op::And:
	  case acc_cond::acc_op::Or:
	    --pos;
	    break;
	  case acc_cond::acc_op::Inf:
	  case acc_cond::acc_op::InfNeg:
	    pos -= 2;
	    break;
	  case acc_cond::acc_op::Fin:
	    if (code_[pos - 2].mark == 0U) // f
	      {
		pos -= 2;
		break;
	      }
	  case acc_cond::acc_op::FinNeg:
	    return true;
	  }
      }
    while (pos > 0);
    return false;
  }

  namespace
  {
    std::set<acc_cond::acc_code> to_dnf_rec(const acc_cond::acc_word* c)
    {
      auto sz = c->size;
      auto start = c - sz - 1;
      auto op = c->op;
      std::set<acc_cond::acc_code> res;
      switch (op)
	{
	case acc_cond::acc_op::Or:
	  {
	    --c;
	    do
	      {
		for (auto& i: to_dnf_rec(c))
		  res.emplace(std::move(i));
		c -= c->size + 1;
	      }
	    while (c > start);
	    return res;
	  }
	case acc_cond::acc_op::And:
	  {
	    std::set<acc_cond::acc_code> old;
	    // Add true to the set.
	    res.emplace(acc_cond::acc_code());
	    --c;
	    do
	      {
		old.clear();
		std::swap(res, old);
		// AND any element in the set with the DNF of c.
		for (auto& i: to_dnf_rec(c))
		  for (auto& j: old)
		    {
		      auto ac = i;
		      ac.append_and(j);
		      res.insert(ac);
		    }
		c -= c->size + 1;
	      }
	    while (c > start);
	    return res;
	  }
	case acc_cond::acc_op::Fin:
	  {
	    acc_cond::acc_code w;
	    w.resize(2);
	    w[1].op = acc_cond::acc_op::Fin;
	    w[1].size = 1;
	    for (auto i: c[-1].mark.sets())
	      {
		w[0].mark = 0U;
		w[0].mark.set(i);
		res.insert(w);
	      }
	    if (!res.empty())
	      return res;
	    /* fall through to handle false */;
	  }
	case acc_cond::acc_op::Inf:
	  {
	    acc_cond::acc_code w;
	    w.insert(w.begin(), c - 1, c + 1);
	    return { w };
	  }
	case acc_cond::acc_op::InfNeg:
	case acc_cond::acc_op::FinNeg:
	  SPOT_UNREACHABLE();
	  return std::set<acc_cond::acc_code>{};
	}
      SPOT_UNREACHABLE();
      return std::set<acc_cond::acc_code>{};
    }
  }

  acc_cond::acc_code acc_cond::acc_code::to_dnf() const
  {
    if (empty())
      return *this;
    acc_cond::acc_code res;
    unsigned count = 0;
    for (auto&i : to_dnf_rec(&back()))
      {
	res.insert(res.end(), i.begin(), i.end());
	++count;
      }
    if (count <= 1)
      return res;
    acc_cond::acc_word w;
    w.op = acc_op::Or;
    w.size = res.size();
    res.push_back(w);
    return res;
  }

  bool acc_cond::acc_code::is_dnf() const
  {
    if (empty())
      return true;
    auto pos = &back();
    auto start = &front();
    if (pos->op == acc_cond::acc_op::Or)
      --pos;
    while (pos > start)
      {
	switch (pos->op)
	  {
	  case acc_cond::acc_op::Or:
	    return false;
	  case acc_cond::acc_op::And:
	    --pos;
	    break;
	  case acc_cond::acc_op::Inf:
	  case acc_cond::acc_op::InfNeg:
	  case acc_cond::acc_op::Fin:
	  case acc_cond::acc_op::FinNeg:
	    pos -= 2;
	    break;
	  }
      }
    return true;
  }

  namespace
  {
    acc_cond::acc_code complement_rec(const acc_cond::acc_word* pos)
    {
      auto start = pos - pos->size;
      switch (pos->op)
	{
	case acc_cond::acc_op::And:
	  {
	    --pos;
	    auto res = acc_cond::acc_code::f();
	    do
	      {
		auto tmp = complement_rec(pos);
		tmp.append_or(std::move(res));
		std::swap(tmp, res);
		pos -= pos->size + 1;
	      }
	    while (pos > start);
	    return res;
	  }
	case acc_cond::acc_op::Or:
	  {
	    --pos;
	    auto res = acc_cond::acc_code::t();
	    do
	      {
		auto tmp = complement_rec(pos);
		tmp.append_and(std::move(res));
		std::swap(tmp, res);
		pos -= pos->size + 1;
	      }
	    while (pos > start);
	    return res;
	  }
	case acc_cond::acc_op::Fin:
	  return acc_cond::acc_code::inf(pos[-1].mark);
	case acc_cond::acc_op::Inf:
	  return acc_cond::acc_code::fin(pos[-1].mark);
	case acc_cond::acc_op::FinNeg:
	  return acc_cond::acc_code::inf_neg(pos[-1].mark);
	case acc_cond::acc_op::InfNeg:
	  return acc_cond::acc_code::fin_neg(pos[-1].mark);
	}
      SPOT_UNREACHABLE();
      return {};
    }

  }


  acc_cond::acc_code acc_cond::acc_code::complement() const
  {
    if (is_true())
      return acc_cond::acc_code::f();
    return complement_rec(&back());
  }

  namespace
  {
    static acc_cond::acc_code
    strip_rec(const acc_cond::acc_word* pos, acc_cond::mark_t rem, bool missing)
    {
      auto start = pos - pos->size;
      switch (pos->op)
	{
	case acc_cond::acc_op::And:
	  {
	    --pos;
	    auto res = acc_cond::acc_code::t();
	    do
	      {
		auto tmp = strip_rec(pos, rem, missing);
		tmp.append_and(std::move(res));
		std::swap(tmp, res);
		pos -= pos->size + 1;
	      }
	    while (pos > start);
	    return res;
	  }
	case acc_cond::acc_op::Or:
	  {
	    --pos;
	    auto res = acc_cond::acc_code::f();
	    do
	      {
		auto tmp = strip_rec(pos, rem, missing);
		tmp.append_or(std::move(res));
		std::swap(tmp, res);
		pos -= pos->size + 1;
	      }
	    while (pos > start);
	    return res;
	  }
	case acc_cond::acc_op::Fin:
	  if (missing && (pos[-1].mark & rem))
	    return acc_cond::acc_code::t();
	  return acc_cond::acc_code::fin(pos[-1].mark.strip(rem));
	case acc_cond::acc_op::Inf:
	  if (missing && (pos[-1].mark & rem))
	    return acc_cond::acc_code::f();
	  return acc_cond::acc_code::inf(pos[-1].mark.strip(rem));
	case acc_cond::acc_op::FinNeg:
	case acc_cond::acc_op::InfNeg:
	  SPOT_UNREACHABLE();
	  return {};
	}
      SPOT_UNREACHABLE();
      return {};
    }
  }

  acc_cond::acc_code
  acc_cond::acc_code::strip(acc_cond::mark_t rem, bool missing) const
  {
    if (is_true() || is_false())
      return *this;
    return strip_rec(&back(), rem, missing);
  }

  acc_cond::mark_t
  acc_cond::acc_code::used_sets() const
  {
    if (is_true() || is_false())
      return 0U;
    acc_cond::mark_t used_in_cond = 0U;
    auto pos = &back();
    auto end = &front();
    while (pos > end)
      {
	switch (pos->op)
	  {
	  case acc_cond::acc_op::And:
	  case acc_cond::acc_op::Or:
	    --pos;
	    break;
	  case acc_cond::acc_op::Fin:
	  case acc_cond::acc_op::Inf:
	  case acc_cond::acc_op::FinNeg:
	  case acc_cond::acc_op::InfNeg:
	    used_in_cond |= pos[-1].mark;
	    pos -= 2;
	    break;
	  }
      }
    return used_in_cond;
  }

  std::ostream& operator<<(std::ostream& os,
			   const spot::acc_cond::acc_code& code)
  {
    if (code.empty())
      os << 't';
    else
      print_code(os, code, code.size() - 1);
    return os;
  }
}
