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
#include <sstream>
#include <set>
#include <cctype>
#include <cstring>
#include "acc.hh"
#include "priv/bddalloc.hh"
#include "misc/minato.hh"

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
    void default_set_printer(std::ostream& os, int v)
    {
      os << v;
    }

    template<bool html>
    static void
    print_code(std::ostream& os,
	       const acc_cond::acc_code& code, unsigned pos,
	       std::function<void(std::ostream&, int)> set_printer)
    {
      const char* op = " | ";
      auto& w = code[pos];
      const char* negated = "";
      bool top = pos == code.size() - 1;
      switch (w.op)
	{
	case acc_cond::acc_op::And:
	  op = html ? " &amp; " : " & ";
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
		print_code<html>(os, code, pos, set_printer);
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
			os << and_ << "Inf(" << negated;
			set_printer(os, level);
			os << ')';
			and_ = html ? "&amp;" : "&";
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
			os << or_ << "Fin(" << negated;
			set_printer(os, level);
			os << ')';
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
	  return (pos[-1].mark & inf) != pos[-1].mark;
	case acc_cond::acc_op::FinNeg:
	case acc_cond::acc_op::InfNeg:
	  SPOT_UNREACHABLE();
	}
      SPOT_UNREACHABLE();
      return false;
    }

    static bool
    inf_eval(acc_cond::mark_t inf, const acc_cond::acc_word* pos)
    {
      switch (pos->op)
	{
	case acc_cond::acc_op::And:
	  {
	    auto sub = pos - pos->size;
	    while (sub < pos)
	      {
		--pos;
		if (!inf_eval(inf, pos))
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
		if (inf_eval(inf, pos))
		  return true;
		pos -= pos->size;
	      }
	    return false;
	  }
	case acc_cond::acc_op::Inf:
	  return (pos[-1].mark & inf) == pos[-1].mark;
	case acc_cond::acc_op::Fin:
	  return true;
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

  bool acc_cond::acc_code::accepting(mark_t inf) const
  {
    if (empty())
      return true;
    return eval(inf, &back());
  }

  bool acc_cond::acc_code::inf_satisfiable(mark_t inf) const
  {
    if (empty())
      return true;
    return inf_eval(inf, &back());
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
    bdd to_bdd_rec(const acc_cond::acc_word* c, const bdd* map)
    {
      auto sz = c->size;
      auto start = c - sz - 1;
      auto op = c->op;
      switch (op)
	{
	case acc_cond::acc_op::Or:
	  {
	    --c;
	    bdd res = bddfalse;
	    do
	      {
		res |= to_bdd_rec(c, map);
		c -= c->size + 1;
	      }
	    while (c > start);
	    return res;
	  }
	case acc_cond::acc_op::And:
	  {
	    --c;
	    bdd res = bddtrue;
	    do
	      {
		res &= to_bdd_rec(c, map);
		c -= c->size + 1;
	      }
	    while (c > start);
	    return res;
	  }
	case acc_cond::acc_op::Fin:
	  {
	    bdd res = bddfalse;
	    for (auto i: c[-1].mark.sets())
	      res |= !map[i];
	    return res;
	  }
	case acc_cond::acc_op::Inf:
	  {
	    bdd res = bddtrue;
	    for (auto i: c[-1].mark.sets())
	      res &= map[i];
	    return res;
	  }
	case acc_cond::acc_op::InfNeg:
	case acc_cond::acc_op::FinNeg:
	  SPOT_UNREACHABLE();
	  return bddfalse;
	}
      SPOT_UNREACHABLE();
      return bddfalse;
    }
  }

  acc_cond::acc_code acc_cond::acc_code::to_dnf() const
  {
    if (empty() || size() == 2)
      return *this;

    auto used = acc_cond::acc_code::used_sets();
    unsigned c = used.count();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> r;
    std::vector<unsigned> sets(c);
    for (unsigned i = 0; r.size() < c; ++i)
      {
	if (used.has(i))
	  {
	    sets[base] = i;
	    r.push_back(bdd_ithvar(base++));
	  }
	else
	  {
	    r.push_back(bddfalse);
	  }
      }

    bdd res = to_bdd_rec(&back(), &r[0]);

    if (res == bddtrue)
      return t();
    if (res == bddfalse)
      return f();

    minato_isop isop(res);
    bdd cube;
    acc_code rescode = f();
    while ((cube = isop.next()) != bddfalse)
      {
	mark_t i = 0U;
	acc_code c;
	while (cube != bddtrue)
	  {
	    // The acceptance set associated to this BDD variable
	    mark_t s = 0U;
	    s.set(sets[bdd_var(cube)]);

	    bdd h = bdd_high(cube);
	    if (h == bddfalse)	// Negative variable? -> Fin
	      {
		cube = bdd_low(cube);
		// The strange order here make sure we can smaller set
		// numbers at the end of the acceptance code, i.e., at
		// the front of the output.
		auto a = fin(s);
		a.append_and(std::move(c));
		std::swap(a, c);
	      }
	    else		// Positive variable? -> Inf
	      {
		i |= s;
		cube = h;
	      }
	  }
	c.append_and(inf(i));
	// See comment above for the order.
	c.append_or(std::move(rescode));
	std::swap(c, rescode);
      }
    return rescode;
  }

  acc_cond::acc_code acc_cond::acc_code::to_cnf() const
  {
    if (empty() || size() == 2)
      return *this;

    auto used = acc_cond::acc_code::used_sets();
    unsigned c = used.count();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> r;
    std::vector<unsigned> sets(c);
    for (unsigned i = 0; r.size() < c; ++i)
      {
	if (used.has(i))
	  {
	    sets[base] = i;
	    r.push_back(bdd_ithvar(base++));
	  }
	else
	  {
	    r.push_back(bddfalse);
	  }
      }

    bdd res = to_bdd_rec(&back(), &r[0]);

    if (res == bddtrue)
      return t();
    if (res == bddfalse)
      return f();

    minato_isop isop(!res);
    bdd cube;
    acc_code rescode;
    while ((cube = isop.next()) != bddfalse)
      {
	mark_t m = 0U;
	acc_code c = f();
	while (cube != bddtrue)
	  {
	    // The acceptance set associated to this BDD variable
	    mark_t s = 0U;
	    s.set(sets[bdd_var(cube)]);

	    bdd h = bdd_high(cube);
	    if (h == bddfalse)	// Negative variable? -> Inf
	      {
		cube = bdd_low(cube);
		// The strange order here make sure we can smaller set
		// numbers at the end of the acceptance code, i.e., at
		// the front of the output.
		auto a = inf(s);
		a.append_or(std::move(c));
		std::swap(a, c);
	      }
	    else		// Positive variable? -> Fin
	      {
		m |= s;
		cube = h;
	      }
	  }
	c.append_or(fin(m));
	// See comment above for the order.
	c.append_and(std::move(rescode));
	std::swap(c, rescode);
      }
    return rescode;
  }

  std::pair<bool, acc_cond::mark_t>
  acc_cond::acc_code::unsat_mark() const
  {
    if (empty())
      return {false, 0U};

    auto used = acc_cond::acc_code::used_sets();
    unsigned c = used.count();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> r;
    std::vector<unsigned> sets(c);
    for (unsigned i = 0; r.size() < c; ++i)
      {
	if (used.has(i))
	  {
	    sets[base] = i;
	    r.push_back(bdd_ithvar(base++));
	  }
	else
	  {
	    r.push_back(bddfalse);
	  }
      }

    bdd res = to_bdd_rec(&back(), &r[0]);

    if (res == bddtrue)
      return {false, 0U};
    if (res == bddfalse)
      return {true, 0U};

    bdd cube = bdd_satone(!res);
    mark_t i = 0U;
    while (cube != bddtrue)
      {
	// The acceptance set associated to this BDD variable
	int s = sets[bdd_var(cube)];

	bdd h = bdd_high(cube);
	if (h == bddfalse)	// Negative variable? -> skip
	  {
	    cube = bdd_low(cube);
	  }
	else		// Positive variable? -> Inf
	  {
	    i.set(s);
	    cube = h;
	  }
      }
    return {true, i};
  }

  std::vector<std::vector<int>>
  acc_cond::acc_code::missing(mark_t inf, bool accepting) const
  {
    if (empty())
      {
	if (accepting)
	  return {};
	else
	  return {
	    {}
	  };
      }
    auto used = acc_cond::acc_code::used_sets();
    unsigned c = used.count();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> r;
    std::vector<unsigned> sets(c);
    bdd known = bddtrue;
    for (unsigned i = 0; r.size() < c; ++i)
      {
	if (used.has(i))
	  {
	    sets[base] = i;
	    bdd v = bdd_ithvar(base++);
	    r.push_back(v);
	    if (inf.has(i))
	      known &= v;
	  }
	else
	  {
	    r.push_back(bddfalse);
	  }
      }

    bdd res = to_bdd_rec(&back(), &r[0]);

    res = bdd_restrict(res, known);

    if (accepting)
      res = !res;

    if (res == bddfalse)
      return {};

    minato_isop isop(res);
    bdd cube;
    std::vector<std::vector<int>> result;
    while ((cube = isop.next()) != bddfalse)
      {
	std::vector<int> partial;
	while (cube != bddtrue)
	  {
	    // The acceptance set associated to this BDD variable
	    int s = sets[bdd_var(cube)];

	    bdd h = bdd_high(cube);
	    if (h == bddfalse)	// Negative variable
	      {
		partial.push_back(s);
		cube = bdd_low(cube);
	      }
	    else		// Positive variable
	      {
		partial.push_back(-s - 1);
		cube = h;
	      }
	  }
	result.emplace_back(std::move(partial));
      }
    return result;
  }

  bool acc_cond::acc_code::is_dnf() const
  {
    if (empty() || size() == 2)
      return true;
    auto pos = &back();
    auto start = &front();
    auto and_scope = pos + 1;
    if (pos->op == acc_cond::acc_op::Or)
      --pos;
    while (pos > start)
      {
	switch (pos->op)
	  {
	  case acc_cond::acc_op::Or:
	    return false;
	  case acc_cond::acc_op::And:
	    and_scope = std::min(and_scope, pos - pos->size);
	    --pos;
	    break;
	  case acc_cond::acc_op::Fin:
	  case acc_cond::acc_op::FinNeg:
	    if (pos[-1].mark.count() > 1 && pos > and_scope)
	      return false;
	    /* fall through */
	  case acc_cond::acc_op::Inf:
	  case acc_cond::acc_op::InfNeg:
	    pos -= 2;
	    break;
	  }
      }
    return true;
  }

  bool acc_cond::acc_code::is_cnf() const
  {
    if (empty() || size() == 2)
      return true;
    auto pos = &back();
    auto start = &front();
    auto or_scope = pos + 1;
    if (pos->op == acc_cond::acc_op::And)
      --pos;
    while (pos > start)
      {
	switch (pos->op)
	  {
	  case acc_cond::acc_op::And:
	    return false;
	  case acc_cond::acc_op::Or:
	    or_scope = std::min(or_scope, pos - pos->size);
	    --pos;
	    break;
	  case acc_cond::acc_op::Inf:
	  case acc_cond::acc_op::InfNeg:
	    if (pos[-1].mark.count() > 1 && pos > or_scope)
	      return false;
	    /* fall through */
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

  std::pair<acc_cond::mark_t, acc_cond::mark_t>
  acc_cond::acc_code::used_inf_fin_sets() const
  {
    if (is_true() || is_false())
      return {0U, 0U};

    acc_cond::mark_t used_fin = 0U;
    acc_cond::mark_t used_inf = 0U;
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
	  case acc_cond::acc_op::FinNeg:
	    used_fin |= pos[-1].mark;
	    pos -= 2;
	    break;
	  case acc_cond::acc_op::Inf:
	  case acc_cond::acc_op::InfNeg:
	    used_inf |= pos[-1].mark;
	    pos -= 2;
	    break;
	  }
      }
    return {used_inf, used_fin};
  }

  std::ostream&
  acc_cond::acc_code::to_html(std::ostream& os,
			      std::function<void(std::ostream&, int)>
			      set_printer) const
  {
    if (empty())
      os << 't';
    else
      print_code<true>(os, *this, size() - 1,
		       set_printer ? set_printer : default_set_printer);
    return os;
  }

  std::ostream&
  acc_cond::acc_code::to_text(std::ostream& os,
			      std::function<void(std::ostream&, int)>
			      set_printer) const
  {
    if (empty())
      os << 't';
    else
      print_code<false>(os, *this, size() - 1,
			set_printer ? set_printer : default_set_printer);
    return os;
  }


  std::ostream& operator<<(std::ostream& os,
			   const spot::acc_cond::acc_code& code)
  {
    return code.to_text(os);
  }



  namespace
  {

    /// acc ::= term | term "|" acc
    /// term := "t" | "f" | "Inf" "(" num ")"
    ///       | "Fin" "(" num ") " | "(" acc ")
    ///       | term "&" term

    static void skip_space(const char*& input)
    {
      while (std::isspace(*input))
	++input;
    }

    // Eat c and remove the following spaces.
    // Complain if there is no c.
    void expect(const char*& input, char c)
    {
      if (*input != c)
	{
	  std::ostringstream s;
	  s << "syntax error at '" << input << "', was expecting " << c << '.';
	  throw parse_error(s.str());
	}
      ++input;
      skip_space(input);
    }

    static acc_cond::acc_code parse_term(const char*& input);

    static acc_cond::acc_code parse_acc(const char*& input)
    {
      auto t = parse_term(input);
      skip_space(input);
      while (*input == '|')
	{
	  ++input;
	  skip_space(input);
	  t.append_or(parse_term(input));
	}
      return t;
    }

    static unsigned parse_num(const char*& input)
    {
      skip_space(input);
      expect(input, '(');

      errno = 0;
      char* end;
      unsigned long n = strtoul(input, &end, 10);
      unsigned num = n;
      if (errno || num != n)
	{
	  std::ostringstream s;
	  s << "syntax error at '" << input << "': value too large.";
	  throw parse_error(s.str());
	}
      input = end;

      skip_space(input);
      expect(input, ')');
      return num;
    }

    static acc_cond::acc_code parse_term(const char*& input)
    {
      acc_cond::acc_code res;
      if (*input == 't')
	{
	  ++input;
	  res = acc_cond::acc_code::t();
	}
      else if (*input == 'f')
	{
	  ++input;
	  res = acc_cond::acc_code::f();
	}
      else if (*input == '(')
	{
	  ++input;
	  skip_space(input);
	  res = parse_acc(input);
	  skip_space(input);
	  expect(input, ')');
	}
      else if (!strncmp(input, "Inf", 3))
	{
	  input += 3;
	  res = acc_cond::acc_code::inf({parse_num(input)});
	}
      else if (!strncmp(input, "Fin", 3))
	{
	  input += 3;
	  res = acc_cond::acc_code::fin({parse_num(input)});
	}
      else
	{
	  std::ostringstream s;
	  s << "syntax error at '" << input << "', unexpected character.";
	  throw parse_error(s.str());
	}

      skip_space(input);
      while (*input == '&')
	{
	  ++input;
	  skip_space(input);
	  res.append_and(parse_term(input));
	}
      return res;
    }

  }

  acc_cond::acc_code parse_acc_code(const char* input)
  {
    skip_space(input);
    acc_cond::acc_code c = parse_acc(input);
    if (*input)
      {
	std::ostringstream s;
	s << "syntax error at '" << input << "', unexpected character.";
	throw parse_error(s.str());
      }
    return c;
  }
}
