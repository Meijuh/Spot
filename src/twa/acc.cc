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
    // Is Rabin or Streett, depending on highop and lowop.
    static bool
    is_rs(const acc_cond::acc_code& code,
	  acc_cond::acc_op highop,
	  acc_cond::acc_op lowop,
	  acc_cond::mark_t all_sets)
    {
      unsigned s = code.back().size;
      auto mainop = code.back().op;
      if (mainop == highop)
	{
	  // The size must be a multiple of 5.
	  if ((s != code.size() - 1) || (s % 5))
	    return false;
	}
      else			// Single pair?
	{
	  if (s != 4 || mainop != lowop)
	    return false;
	  // Pretend we where in a unary highop.
	  s = 5;
	}
      acc_cond::mark_t seen_fin = 0U;
      acc_cond::mark_t seen_inf = 0U;
      while (s)
	{
	  if (code[--s].op != lowop)
	    return false;
	  auto o1 = code[--s].op;
	  auto m1 = code[--s].mark;
	  auto o2 = code[--s].op;
	  auto m2 = code[--s].mark;

	  // We assume
	  //   Fin(n) lowop Inf(n+1)
	  //   o1 (m1)       o2 (m2)
	  // swap if it is the converse
	  if (o2 == acc_cond::acc_op::Fin)
	    {
	      std::swap(o1, o2);
	      std::swap(m1, m2);
	    }
	  if (o1 != acc_cond::acc_op::Fin
	      || o2 != acc_cond::acc_op::Inf
	      || m1.count() != 1
	      || m2.id != (m1.id << 1))
	    return false;
	  seen_fin |= m1;
	  seen_inf |= m2;
	}

      return (!(seen_fin & seen_inf)
	      && (seen_fin | seen_inf) == all_sets);
    }
  }

  int acc_cond::is_rabin() const
  {
    if (code_.is_false())
      return num_ == 0 ? 0 : -1;
    if ((num_ & 1) || code_.is_true())
      return -1;

    if (is_rs(code_, acc_op::Or, acc_op::And, all_sets()))
      return num_ / 2;
    else
      return -1;
  }

  int acc_cond::is_streett() const
  {
    if (code_.is_true())
      return num_ == 0 ? 0 : -1;
    if ((num_ & 1) || code_.is_false())
      return -1;

    if (is_rs(code_, acc_op::And, acc_op::Or, all_sets()))
      return num_ / 2;
    else
      return -1;
  }

  // PAIRS contains the number of Inf in each pair.
  bool acc_cond::is_generalized_rabin(std::vector<unsigned>& pairs) const
  {
    pairs.clear();
    if (is_generalized_co_buchi())
      {
	pairs.resize(num_);
	return true;
      }
    if (code_.is_true()
	|| code_.back().op != acc_op::Or)
      return false;

    auto s = code_.back().size;
    acc_cond::mark_t seen_fin = 0U;
    acc_cond::mark_t seen_inf = 0U;
    // Each pairs is the position of a Fin followed
    // by the number of Inf.
    std::map<unsigned, unsigned> p;
    while (s)
      {
	--s;
	if (code_[s].op == acc_op::And)
	  {
	    auto o1 = code_[--s].op;
	    auto m1 = code_[--s].mark;
	    auto o2 = code_[--s].op;
	    auto m2 = code_[--s].mark;

	    // We assume
	    //   Fin(n) & Inf({n+1,n+2,...,n+i})
	    //   o1 (m1)       o2 (m2)
	    // swap if it is the converse
	    if (o2 == acc_cond::acc_op::Fin)
	      {
		std::swap(o1, o2);
		std::swap(m1, m2);
	      }

	    if (o1 != acc_cond::acc_op::Fin
		|| o2 != acc_cond::acc_op::Inf
		|| m1.count() != 1)
	      return false;

	    unsigned i = m2.count();
	    // If we have seen this pair already, it must have the
	    // same size.
	    if (p.emplace(m1.max_set(), i).first->second != i)
	      return false;
	    assert(i > 0);
	    unsigned j = m1.max_set(); // == n+1
	    do
	      if (!m2.has(j++))
		return false;
	    while (--i);

	    seen_fin |= m1;
	    seen_inf |= m2;
	  }
	else if (code_[s].op == acc_op::Fin)
	  {
	    auto m1 = code_[--s].mark;
	    if (m1.count() != 1)
	      return false;
	    // If we have seen this pair already, it must have the
	    // same size.
	    if (p.emplace(m1.max_set(), 0U).first->second != 0U)
	      return false;
	    seen_fin |= m1;
	  }
	else
	  {
	    return false;
	  }
      }
    for (auto i: p)
      pairs.push_back(i.second);
    return (!(seen_fin & seen_inf)
	    && (seen_fin | seen_inf) == all_sets());
  }

  acc_cond::acc_code
  acc_cond::acc_code::parity(bool max, bool odd, unsigned sets)
  {
    if (sets == 0)
      return f();
    // When you look at something like
    //    acc-name: parity min even 5
    //    Acceptance: 5 Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))
    // remember that we build it from right to left.
    int start = max ? 0 : sets - 1;
    int inc = max ? 1 : -1;
    int end = max ? sets : -1;
    // Do not start with a Fin term, the right-most term is always Inf.
    if ((start & 1) != odd)
      start += inc;
    acc_cond::acc_code res = f();
    for (int i = start; i != end; i += inc)
      {
	if ((i & 1) == odd)
	  res.append_or(inf({(unsigned)i}));
	else
	  res.append_and(fin({(unsigned)i}));
      }
    return res;
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

    static bool
    equiv_codes(const acc_cond::acc_code& lhs,
		const acc_cond::acc_code& rhs)
    {
      auto used = lhs.used_sets() | rhs.used_sets();

      unsigned c = used.count();
      unsigned umax = used.max_set();

      bdd_allocator ba;
      int base = ba.allocate_variables(c);
      assert(base == 0);
      std::vector<bdd> r;
      for (unsigned i = 0; r.size() < umax; ++i)
	if (used.has(i))
	  r.push_back(bdd_ithvar(base++));
	else
	  r.push_back(bddfalse);
      return to_bdd_rec(&lhs.back(), &r[0]) == to_bdd_rec(&rhs.back(), &r[0]);
    }
  }

  bool acc_cond::is_parity(bool& max, bool& odd, bool equiv) const
  {
    unsigned sets = num_;
    if (sets == 0)
      {
	max = false;
	odd = false;
	return is_false();
      }
    if (is_true())
      return false;
    acc_cond::mark_t u_inf;
    acc_cond::mark_t u_fin;
    std::tie(u_inf, u_fin) = code_.used_inf_fin_sets();

    odd = !u_inf.has(0);
    for (auto s: u_inf.sets())
      if ((s & 1) != odd)
	return false;

    auto max_code = acc_code::parity(true, odd, sets);
    if (max_code == code_)
      {
	max = true;
	return true;
      }
    auto min_code = acc_code::parity(false, odd, sets);
    if (min_code == code_)
      {
	max = false;
	return true;
      }

    if (!equiv)
      return false;

    if (equiv_codes(code_, max_code))
      {
	max = true;
	return true;
      }
    if (equiv_codes(code_, min_code))
      {
	max = false;
	return true;
      }
    return false;
  }

  acc_cond::acc_code acc_cond::acc_code::to_dnf() const
  {
    if (empty() || size() == 2)
      return *this;

    auto used = acc_cond::acc_code::used_sets();
    unsigned c = used.count();
    unsigned max = used.max_set();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> r;
    std::vector<unsigned> sets(c);
    for (unsigned i = 0; r.size() < max; ++i)
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
    unsigned max = used.max_set();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> r;
    std::vector<unsigned> sets(c);
    for (unsigned i = 0; r.size() < max; ++i)
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
    unsigned max = used.max_set();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> r;
    std::vector<unsigned> sets(c);
    for (unsigned i = 0; r.size() < max; ++i)
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
    unsigned max = used.max_set();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> r;
    std::vector<unsigned> sets(c);
    bdd known = bddtrue;
    for (unsigned i = 0; r.size() < max; ++i)
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
      auto res = parse_term(input);
      skip_space(input);
      while (*input == '|')
	{
	  ++input;
	  skip_space(input);
	  // Prepend instead of append, to preserve the input order.
	  auto tmp = parse_term(input);
	  std::swap(tmp, res);
	  res.append_or(std::move(tmp));
	}
      return res;
    }

    static unsigned parse_num(const char*& input)
    {

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

      return num;
    }

    static unsigned parse_par_num(const char*& input)
    {
      skip_space(input);
      expect(input, '(');
      unsigned num = parse_num(input);
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
	  res = acc_cond::acc_code::inf({parse_par_num(input)});
	}
      else if (!strncmp(input, "Fin", 3))
	{
	  input += 3;
	  res = acc_cond::acc_code::fin({parse_par_num(input)});
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
	  // Prepend instead of append, to preserve the input order.
	  auto tmp = parse_term(input);
	  std::swap(tmp, res);
	  res.append_and(std::move(tmp));
	}
      return res;
    }

    static bool max_or_min(const char*& input)
    {
      skip_space(input);
      if (!strncmp(input, "max", 3))
	{
	  input += 3;
	  return true;
	}
      if (!strncmp(input, "min", 3))
	{
	  input += 3;
	  return false;
	}
      std::ostringstream s;
      s << "syntax error at '" << input
	<< "': expecting 'min' or 'max'";
      throw parse_error(s.str());
    }

    static bool odd_or_even(const char*& input)
    {
      skip_space(input);
      if (!strncmp(input, "odd", 3))
	{
	  input += 3;
	  return true;
	}
      if (!strncmp(input, "even", 4))
	{
	  input += 4;
	  return false;
	}
      std::ostringstream s;
      s << "syntax error at '" << input
	<< "': expecting 'odd' or 'even'";
      throw parse_error(s.str());
    }

  }

  acc_cond::acc_code parse_acc_code(const char* input)
  {
    skip_space(input);
    acc_cond::acc_code c;
    if (!strncmp(input, "all", 3))
      {
	input += 3;
	c = acc_cond::acc_code::t();
      }
    else if (!strncmp(input, "none", 4))
      {
	input += 4;
	c = acc_cond::acc_code::f();
      }
    else if (!strncmp(input, "Buchi", 5))
      {
	input += 5;
	c = acc_cond::acc_code::buchi();
      }
    else if (!strncmp(input, "co-Buchi", 8))
      {
	input += 8;
	c = acc_cond::acc_code::cobuchi();
      }
    else if (!strncmp(input, "generalized-Buchi", 17))
      {
	input += 17;
	c = acc_cond::acc_code::generalized_buchi(parse_num(input));
      }
    else if (!strncmp(input, "generalized-co-Buchi", 20))
      {
	input += 20;
	c = acc_cond::acc_code::generalized_buchi(parse_num(input));
      }
    else if (!strncmp(input, "Rabin", 5))
      {
	input += 5;
	c = acc_cond::acc_code::rabin(parse_num(input));
      }
    else if (!strncmp(input, "Streett", 7))
      {
	input += 7;
	c = acc_cond::acc_code::streett(parse_num(input));
      }
    else if (!strncmp(input, "generalized-Rabin", 17))
      {
	input += 17;
	unsigned num = parse_num(input);
	std::vector<unsigned> v;
	v.reserve(num);
	while (num > 0)
	  {
	    v.push_back(parse_num(input));
	    --num;
	  }
	c = acc_cond::acc_code::generalized_rabin(v.begin(), v.end());
      }
    else if (!strncmp(input, "parity", 6))
      {
	input += 6;
	bool max = max_or_min(input);
	bool odd = odd_or_even(input);
	unsigned num = parse_num(input);
	c = acc_cond::acc_code::parity(max, odd, num);
      }
    else
      {
	c = parse_acc(input);
      }
    skip_space(input);
    if (*input)
      {
	std::ostringstream s;
	s << "syntax error at '" << input << "', unexpected character.";
	throw parse_error(s.str());
      }
    return c;
  }
}
