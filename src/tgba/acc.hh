// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et Développement de
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

#ifndef SPOT_TGBA_ACC_HH
# define SPOT_TGBA_ACC_HH

# include <functional>
# include <unordered_map>
# include <sstream>
# include <vector>
# include "ltlenv/defaultenv.hh"
# include <iostream>

namespace spot
{
  class SPOT_API acc_cond
  {
  public:
    struct mark_t
    {
      typedef unsigned value_t;
      value_t id;

      mark_t() = default;

      mark_t(value_t id)
	: id(id)
      {
      }

      bool operator==(unsigned o) const
      {
	assert(o == 0U);
	return id == o;
      }

      bool operator!=(unsigned o) const
      {
	assert(o == 0U);
	return id != o;
      }

      bool operator==(mark_t o) const
      {
	return id == o.id;
      }

      bool operator!=(mark_t o) const
      {
	return id != o.id;
      }

      bool operator<(mark_t o) const
      {
	return id < o.id;
      }

      bool operator<=(mark_t o) const
      {
	return id <= o.id;
      }

      bool operator>(mark_t o) const
      {
	return id > o.id;
      }

      bool operator>=(mark_t o) const
      {
	return id >= o.id;
      }

      operator bool() const
      {
	return id != 0;
      }

      bool has(unsigned u) const
      {
	return id & (1U << u);
      }

      void set(unsigned u)
      {
	id |= (1U << u);
      }

      mark_t& operator&=(mark_t r)
      {
	id &= r.id;
	return *this;
      }

      mark_t& operator|=(mark_t r)
      {
	id |= r.id;
	return *this;
      }

      mark_t& operator-=(mark_t r)
      {
	id &= ~r.id;
	return *this;
      }

      mark_t& operator^=(mark_t r)
      {
	id ^= r.id;
	return *this;
      }

      mark_t operator&(mark_t r) const
      {
	return id & r.id;
      }

      mark_t operator|(mark_t r) const
      {
	return id | r.id;
      }

      mark_t operator-(mark_t r) const
      {
	return id & ~r.id;
      }

      mark_t operator^(mark_t r) const
      {
	return id ^ r.id;
      }

      // Number of bits sets.
      unsigned count() const
      {
#ifdef __GNUC__
	return __builtin_popcount(id);
#else
	unsigned c = 0U;
	auto v = id;
	while (v)
	  {
	    ++c;
	    v &= v - 1;
	  }
	return c;
#endif
      }

      // Remove n bits that where set
      mark_t& remove_some(unsigned n)
      {
	while (n--)
	  id &= id - 1;
	return *this;
      }

      template<class iterator>
      void fill(iterator here) const
      {
	auto a = id;
	unsigned level = 0;
	while (a)
	  {
	    if (a & 1)
	      *here++ = level;
	    ++level;
	    a >>= 1;
	  }
      }

      // FIXME: Return some iterable object without building a vector.
      std::vector<unsigned> sets() const
      {
	std::vector<unsigned> res;
	fill(std::back_inserter(res));
	return res;
      }

      SPOT_API
      friend std::ostream& operator<<(std::ostream& os, mark_t m);
    };

    // This encodes either an operator or set of acceptance sets.
    enum class acc_op : unsigned char
    { Inf, Fin, InfNeg, FinNeg, And, Or };
    union acc_word
    {
      mark_t mark;
      struct {
	acc_op op;	    // Operator
	unsigned char size; // Size of the subtree (number of acc_word),
			    // not counting this node.
      };
    };

    struct SPOT_API acc_code: public std::vector<acc_word>
    {
      bool operator==(const acc_code& other) const
      {
	unsigned pos = size();
	if (other.size() != pos)
	  return false;
	while (pos > 0)
	  {
	    auto op = (*this)[pos - 1].op;
	    auto sz = (*this)[pos - 1].size;
	    if (other[pos - 1].op != op ||
		other[pos - 1].size != sz)
	      return false;
	    switch (op)
	      {
	      case acc_cond::acc_op::And:
	      case acc_cond::acc_op::Or:
		--pos;
		break;
	      case acc_cond::acc_op::Inf:
	      case acc_cond::acc_op::InfNeg:
	      case acc_cond::acc_op::Fin:
	      case acc_cond::acc_op::FinNeg:
		pos -= 2;
		if (other[pos].mark != (*this)[pos].mark)
		  return false;
		break;
	      }
	  }
	return true;
      };

      bool operator<(const acc_code& other) const
      {
	unsigned pos = size();
	auto osize = other.size();
	if (pos < osize)
	  return true;
	if (pos > osize)
	  return false;
	while (pos > 0)
	  {
	    auto op = (*this)[pos - 1].op;
	    auto oop = other[pos - 1].op;
	    if (op < oop)
	      return true;
	    if (op > oop)
	      return false;
	    auto sz = (*this)[pos - 1].size;
	    auto osz = other[pos - 1].size;
	    if (sz < osz)
	      return true;
	    if (sz > osz)
	      return false;
	    switch (op)
	      {
	      case acc_cond::acc_op::And:
	      case acc_cond::acc_op::Or:
		--pos;
		break;
	      case acc_cond::acc_op::Inf:
	      case acc_cond::acc_op::InfNeg:
	      case acc_cond::acc_op::Fin:
	      case acc_cond::acc_op::FinNeg:
		pos -= 2;
		auto m = (*this)[pos].mark;
		auto om = other[pos].mark;
		if (m < om)
		  return true;
		if (m > om)
		  return false;
		break;
	      }
	  }
	return false;
      }

      bool operator>(const acc_code& other) const
      {
	return other < *this;
      }

      bool operator<=(const acc_code& other) const
      {
	return !(other < *this);
      }

      bool operator>=(const acc_code& other) const
      {
	return !(*this < other);
      }

      bool operator!=(const acc_code& other) const
      {
	return !(*this == other);
      }

      bool is_true() const
      {
	unsigned s = size();
	return s == 0
	  || ((*this)[s - 1].op == acc_op::Inf && (*this)[s - 2].mark == 0U);
      }

      bool is_false() const
      {
	unsigned s = size();
	return s > 1
	  && (*this)[s - 1].op == acc_op::Fin && (*this)[s - 2].mark == 0U;
      }

      void append_and(acc_code&& r)
      {
	if (is_true() || r.is_false())
	  {
	    *this = std::move(r);
	    return;
	  }
	if (is_false() || r.is_true())
	  return;
	unsigned s = size() - 1;
	unsigned rs = r.size() - 1;
	// We want to group all Inf(x) operators:
	//   Inf(a) & Inf(b) = Inf(a & b)
	if (((*this)[s].op == acc_op::Inf && r[rs].op == acc_op::Inf)
	    || ((*this)[s].op == acc_op::InfNeg && r[rs].op == acc_op::InfNeg))
	  {
	    (*this)[s - 1].mark |= r[rs - 1].mark;
	    return;
	  }

	// In the more complex scenarios, left and right may both
	// be conjunctions, and Inf(x) might be a member of each
	// side.  Find it if it exists.
	// left_inf points to the left Inf mark if any.
	// right_inf points to the right Inf mark if any.
	acc_word* left_inf = nullptr;
	if ((*this)[s].op == acc_op::And)
	  {
	    auto start = &(*this)[s] - (*this)[s].size;
	    auto pos = &(*this)[s] - 1;
	    pop_back();
	    while (pos > start)
	      {
		if (pos->op == acc_op::Inf)
		  {
		    left_inf = pos - 1;
		    break;
		  }
		pos -= pos->size + 1;
	      }
	  }
	else if ((*this)[s].op == acc_op::Inf)
	  {
	    left_inf = &(*this)[s - 1];
	  }

	acc_word* right_inf = nullptr;
	auto right_end = &r.back();
	if (right_end->op == acc_op::And)
	  {
	    auto start = &r[0];
	    auto pos = --right_end;
	    while (pos > start)
	    {
	      if (pos->op == acc_op::Inf)
		{
		  right_inf = pos - 1;
		  break;
		}
	      pos -= pos->size + 1;
	    }
	  }
	else if (right_end->op == acc_op::Inf)
	  {
	    right_inf = right_end - 1;
	  }

	if (left_inf && right_inf)
	  {
	    left_inf->mark |= right_inf->mark;
	    insert(this->end(), &r[0], right_inf);
	    insert(this->end(), right_inf + 2, right_end + 1);
	  }
	else if (right_inf)
	  {
	    // Always insert Inf() at the very first entry.
	    insert(this->begin(), right_inf, right_inf + 2);
	    insert(this->end(), &r[0], right_inf);
	    insert(this->end(), right_inf + 2, right_end + 1);
	  }
	else
	  {
	    insert(this->end(), &r[0], right_end + 1);
	  }

	acc_word w;
	w.op = acc_op::And;
	w.size = size();
	push_back(w);
      }

      void append_and(const acc_code& r)
      {
	if (is_true() || r.is_false())
	  {
	    *this = r;
	    return;
	  }
	if (is_false() || r.is_true())
	  return;
	unsigned s = size() - 1;
	unsigned rs = r.size() - 1;
	// Inf(a) & Inf(b) = Inf(a & b)
	if (((*this)[s].op == acc_op::Inf && r[rs].op == acc_op::Inf)
	    || ((*this)[s].op == acc_op::InfNeg && r[rs].op == acc_op::InfNeg))
	  {
	    (*this)[s - 1].mark |= r[rs - 1].mark;
	    return;
	  }

	// In the more complex scenarios, left and right may both
	// be conjunctions, and Inf(x) might be a member of each
	// side.  Find it if it exists.
	// left_inf points to the left Inf mark if any.
	// right_inf points to the right Inf mark if any.
	acc_word* left_inf = nullptr;
	if ((*this)[s].op == acc_op::And)
	  {
	    auto start = &(*this)[s] - (*this)[s].size;
	    auto pos = &(*this)[s] - 1;
	    pop_back();
	    while (pos > start)
	      {
		if (pos->op == acc_op::Inf)
		  {
		    left_inf = pos - 1;
		    break;
		  }
		pos -= pos->size + 1;
	      }
	  }
	else if ((*this)[s].op == acc_op::Inf)
	  {
	    left_inf = &(*this)[s - 1];
	  }

	const acc_word* right_inf = nullptr;
	auto right_end = &r.back();
	if (right_end->op == acc_op::And)
	  {
	    auto start = &r[0];
	    auto pos = --right_end;
	    while (pos > start)
	    {
	      if (pos->op == acc_op::Inf)
		{
		  right_inf = pos - 1;
		  break;
		}
	      pos -= pos->size + 1;
	    }
	  }
	else if (right_end->op == acc_op::Inf)
	  {
	    right_inf = right_end - 1;
	  }

	if (left_inf && right_inf)
	  {
	    left_inf->mark |= right_inf->mark;
	    insert(this->end(), &r[0], right_inf);
	    insert(this->end(), right_inf + 2, right_end + 1);
	  }
	else if (right_inf)
	  {
	    // Always insert Inf() at the very first entry.
	    insert(this->begin(), right_inf, right_inf + 2);
	    insert(this->end(), &r[0], right_inf);
	    insert(this->end(), right_inf + 2, right_end + 1);
	  }
	else
	  {
	    insert(this->end(), &r[0], right_end + 1);
	  }

	acc_word w;
	w.op = acc_op::And;
	w.size = size();
	push_back(w);
      }

      void append_or(acc_code&& r)
      {
	if (is_true() || r.is_false())
	  return;
	if (is_false() || r.is_true())
	  {
	    *this = std::move(r);
	    return;
	  }
	unsigned s = size() - 1;
	unsigned rs = r.size() - 1;
	// Fin(a) | Fin(b) = Fin(a | b)
	if (((*this)[s].op == acc_op::Fin && r[rs].op == acc_op::Fin)
	    || ((*this)[s].op == acc_op::FinNeg && r[rs].op == acc_op::FinNeg))
	  {
	    (*this)[s - 1].mark |= r[rs - 1].mark;
	    return;
	  }
	if ((*this)[s].op == acc_op::Or)
	  pop_back();
	if (r.back().op == acc_op::Or)
	  r.pop_back();
	insert(this->end(), r.begin(), r.end());
	acc_word w;
	w.op = acc_op::Or;
	w.size = size();
	push_back(w);
      }

      void shift_left(unsigned sets)
      {
	if (empty())
	  return;
	unsigned pos = size();
	do
	  {
	    switch ((*this)[pos - 1].op)
	      {
	      case acc_cond::acc_op::And:
	      case acc_cond::acc_op::Or:
		--pos;
		break;
	      case acc_cond::acc_op::Inf:
	      case acc_cond::acc_op::InfNeg:
	      case acc_cond::acc_op::Fin:
	      case acc_cond::acc_op::FinNeg:
		pos -= 2;
		(*this)[pos].mark.id <<= sets;
		break;
	      }
	  }
	while (pos > 0);
      }

      acc_code to_dnf() const;

      SPOT_API
      friend std::ostream& operator<<(std::ostream& os, const acc_code& code);
    };

    acc_cond(unsigned n_sets = 0)
      : num_(0U), all_(0U)
    {
      add_sets(n_sets);
    }

    acc_cond(const acc_cond& o)
      : num_(o.num_), all_(o.all_), code_(o.code_)
    {
    }

    ~acc_cond()
    {
    }

    void set_acceptance(const acc_code& code)
    {
      code_ = code;
      uses_fin_acceptance_ = check_fin_acceptance();
    }

    acc_code get_acceptance() const
    {
      return code_;
    }

    bool uses_fin_acceptance() const
    {
      return uses_fin_acceptance_;
    }

    void set_generalized_buchi()
    {
      set_acceptance(inf(all_sets()));
    }

    bool is_generalized_buchi() const
    {
      unsigned s = code_.size();
      return (s == 0 && num_ == 0) ||
	(s == 2 && code_[1].op == acc_op::Inf && code_[0].mark == all_sets());
    }

  protected:
    bool check_fin_acceptance() const;

    acc_code primitive(mark_t mark, acc_op op) const
    {
      acc_word w1;
      w1.mark = mark;
      acc_word w2;
      w2.op = op;
      w2.size = 1;
      acc_code c;
      c.push_back(w1);
      c.push_back(w2);
      return c;
    }

  public:
    acc_code inf(mark_t mark) const
    {
      return primitive(mark, acc_op::Inf);
    }

    acc_code inf(std::initializer_list<unsigned> vals) const
    {
      return inf(marks(vals.begin(), vals.end()));
    }

    acc_code inf_neg(mark_t mark) const
    {
      return primitive(mark, acc_op::InfNeg);
    }

    acc_code inf_neg(std::initializer_list<unsigned> vals) const
    {
      return inf_neg(marks(vals.begin(), vals.end()));
    }

    acc_code fin(mark_t mark) const
    {
      return primitive(mark, acc_op::Fin);
    }

    acc_code fin(std::initializer_list<unsigned> vals) const
    {
      return fin(marks(vals.begin(), vals.end()));
    }

    acc_code fin_neg(mark_t mark) const
    {
      return primitive(mark, acc_op::FinNeg);
    }

    acc_code fin_neg(std::initializer_list<unsigned> vals) const
    {
      return fin_neg(marks(vals.begin(), vals.end()));
    }

    unsigned add_sets(unsigned num)
    {
      if (num == 0)
	return -1U;
      unsigned j = num_;
      num_ += num;
      if (num_ > 8 * sizeof(mark_t::id))
	throw std::runtime_error("Too many acceptance sets used.");
      all_ = all_sets_();
      return j;
    }

    unsigned add_set()
    {
      return add_sets(1);
    }

    mark_t mark(unsigned u) const
    {
      return mark_(u);
    }

    template<class iterator>
    mark_t marks(const iterator& begin, const iterator& end) const
    {
      mark_t::value_t res = 0U;
      for (iterator i = begin; i != end; ++i)
	res |= mark_(*i);
      return res;
    }

    mark_t marks(std::initializer_list<unsigned> vals) const
    {
      return marks(vals.begin(), vals.end());
    }

    // FIXME: Return some iterable object without building a vector.
    std::vector<unsigned> sets(mark_t m) const
    {
      return m.sets();
    }

    // whether m contains u
    bool has(mark_t m, unsigned u) const
    {
      return m.has(u);
    }

    mark_t cup(mark_t l, mark_t r) const
    {
      return l | r;
    }

    mark_t cap(mark_t l, mark_t r) const
    {
      return l & r;
    }

    mark_t set_minus(mark_t l, mark_t r) const
    {
      return l - r;
    }

    mark_t join(const acc_cond& la, mark_t lm,
		const acc_cond& ra, mark_t rm) const
    {
      assert(la.num_sets() + ra.num_sets() == num_sets());
      (void)ra;
      return lm.id | (rm.id << la.num_sets());
    }

    mark_t comp(mark_t l) const
    {
      return all_ ^ l.id;
    }

    mark_t all_sets() const
    {
      return all_;
    }

    bool accepting(mark_t inf, mark_t fin) const;

    bool accepting(mark_t inf) const;

    std::ostream& format(std::ostream& os, mark_t m) const
    {
      auto a = m;
      if (a == 0U)
	return os;
      return os << m;
    }

    std::string format(mark_t m) const
    {
      std::ostringstream os;
      format(os, m);
      return os.str();
    }

    unsigned num_sets() const
    {
      return num_;
    }

    template<class iterator>
    mark_t useless(iterator begin, iterator end) const
    {
      mark_t::value_t u = 0U;	// The set of useless marks.
      for (unsigned x = 0; x < num_; ++x)
	{
	  // Skip marks that are already known to be useless.
	  if (u & (1 << x))
	    continue;
	  unsigned all = all_ ^ (u | (1 << x));
	  for (iterator y = begin; y != end; ++y)
	    {
	      auto v = y->id;
	      if (v & (1 << x))
		{
		  all &= v;
		  if (!all)
		    break;
		}
	    }
	  u |= all;
	}
      return u;
    }

    mark_t strip(mark_t x, mark_t y) const
    {
      // strip every bit of x that is marked in y
      // strip(100101110100,
      //       001011001000)
      //   ==  10 1  11 100
      //   ==      10111100

      auto xv = x.id;		// 100101110100
      auto yv = y.id;		// 001011001000

      while (yv && xv)
	{
	  // Mask for everything after the last 1 in y
	  auto rm = (~yv) & (yv - 1);	// 000000000111
	  // Mask for everything before the last 1 in y
	  auto lm = ~(yv ^ (yv - 1));	// 111111110000
	  xv = ((xv & lm) >> 1) | (xv & rm);
	  yv = (yv & lm) >> 1;
	}

      return xv;
    }

  protected:
    mark_t::value_t mark_(unsigned u) const
    {
      assert(u < num_sets());
      return 1U << u;
    }

    mark_t::value_t all_sets_() const
    {
      if (num_ == 0)
	return 0;
      return -1U >> (8 * sizeof(mark_t::value_t) - num_);
    }

    unsigned num_;
    mark_t::value_t all_;
    acc_code code_;
    bool uses_fin_acceptance_ = false;
  };

}

namespace std
{
  template<>
  struct hash<spot::acc_cond::mark_t>
  {
    size_t operator()(spot::acc_cond::mark_t m) const
    {
      std::hash<decltype(m.id)> h;
      return h(m.id);
    }
  };
}

#endif // SPOT_TGBA_ACC_HH
