// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement de
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
# include "bdddict.hh"
# include "ltlenv/defaultenv.hh"

namespace spot
{
  class acc_cond
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

      friend std::ostream& operator<<(std::ostream& os, mark_t m)
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
    };

    acc_cond(const bdd_dict_ptr& dict, unsigned n_sets = 0)
      : d_(dict), num_(0U), all_(0U)
    {
      add_sets(n_sets);
    }

    acc_cond(const acc_cond& o)
      : num_(o.num_), all_(o.all_)
    {
    }

    ~acc_cond()
    {
    }

    const bdd_dict_ptr& get_dict() const
    {
      return d_;
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
      return out(mark_(u));
    }

    template<class iterator>
    mark_t marks(const iterator& begin, const iterator& end) const
    {
      mark_t::value_t res = 0U;
      for (iterator i = begin; i != end; ++i)
	res |= mark_(*i);
      return out(res);
    }

    mark_t marks(std::initializer_list<unsigned> vals) const
    {
      return marks(vals.begin(), vals.end());
    }

    template<class iterator>
    void fill_from(mark_t m, iterator here) const
    {
      auto a = in(m);
      unsigned level = 0;
      while (a)
	{
	  if (a & 1)
	    *here++ = level;
	  ++level;
	  a >>= 1;
	}
      assert(level <= num_sets());
    }

    // FIXME: Return some iterable object without building a vector.
    std::vector<unsigned> sets(mark_t m) const
    {
      std::vector<unsigned> res;
      fill_from(m, std::back_inserter(res));
      return res;
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
      return la.in(lm) | (ra.in(rm) << la.num_sets());
    }

    mark_t comp(mark_t l) const
    {
      return out(all_ ^ in(l));
    }

    mark_t all_sets() const
    {
      return out(all_);
    }

    bool accepting(mark_t inf) const
    {
      return in(inf) == all_;
    }

    std::ostream& format_quoted(std::ostream& os, mark_t m) const
    {
      auto a = in(m);
      if (a == 0U)
	return os;
      unsigned level = 0;
      const char* space = "";
      while (a)
	{
	  if (a & 1)
	    {
	      os << space << '"' << level << '"';
	      space = " ";
	    }
	  a >>= 1;
	  ++level;
	}
      return os;
    }

    std::ostream& format(std::ostream& os, mark_t m) const
    {
      auto a = in(m);
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
	      auto v = in(*y);
	      if (v & (1 << x))
		{
		  all &= v;
		  if (!all)
		    break;
		}
	    }
	  u |= all;
	}
      return out(u);
    }

    mark_t strip(mark_t x, mark_t y) const
    {
      // strip every bit of x that is marked in y
      // strip(100101110100,
      //       001011001000)
      //   ==  10 1  11 100
      //   ==      10111100

      auto xv = in(x);		// 100101110100
      auto yv = in(y);		// 001011001000

      while (yv && xv)
	{
	  // Mask for everything after the last 1 in y
	  auto rm = (~yv) & (yv - 1);	// 000000000111
	  // Mask for everything before the last 1 in y
	  auto lm = ~(yv ^ (yv - 1));	// 111111110000
	  xv = ((xv & lm) >> 1) | (xv & rm);
	  yv = (yv & lm) >> 1;
	}

      return out(xv);
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

    mark_t::value_t in(mark_t m) const
    {
      return m.id;
    }

    mark_t out(mark_t::value_t r) const
    {
      return r;
    }

    bdd_dict_ptr d_;
    unsigned num_;
    mark_t::value_t all_;
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
