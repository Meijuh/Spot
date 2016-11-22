// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015, 2016 Laboratoire de Recherche et
// Développement de l'Epita.
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

#pragma once

#include <functional>
#include <unordered_map>
#include <sstream>
#include <vector>
#include <spot/tl/defaultenv.hh>
#include <iostream>

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

      mark_t(value_t id) noexcept
        : id(id)
      {
      }

      template<class iterator>
      mark_t(const iterator& begin, const iterator& end) noexcept
      {
        id = 0U;
        for (iterator i = begin; i != end; ++i)
          set(*i);
      }

      mark_t(std::initializer_list<unsigned> vals) noexcept
        : mark_t(vals.begin(), vals.end())
      {
      }

      bool operator==(unsigned o) const
      {
        SPOT_ASSERT(o == 0U);
        return id == o;
      }

      bool operator!=(unsigned o) const
      {
        SPOT_ASSERT(o == 0U);
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

      void clear(unsigned u)
      {
        id &= ~(1U << u);
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

      mark_t operator~() const
      {
        return ~id;
      }

      mark_t operator^(mark_t r) const
      {
        return id ^ r.id;
      }

      mark_t operator<<(unsigned i) const
      {
        return id << i;
      }

      mark_t& operator<<=(unsigned i)
      {
        id <<= i;
        return *this;
      }

      mark_t operator>>(unsigned i) const
      {
        return id >> i;
      }

      mark_t& operator>>=(unsigned i)
      {
        id >>= i;
        return *this;
      }

      mark_t strip(mark_t y) const
      {
        // strip every bit of id that is marked in y
        //       100101110100.strip(
        //       001011001000)
        //   ==  10 1  11 100
        //   ==      10111100

        auto xv = id;                // 100101110100
        auto yv = y.id;                // 001011001000

        while (yv && xv)
          {
            // Mask for everything after the last 1 in y
            auto rm = (~yv) & (yv - 1);        // 000000000111
            // Mask for everything before the last 1 in y
            auto lm = ~(yv ^ (yv - 1));        // 111111110000
            xv = ((xv & lm) >> 1) | (xv & rm);
            yv = (yv & lm) >> 1;
          }
        return xv;
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

      // Return the number of the highest set used plus one.
      // So if no set is used, this returns 0,
      // but if the sets {1,3,8} are used, this returns 9.
      unsigned max_set() const
      {
        auto i = id;
        int res = 0;
        while (i)
          {
            ++res;
            i >>= 1;
          }
        return res;
      }

      // Return the lowest acceptance mark
      mark_t lowest() const
      {
        return id & -id;
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
    enum class acc_op : unsigned short
    { Inf, Fin, InfNeg, FinNeg, And, Or };
    union acc_word
    {
      mark_t mark;
      struct {
        acc_op op;             // Operator
        unsigned short size; // Size of the subtree (number of acc_word),
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

      bool is_t() const
      {
        unsigned s = size();
        return s == 0
          || ((*this)[s - 1].op == acc_op::Inf && (*this)[s - 2].mark == 0U);
      }

      bool is_f() const
      {
        unsigned s = size();
        return s > 1
          && (*this)[s - 1].op == acc_op::Fin && (*this)[s - 2].mark == 0U;
      }

      static acc_code f()
      {
        acc_code res;
        res.resize(2);
        res[0].mark = 0U;
        res[1].op = acc_op::Fin;
        res[1].size = 1;
        return res;
      }

      static acc_code t()
      {
        return {};
      }

      static acc_code fin(mark_t m)
      {
        acc_code res;
        res.resize(2);
        res[0].mark = m;
        res[1].op = acc_op::Fin;
        res[1].size = 1;
        return res;
      }

      static acc_code fin(std::initializer_list<unsigned> vals)
      {
        return fin(mark_t(vals));
      }

      static acc_code fin_neg(mark_t m)
      {
        acc_code res;
        res.resize(2);
        res[0].mark = m;
        res[1].op = acc_op::FinNeg;
        res[1].size = 1;
        return res;
      }

      static acc_code fin_neg(std::initializer_list<unsigned> vals)
      {
        return fin_neg(mark_t(vals));
      }

      static acc_code inf(mark_t m)
      {
        acc_code res;
        res.resize(2);
        res[0].mark = m;
        res[1].op = acc_op::Inf;
        res[1].size = 1;
        return res;
      }

      static acc_code inf(std::initializer_list<unsigned> vals)
      {
        return inf(mark_t(vals));
      }

      static acc_code inf_neg(mark_t m)
      {
        acc_code res;
        res.resize(2);
        res[0].mark = m;
        res[1].op = acc_op::InfNeg;
        res[1].size = 1;
        return res;
      }

      static acc_code inf_neg(std::initializer_list<unsigned> vals)
      {
        return inf_neg(mark_t(vals));
      }

      static acc_code buchi()
      {
        return inf({0});
      }

      static acc_code cobuchi()
      {
        return fin({0});
      }

      static acc_code generalized_buchi(unsigned n)
      {
        acc_cond::mark_t m = (1U << n) - 1;
        if (n == 8 * sizeof(mark_t::value_t))
          m = mark_t(-1U);
        return inf(m);
      }

      static acc_code generalized_co_buchi(unsigned n)
      {
        acc_cond::mark_t m = (1U << n) - 1;
        if (n == 8 * sizeof(mark_t::value_t))
          m = mark_t(-1U);
        return fin(m);
      }

      // n is a number of pairs.
      static acc_code rabin(unsigned n)
      {
        acc_cond::acc_code res = f();
        while (n > 0)
          {
            res |= inf({2*n - 1}) & fin({2*n - 2});
            --n;
          }
        return res;
      }

       // n is a number of pairs.
      static acc_code streett(unsigned n)
      {
        acc_cond::acc_code res = t();
        while (n > 0)
          {
            res &= inf({2*n - 1}) | fin({2*n - 2});
            --n;
          }
        return res;
      }

      template<class Iterator>
      static acc_code generalized_rabin(Iterator begin, Iterator end)
      {
        acc_cond::acc_code res = f();
        unsigned n = 0;
        for (Iterator i = begin; i != end; ++i)
          {
            acc_cond::acc_code pair = fin({n++});
            acc_cond::mark_t m = 0U;
            for (unsigned ni = *i; ni > 0; --ni)
              m.set(n++);
            pair &= inf(m);
            std::swap(pair, res);
            res |= std::move(pair);
          }
        return res;
      }

      static acc_code parity(bool max, bool odd, unsigned sets);

      // Number of acceptance sets to use, and probability to reuse
      // each set another time after it has been used in the
      // acceptance formula.
      static acc_code random(unsigned n, double reuse = 0.0);

      acc_code& operator&=(acc_code&& r)
      {
        if (is_t() || r.is_f())
          {
            *this = std::move(r);
            return *this;
          }
        if (is_f() || r.is_t())
          return *this;
        unsigned s = size() - 1;
        unsigned rs = r.size() - 1;
        // We want to group all Inf(x) operators:
        //   Inf(a) & Inf(b) = Inf(a & b)
        if (((*this)[s].op == acc_op::Inf && r[rs].op == acc_op::Inf)
            || ((*this)[s].op == acc_op::InfNeg && r[rs].op == acc_op::InfNeg))
          {
            (*this)[s - 1].mark |= r[rs - 1].mark;
            return *this;
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
        emplace_back(w);
        return *this;
      }

      acc_code& operator&=(const acc_code& r)
      {
        if (is_t() || r.is_f())
          {
            *this = r;
            return *this;
          }
        if (is_f() || r.is_t())
          return *this;
        unsigned s = size() - 1;
        unsigned rs = r.size() - 1;
        // Inf(a) & Inf(b) = Inf(a & b)
        if (((*this)[s].op == acc_op::Inf && r[rs].op == acc_op::Inf)
            || ((*this)[s].op == acc_op::InfNeg && r[rs].op == acc_op::InfNeg))
          {
            (*this)[s - 1].mark |= r[rs - 1].mark;
            return *this;
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
        emplace_back(w);
        return *this;
      }

      acc_code operator&(acc_code&& r)
      {
        acc_code res = *this;
        res &= r;
        return res;
      }

      acc_code operator&(const acc_code& r)
      {
        acc_code res = *this;
        res &= r;
        return res;
      }

      acc_code& operator|=(acc_code&& r)
      {
        if (is_t() || r.is_f())
          return *this;
        if (is_f() || r.is_t())
          {
            *this = std::move(r);
            return *this;
          }
        unsigned s = size() - 1;
        unsigned rs = r.size() - 1;
        // Fin(a) | Fin(b) = Fin(a | b)
        if (((*this)[s].op == acc_op::Fin && r[rs].op == acc_op::Fin)
            || ((*this)[s].op == acc_op::FinNeg && r[rs].op == acc_op::FinNeg))
          {
            (*this)[s - 1].mark |= r[rs - 1].mark;
            return *this;
          }
        if ((*this)[s].op == acc_op::Or)
          pop_back();
        if (r.back().op == acc_op::Or)
          r.pop_back();
        insert(this->end(), r.begin(), r.end());
        acc_word w;
        w.op = acc_op::Or;
        w.size = size();
        emplace_back(w);
        return *this;
      }

      acc_code& operator|=(const acc_code& r)
      {
        return *this |= acc_code(r);
      }

      acc_code operator|(acc_code&& r)
      {
        acc_code res = *this;
        res |= r;
        return res;
      }

      acc_code operator|(const acc_code& r)
      {
        acc_code res = *this;
        res |= r;
        return res;
      }

      acc_code& operator<<=(unsigned sets)
      {
        if (empty())
          return *this;
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
        return *this;
      }

      acc_code operator<<(unsigned sets) const
      {
        acc_code res = *this;
        res <<= sets;
        return res;
      }

      bool is_dnf() const;
      bool is_cnf() const;

      acc_code to_dnf() const;
      acc_code to_cnf() const;

      acc_code complement() const;

      // Return a list of acceptance marks needed to close a cycle
      // that already visit INF infinitely often, so that the cycle is
      // accepting (ACCEPTING=true) or rejecting (ACCEPTING=false).
      // Positive values describe positive set.
      // A negative value x means the set -x-1 must be absent.
      std::vector<std::vector<int>>
        missing(mark_t inf, bool accepting) const;

      bool accepting(mark_t inf) const;

      bool inf_satisfiable(mark_t inf) const;

      // Remove all the acceptance sets in rem.
      //
      // If MISSING is set, the acceptance sets are assumed to be
      // missing from the automaton, and the acceptance is updated to
      // reflect this.  For instance (Inf(1)&Inf(2))|Fin(3) will
      // become Fin(3) if we remove 2 because it is missing from this
      // automaton, because there is no way to fulfill Inf(1)&Inf(2)
      // in this case.  So essentially MISSING causes Inf(rem) to
      // become f, and Fin(rem) to become t.
      //
      // If MISSING is unset, Inf(rem) become t while Fin(rem) become
      // f.  Removing 2 from (Inf(1)&Inf(2))|Fin(3) would then give
      // Inf(1)|Fin(3).
      acc_code strip(acc_cond::mark_t rem, bool missing) const;

      // Return the set of sets appearing in the condition.
      acc_cond::mark_t used_sets() const;

      // Return the sets used as Inf or Fin in the acceptance condition
      std::pair<acc_cond::mark_t, acc_cond::mark_t> used_inf_fin_sets() const;

      // Print the acceptance as HTML.  The set_printer function can
      // be used to implement customized output for set numbers.
      std::ostream&
      to_html(std::ostream& os,
              std::function<void(std::ostream&, int)>
              set_printer = nullptr) const;

      // Print the acceptance as text.  The set_printer function can
      // be used to implement customized output for set numbers.
      std::ostream&
      to_text(std::ostream& os,
              std::function<void(std::ostream&, int)>
              set_printer = nullptr) const;


      /// \brief Construct an acc_code from a string.
      ///
      /// The string can follow the following grammar:
      ///
      /// <pre>
      ///   acc ::= "t"
      ///         | "f"
      ///         | "Inf" "(" num ")"
      ///         | "Fin" "(" num ")"
      ///         | "(" acc ")"
      ///         | acc "&" acc
      ///         | acc "|" acc
      /// </pre>
      ///
      /// Where num is an integer and "&" has priority over "|".  Note that
      /// "Fin(!x)" and "Inf(!x)" are not supported by this parser.
      ///
      /// Or the string can be the name of an acceptance condition, as
      /// speficied in the HOA format.  (E.g. "Rabin 2", "parity max odd 3",
      /// "generalized-Rabin 4 2 1", etc.).
      ///
      /// A spot::parse_error is thrown on syntax error.
      acc_code(const char* input);

      /// \brief Build an empty acceptance condition.
      ///
      /// This is the same as t().
      acc_code()
      {
      }

      // Calls to_text
      SPOT_API
      friend std::ostream& operator<<(std::ostream& os, const acc_code& code);
    };

    acc_cond(unsigned n_sets = 0, const acc_code& code = {})
      : num_(0U), all_(0U), code_(code)
    {
      add_sets(n_sets);
      uses_fin_acceptance_ = check_fin_acceptance();
    }

    acc_cond(const acc_code& code)
      : num_(0U), all_(0U), code_(code)
    {
      add_sets(code.used_sets().max_set());
      uses_fin_acceptance_ = check_fin_acceptance();
    }

    acc_cond(const acc_cond& o)
      : num_(o.num_), all_(o.all_), code_(o.code_),
        uses_fin_acceptance_(o.uses_fin_acceptance_)
    {
    }

    acc_cond& operator=(const acc_cond& o)
    {
      num_ = o.num_;
      all_ = o.all_;
      code_ = o.code_;
      uses_fin_acceptance_ = o.uses_fin_acceptance_;
      return *this;
    }

    ~acc_cond()
    {
    }

    void set_acceptance(const acc_code& code)
    {
      code_ = code;
      uses_fin_acceptance_ = check_fin_acceptance();
    }

    const acc_code& get_acceptance() const
    {
      return code_;
    }

    acc_code& get_acceptance()
    {
      return code_;
    }

    bool uses_fin_acceptance() const
    {
      return uses_fin_acceptance_;
    }

    bool is_t() const
    {
      return code_.is_t();
    }

    bool is_all() const
    {
      return num_ == 0 && is_t();
    }

    bool is_f() const
    {
      return code_.is_f();
    }

    bool is_none() const
    {
      return num_ == 0 && is_f();
    }

    bool is_buchi() const
    {
      unsigned s = code_.size();
      return num_ == 1 &&
        s == 2 && code_[1].op == acc_op::Inf && code_[0].mark == all_sets();
    }

    bool is_co_buchi() const
    {
      return num_ == 1 && is_generalized_co_buchi();
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

    bool is_generalized_co_buchi() const
    {
      unsigned s = code_.size();
      return (s == 2 &&
              code_[1].op == acc_op::Fin && code_[0].mark == all_sets());
    }

    // Returns a number of pairs (>=0) if Rabin, or -1 else.
    int is_rabin() const;
    // Returns a number of pairs (>=0) if Streett, or -1 else.
    int is_streett() const;

    // Return the number of Inf in each pair.
    bool is_generalized_rabin(std::vector<unsigned>& pairs) const;

    // If EQUIV is false, this return true iff the acceptance
    // condition is a parity condition written in the canonical way
    // given in the HOA specifications.  If EQUIV is true, then we
    // check whether the condition is logically equivalent to some
    // parity acceptance condition.
    bool is_parity(bool& max, bool& odd, bool equiv = false) const;
    bool is_parity() const
    {
      bool max;
      bool min;
      return is_parity(max, min);
    }

    // Return (true, m) if there exist some acceptance mark m that
    // does not satisfy the acceptance condition.  Return (false, 0U)
    // otherwise.
    std::pair<bool, acc_cond::mark_t> unsat_mark() const;

  protected:
    bool check_fin_acceptance() const;

  public:
    static acc_code inf(mark_t mark)
    {
      return acc_code::inf(mark);
    }

    static acc_code inf(std::initializer_list<unsigned> vals)
    {
      return inf(mark_t(vals.begin(), vals.end()));
    }

    static acc_code inf_neg(mark_t mark)
    {
      return acc_code::inf_neg(mark);
    }

    static acc_code inf_neg(std::initializer_list<unsigned> vals)
    {
      return inf_neg(mark_t(vals.begin(), vals.end()));
    }

    static acc_code fin(mark_t mark)
    {
      return acc_code::fin(mark);
    }

    static acc_code fin(std::initializer_list<unsigned> vals)
    {
      return fin(mark_t(vals.begin(), vals.end()));
    }

    static acc_code fin_neg(mark_t mark)
    {
      return acc_code::fin_neg(mark);
    }

    static acc_code fin_neg(std::initializer_list<unsigned> vals)
    {
      return fin_neg(mark_t(vals.begin(), vals.end()));
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
      SPOT_ASSERT(u < num_sets());
      return 1U << u;
    }

    mark_t comp(mark_t l) const
    {
      return all_ ^ l.id;
    }

    mark_t all_sets() const
    {
      return all_;
    }

    bool accepting(mark_t inf) const
    {
      return code_.accepting(inf);
    }

    bool inf_satisfiable(mark_t inf) const
    {
      return code_.inf_satisfiable(inf);
    }

    mark_t accepting_sets(mark_t inf) const;

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
      mark_t::value_t u = 0U;        // The set of useless marks.
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

  protected:
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

  SPOT_API
  std::ostream& operator<<(std::ostream& os, const acc_cond& acc);
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
