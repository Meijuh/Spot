// -*- coding: utf-8 -*-
// Copyright (C) 2014-2018 Laboratoire de Recherche et Développement
// de l'Epita.
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
#include <spot/misc/trival.hh>
#include <iostream>

namespace spot
{
  namespace internal
  {
    class mark_container;
  }

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

      explicit operator bool() const
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

      bool subset(mark_t m) const
      {
        return (*this) - m == 0U;
      }

      bool proper_subset(mark_t m) const
      {
        return *this != m && this->subset(m);
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
      // If no set is used, this returns 0,
      // If the sets {1,3,8} are used, this returns 9.
      unsigned max_set() const
      {
#ifdef __GNUC__
        return (id == 0) ? 0 : (sizeof(unsigned) * 8 - __builtin_clz(id));
#else
        auto i = id;
        int res = 0;
        while (i)
          {
            ++res;
            i >>= 1;
          }
        return res;
#endif
      }

      // Return the number of the lowest set used plus one.
      // If no set is used, this returns 0.
      // If the sets {1,3,8} are used, this returns 2.
      unsigned min_set() const
      {
        if (id == 0)
          return 0;
#ifdef __GNUC__
        return __builtin_ctz(id) + 1;
#else
        auto i = id;
        int res = 1;
        while ((i & 1) == 0)
          {
            ++res;
            i >>= 1;
          }
        return res;
#endif
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

      // Returns some iterable object that contains the used sets.
      spot::internal::mark_container sets() const;

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
      } sub;
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
            auto op = (*this)[pos - 1].sub.op;
            auto sz = (*this)[pos - 1].sub.size;
            if (other[pos - 1].sub.op != op ||
                other[pos - 1].sub.size != sz)
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
            auto op = (*this)[pos - 1].sub.op;
            auto oop = other[pos - 1].sub.op;
            if (op < oop)
              return true;
            if (op > oop)
              return false;
            auto sz = (*this)[pos - 1].sub.size;
            auto osz = other[pos - 1].sub.size;
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
                {
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
        return s == 0 || ((*this)[s - 1].sub.op == acc_op::Inf
                          && (*this)[s - 2].mark == 0U);
      }

      bool is_f() const
      {
        unsigned s = size();
        return s > 1
          && (*this)[s - 1].sub.op == acc_op::Fin && (*this)[s - 2].mark == 0U;
      }

      static acc_code f()
      {
        acc_code res;
        res.resize(2);
        res[0].mark = 0U;
        res[1].sub.op = acc_op::Fin;
        res[1].sub.size = 1;
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
        res[1].sub.op = acc_op::Fin;
        res[1].sub.size = 1;
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
        res[1].sub.op = acc_op::FinNeg;
        res[1].sub.size = 1;
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
        res[1].sub.op = acc_op::Inf;
        res[1].sub.size = 1;
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
        res[1].sub.op = acc_op::InfNeg;
        res[1].sub.size = 1;
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
            unsigned f = n++;
            acc_cond::mark_t m = 0U;
            for (unsigned ni = *i; ni > 0; --ni)
              m.set(n++);
            auto pair = inf(m) & fin({f});
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
        // We want to group all Inf(x) operators:
        //   Inf(a) & Inf(b) = Inf(a & b)
        if (((*this)[s].sub.op == acc_op::Inf
             && r[rs].sub.op == acc_op::Inf)
            || ((*this)[s].sub.op == acc_op::InfNeg
                && r[rs].sub.op == acc_op::InfNeg))
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
        if ((*this)[s].sub.op == acc_op::And)
          {
            auto start = &(*this)[s] - (*this)[s].sub.size;
            auto pos = &(*this)[s] - 1;
            pop_back();
            while (pos > start)
              {
                if (pos->sub.op == acc_op::Inf)
                  {
                    left_inf = pos - 1;
                    break;
                  }
                pos -= pos->sub.size + 1;
              }
          }
        else if ((*this)[s].sub.op == acc_op::Inf)
          {
            left_inf = &(*this)[s - 1];
          }

        const acc_word* right_inf = nullptr;
        auto right_end = &r.back();
        if (right_end->sub.op == acc_op::And)
          {
            auto start = &r[0];
            auto pos = --right_end;
            while (pos > start)
            {
              if (pos->sub.op == acc_op::Inf)
                {
                  right_inf = pos - 1;
                  break;
                }
              pos -= pos->sub.size + 1;
            }
          }
        else if (right_end->sub.op == acc_op::Inf)
          {
            right_inf = right_end - 1;
          }

        acc_cond::mark_t carry = 0U;
        if (left_inf && right_inf)
          {
            carry = left_inf->mark;
            auto pos = left_inf - &(*this)[0];
            erase(begin() + pos, begin() + pos + 2);
          }
        auto sz = size();
        insert(end(), &r[0], right_end + 1);
        if (carry)
          (*this)[sz + (right_inf - &r[0])].mark |= carry;

        acc_word w;
        w.sub.op = acc_op::And;
        w.sub.size = size();
        emplace_back(w);
        return *this;
      }

      acc_code operator&(const acc_code& r)
      {
        acc_code res = *this;
        res &= r;
        return res;
      }

      acc_code operator&(acc_code&& r)
      {
        acc_code res = *this;
        res &= r;
        return res;
      }

      acc_code& operator|=(const acc_code& r)
      {
        if (is_t() || r.is_f())
          return *this;
        if (is_f() || r.is_t())
          {
            *this = r;
            return *this;
          }
        unsigned s = size() - 1;
        unsigned rs = r.size() - 1;
        // Fin(a) | Fin(b) = Fin(a | b)
        if (((*this)[s].sub.op == acc_op::Fin
             && r[rs].sub.op == acc_op::Fin)
            || ((*this)[s].sub.op == acc_op::FinNeg
                && r[rs].sub.op == acc_op::FinNeg))
          {
            (*this)[s - 1].mark |= r[rs - 1].mark;
            return *this;
          }

        // In the more complex scenarios, left and right may both
        // be disjunctions, and Fin(x) might be a member of each
        // side.  Find it if it exists.
        // left_inf points to the left Inf mark if any.
        // right_inf points to the right Inf mark if any.
        acc_word* left_fin = nullptr;
        if ((*this)[s].sub.op == acc_op::Or)
          {
            auto start = &(*this)[s] - (*this)[s].sub.size;
            auto pos = &(*this)[s] - 1;
            pop_back();
            while (pos > start)
              {
                if (pos->sub.op == acc_op::Fin)
                  {
                    left_fin = pos - 1;
                    break;
                  }
                pos -= pos->sub.size + 1;
              }
          }
        else if ((*this)[s].sub.op == acc_op::Fin)
          {
            left_fin = &(*this)[s - 1];
          }

        const acc_word* right_fin = nullptr;
        auto right_end = &r.back();
        if (right_end->sub.op == acc_op::Or)
          {
            auto start = &r[0];
            auto pos = --right_end;
            while (pos > start)
            {
              if (pos->sub.op == acc_op::Fin)
                {
                  right_fin = pos - 1;
                  break;
                }
              pos -= pos->sub.size + 1;
            }
          }
        else if (right_end->sub.op == acc_op::Fin)
          {
            right_fin = right_end - 1;
          }

        acc_cond::mark_t carry = 0U;
        if (left_fin && right_fin)
          {
            carry = left_fin->mark;
            auto pos = (left_fin - &(*this)[0]);
            this->erase(begin() + pos, begin() + pos + 2);
          }
        auto sz = size();
        insert(end(), &r[0], right_end + 1);
        if (carry)
          (*this)[sz + (right_fin - &r[0])].mark |= carry;
        acc_word w;
        w.sub.op = acc_op::Or;
        w.sub.size = size();
        emplace_back(w);
        return *this;
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
            switch ((*this)[pos - 1].sub.op)
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

      trival maybe_accepting(mark_t infinitely_often,
                             mark_t always_present) const;


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
      acc_code remove(acc_cond::mark_t rem, bool missing) const;
      // Same as remove, but also shift numbers
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

      // Print the acceptance as Latex.  The set_printer function can
      // be used to implement customized output for set numbers.
      std::ostream&
      to_latex(std::ostream& os,
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

    bool operator==(const acc_cond& other) const
    {
      return other.num_sets() == num_ && other.get_acceptance() == code_;
    }

    bool operator!=(const acc_cond& other) const
    {
      return !(*this == other);
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
        s == 2 && code_[1].sub.op == acc_op::Inf && code_[0].mark == all_sets();
    }

    bool is_co_buchi() const
    {
      return num_ == 1 && is_generalized_co_buchi();
    }

    void set_generalized_buchi()
    {
      set_acceptance(inf(all_sets()));
    }

    void set_generalized_co_buchi()
    {
      set_acceptance(fin(all_sets()));
    }

    bool is_generalized_buchi() const
    {
      unsigned s = code_.size();
      return (s == 0 && num_ == 0) || (s == 2 && code_[1].sub.op == acc_op::Inf
                                       && code_[0].mark == all_sets());
    }

    bool is_generalized_co_buchi() const
    {
      unsigned s = code_.size();
      return (s == 2 &&
              code_[1].sub.op == acc_op::Fin && code_[0].mark == all_sets());
    }

    // Returns a number of pairs (>=0) if Rabin, or -1 else.
    int is_rabin() const;
    // Returns a number of pairs (>=0) if Streett, or -1 else.
    int is_streett() const;

    /// \brief Rabin/streett pairs used by is_rabin_like and is_streett_like.
    ///
    /// These pairs hold two marks which can each contain one or no set.
    ///
    /// For instance is_streett_like() rewrites  Inf(0)&(Inf(2)|Fin(1))&Fin(3)
    /// as three pairs: [(fin={},inf={0}),(fin={1},inf={2}),(fin={3},inf={})].
    ///
    /// Empty marks should be interpreted in a way that makes them
    /// false in Streett, and true in Rabin.
    struct SPOT_API rs_pair
    {
      rs_pair() = default;
      rs_pair(const rs_pair&) = default;

      rs_pair(acc_cond::mark_t fin, acc_cond::mark_t inf):
        fin(fin),
        inf(inf)
        {}
      acc_cond::mark_t fin;
      acc_cond::mark_t inf;

      bool operator==(rs_pair o) const
      {
        return fin == o.fin && inf == o.inf;
      }
      bool operator!=(rs_pair o) const
      {
        return fin != o.fin || inf != o.inf;
      }
      bool operator<(rs_pair o) const
      {
        return fin < o.fin || (!(o.fin < fin) && inf < o.inf);
      }
      bool operator<=(rs_pair o) const
      {
        return !(o < *this);
      }
      bool operator>(rs_pair o) const
      {
        return o < *this;
      }
      bool operator>=(rs_pair o) const
      {
        return !(*this < o);
      }
    };
    /// \brief Test whether an acceptance condition is Streett-like
    ///  and returns each Streett pair in an std::vector<rs_pair>.
    ///
    /// An acceptance condition is Streett-like if it can be transformed into
    /// a Streett acceptance with little modification to its automaton.
    /// A Streett-like acceptance condition follows one of those rules:
    /// -It is a conjunction of disjunctive clauses containing at most one
    ///  Inf and at most one Fin.
    /// -It is true (with 0 pair)
    /// -It is false (1 pair [0U, 0U])
    bool is_streett_like(std::vector<rs_pair>& pairs) const;

    /// \brief Test whether an acceptance condition is Rabin-like
    ///  and returns each Rabin pair in an std::vector<rs_pair>.
    ///
    /// An acceptance condition is Rabin-like if it can be transformed into
    /// a Rabin acceptance with little modification to its automaton.
    /// A Rabin-like acceptance condition follows one of those rules:
    /// -It is a disjunction of conjunctive clauses containing at most one
    ///  Inf and at most one Fin.
    /// -It is true (1 pair [0U, 0U])
    /// -It is false (0 pairs)
    bool is_rabin_like(std::vector<rs_pair>& pairs) const;

    // Return the number of Inf in each pair.
    bool is_generalized_rabin(std::vector<unsigned>& pairs) const;

    // Return the number of Inf in each pair.
    bool is_generalized_streett(std::vector<unsigned>& pairs) const;

    // If EQUIV is false, this return true iff the acceptance
    // condition is a parity condition written in the canonical way
    // given in the HOA specifications.  If EQUIV is true, then we
    // check whether the condition is logically equivalent to some
    // parity acceptance condition.
    bool is_parity(bool& max, bool& odd, bool equiv = false) const;
    bool is_parity() const
    {
      bool max;
      bool odd;
      return is_parity(max, odd);
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

    trival maybe_accepting(mark_t infinitely_often, mark_t always_present) const
    {
      return code_.maybe_accepting(infinitely_often, always_present);
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
    acc_cond remove(mark_t rem, bool missing) const
    {
      return {num_sets(), code_.remove(rem, missing)};
    }

    // Same as remove, but also shift the set numbers
    acc_cond strip(mark_t rem, bool missing) const
    {
      return
        { num_sets() - (all_sets() & rem).count(), code_.strip(rem, missing) };
    }

    // Restrict an acceptance condition to a subset of set numbers
    // that are occurring at some point.
    acc_cond restrict_to(mark_t rem) const
    {
      return {num_sets(), code_.remove(all_sets() - rem, true)};
    }

    /// \brief Return the name of this acceptance condition, in the
    /// specified format.
    ///
    /// The empty string is returned if no name is known.
    ///
    /// \a fmt should be a combination of the following letters.  (0)
    /// no parameters, (a) accentuated, (b) abbreviated, (d) style
    /// used in dot output, (g) no generalized parameter, (l)
    /// recognize Street-like and Rabin-like, (m) no main parameter,
    /// (p) no parity parameter, (o) name unknown acceptance as
    /// 'other', (s) shorthand for 'lo0'.
    std::string name(const char* fmt = "alo") const;

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

  struct rs_pairs_view {
    typedef std::vector<acc_cond::rs_pair> rs_pairs;

    // Creates view of pairs 'p' with restriction only to marks in 'm'
    explicit rs_pairs_view(const rs_pairs& p, const acc_cond::mark_t& m)
      : pairs_(p), view_marks_(m) {}

    // Creates view of pairs without restriction to marks
    explicit rs_pairs_view(const rs_pairs& p)
      : rs_pairs_view(p, std::numeric_limits<unsigned>::max()) {}

    acc_cond::mark_t infs() const
    {
      return do_view([&](const acc_cond::rs_pair& p)
        {
          return visible(p.inf) ? p.inf : 0U;
        });
    }

    acc_cond::mark_t fins() const
    {
      return do_view([&](const acc_cond::rs_pair& p)
        {
          return visible(p.fin) ? p.fin : 0U;
        });
    }

    acc_cond::mark_t fins_alone() const
    {
      return do_view([&](const acc_cond::rs_pair& p)
        {
          return !visible(p.inf) && visible(p.fin) ? p.fin : 0U;
        });
    }

    acc_cond::mark_t infs_alone() const
    {
      return do_view([&](const acc_cond::rs_pair& p)
        {
          return !visible(p.fin) && visible(p.inf) ? p.inf : 0U;
        });
    }

    acc_cond::mark_t paired_with(unsigned mark) const
    {
      acc_cond::mark_t res = 0U;
      for (const auto& p: pairs_)
      {
        if (visible(p.fin) && visible(p.inf))
          {
            if (p.fin.has(mark))
              res |= p.inf;
            if (p.inf.has(mark))
              res |= p.fin;
          }
      }
      return res;
    }

    const rs_pairs& pairs() const
    {
      return pairs_;
    }

  private:
    template<typename filter>
    acc_cond::mark_t do_view(const filter& filt) const
    {
      acc_cond::mark_t res = 0U;
      for (const auto& p: pairs_)
        res |= filt(p);
      return res;
    }

    bool visible(const acc_cond::mark_t& v) const
    {
      return (view_marks_ & v) != 0;
    }

    const rs_pairs& pairs_;
    acc_cond::mark_t view_marks_;
  };


  SPOT_API
  std::ostream& operator<<(std::ostream& os, const acc_cond& acc);

  namespace internal
  {
    class SPOT_API mark_iterator
    {
    public:
      typedef unsigned value_type;
      typedef const value_type& reference;
      typedef const value_type* pointer;
      typedef std::ptrdiff_t difference_type;
      typedef std::forward_iterator_tag iterator_category;

      mark_iterator() noexcept
        : m_(0U)
      {
      }

      mark_iterator(acc_cond::mark_t m) noexcept
        : m_(m)
      {
      }

      bool operator==(mark_iterator m) const
      {
        return m_ == m.m_;
      }

      bool operator!=(mark_iterator m) const
      {
        return m_ != m.m_;
      }

      value_type operator*() const
      {
        SPOT_ASSERT(m_);
        return m_.min_set() - 1;
      }

      mark_iterator operator++()
      {
        m_.id &= m_.id - 1;
        return *this;
      }

      mark_iterator operator++(int)
      {
        mark_iterator it = *this;
        ++(*this);
        return it;
      }
    private:
      acc_cond::mark_t m_;
    };

    class SPOT_API mark_container
    {
    public:
      mark_container(spot::acc_cond::mark_t m) noexcept
        : m_(m)
      {
      }

      mark_iterator begin() const
      {
        return {m_};
      }
      mark_iterator end() const
      {
        return {};
      }
    private:
      spot::acc_cond::mark_t m_;
    };
  }

  inline spot::internal::mark_container acc_cond::mark_t::sets() const
  {
    return {*this};
  }
}

namespace std
{
  template<>
  struct hash<spot::acc_cond::mark_t>
  {
    size_t operator()(spot::acc_cond::mark_t m) const noexcept
    {
      std::hash<decltype(m.id)> h;
      return h(m.id);
    }
  };
}
