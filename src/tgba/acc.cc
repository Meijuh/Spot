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
    eval(acc_cond::mark_t inf, acc_cond::mark_t fin,
	 const acc_cond::acc_code& code, unsigned pos)
    {
      auto& w = code[pos];
      switch (w.op)
	{
	case acc_cond::acc_op::And:
	  {
	    unsigned sub = pos - w.size;
	    while (sub < pos)
	      {
		--pos;
		if (!eval(inf, fin, code, pos))
		  return false;
		pos -= code[pos].size;
	      }
	    return true;
	  }
	case acc_cond::acc_op::Or:
	  {
	    unsigned sub = pos - w.size;
	    while (sub < pos)
	      {
		--pos;
		if (eval(inf, fin, code, pos))
		  return true;
		pos -= code[pos].size;
	      }
	    return false;
	  }
	case acc_cond::acc_op::Inf:
	  return (code[pos - 1].mark & inf) == code[pos - 1].mark;
	case acc_cond::acc_op::Fin:
	  return (code[pos - 1].mark & fin) != 0U;
	case acc_cond::acc_op::FinNeg:
	case acc_cond::acc_op::InfNeg:
	  SPOT_UNREACHABLE();
	}
      SPOT_UNREACHABLE();
      return false;
    }
  }

  bool acc_cond::accepting(mark_t inf, mark_t fin) const
  {
    if (code_.empty())
      return true;
    return eval(inf, fin, code_, code_.size() - 1);
  }

  bool acc_cond::accepting(mark_t inf) const
  {
    if (uses_fin_acceptance())
      throw std::runtime_error
	("Fin acceptance is not supported by this code path.");
    return accepting(inf, 0U);
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
	  case acc_cond::acc_op::FinNeg:
	    return true;
	  }
      }
    while (pos > 0);
    return false;
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
