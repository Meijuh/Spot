// Copyright (C) 2009, 2010 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include "bunop.hh"
#include "visitor.hh"
#include <cassert>
#include <iostream>
#include <sstream>
#include "constant.hh"
#include "unop.hh"
#include "ltlvisit/kind.hh"

namespace spot
{
  namespace ltl
  {
    bunop::bunop(type op, formula* child, unsigned min, unsigned max)
      : op_(op), child_(child), min_(min), max_(max)
    {
    }

    bunop::~bunop()
    {
      // Get this instance out of the instance map.
      pair p(pairo(op(), child()), pairu(min_, max_));
      map::iterator i = instances.find(p);
      assert (i != instances.end());
      instances.erase(i);

      // Dereference child.
      child()->destroy();
    }

    std::string
    bunop::dump() const
    {
      std::ostringstream out;
      out << "bunop(" << op_name() << ", "
	  << child()->dump() << ", " << min_ << ", ";
      if (max_ == unbounded)
	out << "unbounded";
      else
	out << max_;
      out << ")";
      return out.str();
    }

    void
    bunop::accept(visitor& v)
    {
      v.visit(this);
    }

    void
    bunop::accept(const_visitor& v) const
    {
      v.visit(this);
    }

    const formula*
    bunop::child() const
    {
      return child_;
    }

    formula*
    bunop::child()
    {
      return child_;
    }

    unsigned
    bunop::min() const
    {
      return min_;
    }

    unsigned
    bunop::max() const
    {
      return max_;
    }

    bunop::type
    bunop::op() const
    {
      return op_;
    }

    const char*
    bunop::op_name() const
    {
      switch (op_)
	{
	case Equal:
	  return "Equal";
	case Star:
	  return "Star";
	}
      // Unreachable code.
      assert(0);
      return 0;
    }

    std::string
    bunop::format() const
    {
      std::ostringstream out;

      switch (op_)
	{
	case Star:
	  // Syntactic sugaring
	  if (min_ == 1 && max_ == unbounded)
	    {
	      out << "[+]";
	      return out.str();
	    }
	  out << "[*";
	  break;
	case Equal:
	  out << "[=";
	  break;
	}

      if (min_ != 0 || max_ != unbounded)
	{
	  out << min_;
	  if (min_ != max_)
	    {
	      out << "..";
	      if (max_ != unbounded)
		out << max_;
	    }
	}
      out << "]";
      return out.str();
    }

    bunop::map bunop::instances;

    formula*
    bunop::instance(type op, formula* child, unsigned min, unsigned max)
    {
      assert(min <= max);

      // Some trivial simplifications.

      switch (op)
	{
	case Equal:
	  {
	    //   - 0[=0..max] = [*]
	    //   - 0[=min..max] = 0 if min > 0
	    if (child == constant::false_instance())
	      {
		if (min == 0)
		  {
		    max = -1U;
		    op = Star;
		    child = constant::true_instance();
		    break;
		  }
		else
		  return child;
	      }
	    //   - 1[=0] = [*0]
	    //   - 1[=min..max] = 1[*min..max]
	    if (child == constant::true_instance())
	      {
		if (max == 0)
		  return constant::empty_word_instance();
		else
		  {
		    op = Star;
		    break;
		  }
	      }
	    //   - Exp[=0] = (!Exp)[*]
	    if (max == 0)
	      return bunop::instance(bunop::Star,
				     unop::instance(unop::Not, child));
	    break;
	  }
	case Star:
	  {
	    //   - [*0][*min..max] = [*0]
	    if (child == constant::empty_word_instance())
	      return child;

	    //   - 0[*0..max] = [*0]
	    //   - 0[*min..max] = 0 if min > 0
	    if (child == constant::false_instance())
	      {
		if (min == 0)
		  return constant::empty_word_instance();
		else
		  return child;
	      }

	    //   - Exp[*0] = [*0]
	    if (max == 0)
	      {
		child->destroy();
		return constant::empty_word_instance();
	      }

	    // - Exp[*i..j][*min..max] = Exp[*i(min)..j(max)]
	    //                                       if i*(min+1)<=j(min)+1.
	    bunop* s = dynamic_cast<bunop*>(child);
	    if (s)
	      {
		unsigned i = s->min();
		unsigned j = s->max();

		// Exp has to be true between i*min and j*min
		//               then between i*(min+1) and j*(min+1)
		//               ...
		//            finally between i*max and j*max
		//
		// We can merge these intervals into [i*min..j*max] iff the
		// first are adjacent or overlap, i.e. iff
		//   i*(min+1) <= j*min+1.
		// (Because i<=j, this entails that the other intervals also
		// overlap).

		formula* exp = s->child();
		if (j == unbounded)
		  {
		    min *= i;
		    max = unbounded;

		    // Exp[*min..max]
		    exp->clone();
		    child->destroy();
		    child = exp;
		  }
		else
		  {
		    if (i * (min + 1) <= (j * min) + 1)
		      {
			min *= i;
			if (max != unbounded)
			  {
			    if (j == unbounded)
			      max = unbounded;
			    else
			      max *= j;
			  }
			exp->clone();
			child->destroy();
			child = exp;
		      }
		  }
	      }
	    break;
	  }
	}

      pair p(pairo(op, child), pairu(min, max));
      map::iterator i = instances.find(p);
      if (i != instances.end())
	{
	  // This instance already exists.
	  child->destroy();
	  return i->second->clone();
	}
      bunop* ap = new bunop(op, child, min, max);
      instances[p] = ap;
      return static_cast<bunop*>(ap->clone());
    }

    unsigned
    bunop::instance_count()
    {
      return instances.size();
    }

    std::ostream&
    bunop::dump_instances(std::ostream& os)
    {
      for (map::iterator i = instances.begin(); i != instances.end(); ++i)
	{
	  os << i->second << " = "
	     << i->second->ref_count_() << " * "
	     << i->second->dump()
	     << std::endl;
	}
      return os;
    }

  }
}
