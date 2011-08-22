// Copyright (C) 2008, 2009, 2010, 2011 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2004, 2006, 2007 Laboratoire d'Informatique de
// Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
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

#include "reduce.hh"
#include "ltlast/allnodes.hh"
#include <cassert>

#include "lunabbrev.hh"
#include "simpfg.hh"
#include "nenoform.hh"
#include "contain.hh"
#include "simplify.hh"

namespace spot
{
  namespace ltl
  {

    formula*
    reduce(const formula* f, int opt)
    {
      formula* f1;
      formula* f2;
      formula* prev = 0;

      ltl_simplifier_options o;
      o.reduce_basics = opt & Reduce_Basics;
      o.synt_impl = opt & Reduce_Syntactic_Implications;
      o.event_univ = opt & Reduce_Eventuality_And_Universality;
      o.containment_checks = opt & Reduce_Containment_Checks;
      o.containment_checks_stronger = opt & Reduce_Containment_Checks_Stronger;
      ltl_simplifier simplifier(o);

      int n = 0;

      while (f != prev)
	{
	  ++n;
	  assert(n < 100);
	  if (prev)
	    {
	      prev->destroy();
	      prev = const_cast<formula*>(f);
	    }
	  else
	    {
	      prev = f->clone();
	    }
	  f1 = unabbreviate_logic(f);
	  f2 = simplify_f_g(f1);
	  f1->destroy();
	  f1 = negative_normal_form(f2);
	  f2->destroy();
	  f2 = f1;

	  f1 = simplifier.simplify(f2);
	  f2->destroy();
	  f2 = f1;

	  if (opt & (Reduce_Containment_Checks
		     | Reduce_Containment_Checks_Stronger))
	    {
	      formula* f1 =
		reduce_tau03(f2,
			     opt & Reduce_Containment_Checks_Stronger);
	      f2->destroy();
	      f2 = f1;
	    }
	  f = f2;
	}
      prev->destroy();

      return const_cast<formula*>(f);
    }

    bool
    is_eventual(const formula* f)
    {
      return f->is_eventual();
    }

    bool
    is_universal(const formula* f)
    {
      return f->is_universal();
    }
  }
}
