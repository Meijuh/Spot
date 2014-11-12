// Copyright (C) 2014 Laboratoire de Recherche et Développement
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


#include <iostream>
#include "tgba/tgbagraph.hh"
#include "closure.hh"
#include "stutterize.hh"
#include "ltlvisit/remove_x.hh"
#include "tgbaalgos/translate.hh"
#include "ltlast/allnodes.hh"
#include "ltlvisit/apcollect.hh"
#include "stutter_invariance.hh"
#include "tgba/tgbasl.hh"
#include "tgba/tgbaproduct.hh"
#include "tgbaalgos/dupexp.hh"

namespace spot
{
  // The stutter check algorithm to use can be overridden via an
  // environment variable.
  static int default_stutter_check_algorithm()
  {
    static const char* stutter_check = getenv("SPOT_STUTTER_CHECK");
    if (stutter_check)
      {
	char* endptr;
	long res = strtol(stutter_check, &endptr, 10);
	if (*endptr || res < 0 || res > 8)
	  throw
	    std::runtime_error("invalid value for SPOT_STUTTER_CHECK.");
	return res;
      }
    else
      {
	return 8;     // The best variant, according to our benchmarks.
      }
  }

  bool
  is_stutter_invariant(const ltl::formula* f)
  {
    if (f->is_ltl_formula() && f->is_X_free())
      return true;

    int algo = default_stutter_check_algorithm();

    if (algo == 0) // Etessami's check via syntactic transformation.
      {
	if (!f->is_ltl_formula())
	  throw std::runtime_error("Cannot use the syntactic "
				   "stutter-invariance check "
				   "for non-LTL formulas");
	const ltl::formula* g = remove_x(f);
	ltl::ltl_simplifier ls;
	bool res = ls.are_equivalent(f, g);
	g->destroy();
	return res;
      }

    // Prepare for an automata-based check.
    const ltl::formula* nf = ltl::unop::instance(ltl::unop::Not, f->clone());
    translator trans;
    auto aut_f = trans.run(f);
    auto aut_nf = trans.run(nf);
    bdd aps = atomic_prop_collect_as_bdd(f, aut_f);
    nf->destroy();
    return is_stutter_invariant(std::move(aut_f), std::move(aut_nf), aps, algo);
  }

  bool
  is_stutter_invariant(tgba_digraph_ptr&& aut_f,
                       tgba_digraph_ptr&& aut_nf, bdd aps, int algo)
  {
    if (algo == 0)
      algo = default_stutter_check_algorithm();

    switch (algo)
      {
      case 1: // sl(aut_f) x sl(aut_nf)
	return product(sl(std::move(aut_f), aps),
		       sl(std::move(aut_nf), aps))->is_empty();
      case 2: // sl(cl(aut_f)) x aut_nf
	return product(sl(closure(std::move(aut_f)), aps),
		       std::move(aut_nf))->is_empty();
      case 3: // (cl(sl(aut_f)) x aut_nf
	return product(closure(sl(std::move(aut_f), aps)),
		       std::move(aut_nf))->is_empty();
      case 4: // sl2(aut_f) x sl2(aut_nf)
	return product(sl2(std::move(aut_f), aps),
		       sl2(std::move(aut_nf), aps))->is_empty();
      case 5: // sl2(cl(aut_f)) x aut_nf
	return product(sl2(closure(std::move(aut_f)), aps),
		       std::move(aut_nf))->is_empty();
      case 6: // (cl(sl2(aut_f)) x aut_nf
	return product(closure(sl2(std::move(aut_f), aps)),
		       std::move(aut_nf))->is_empty();
      case 7: // on-the-fly sl(aut_f) x sl(aut_nf)
	return product(make_tgbasl(aut_f, aps),
		       make_tgbasl(aut_nf, aps))->is_empty();
      case 8: // cl(aut_f) x cl(aut_nf)
	return product(closure(std::move(aut_f)),
		       closure(std::move(aut_nf)))->is_empty();
      default:
	throw std::runtime_error("invalid algorithm number for "
				 "is_stutter_invariant()");
	SPOT_UNREACHABLE();
      }
  }
}
