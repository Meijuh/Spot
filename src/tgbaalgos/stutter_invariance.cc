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
  bool
  is_stutter_invariant(const ltl::formula* f)
    {
      const char* stutter_check = getenv("SPOT_STUTTER_CHECK");
      char algo = stutter_check ? stutter_check[0] : '1';
      if (f->is_ltl_formula() && f->is_X_free())
        return true;

      if (algo == '0')
        {
          // Syntactic checking.
          if (f->is_ltl_formula())
            {
              const ltl::formula* g = remove_x(f);
              ltl::ltl_simplifier ls;
              bool res = ls.are_equivalent(f, g);
              g->destroy();
              return res;
            }
          else
            {
              throw std::runtime_error("Cannot use the syntactic-based " \
                                       "approach to stutter-invariance " \
                                       "checking on non-ltl formula");
            }
        }
      const ltl::formula* nf = ltl::unop::instance(ltl::unop::Not, f->clone());
      translator trans;
      tgba_digraph_ptr aut_f = trans.run(f);
      tgba_digraph_ptr aut_nf = trans.run(nf);
      bdd aps = atomic_prop_collect_as_bdd(f, aut_f);
      nf->destroy();
      return is_stutter_invariant(std::move(aut_f), std::move(aut_nf), aps);
    }

  bool
  is_stutter_invariant(tgba_digraph_ptr&& aut_f,
                       tgba_digraph_ptr&& aut_nf, bdd aps)
    {
      const char* stutter_check = getenv("SPOT_STUTTER_CHECK");
      char algo = stutter_check ? stutter_check[0] : '8';

      switch (algo)
        {
          // sl(aut_f) x sl(aut_nf)
        case '1':
            {
              return product(sl(std::move(aut_f), aps),
                             sl(std::move(aut_nf), aps))->is_empty();
            }
          // sl(cl(aut_f)) x aut_nf
        case '2':
            {
              return product(sl(closure(std::move(aut_f)), aps),
                             std::move(aut_nf))->is_empty();
            }
          // (cl(sl(aut_f)) x aut_nf
        case '3':
            {
              return product(closure(sl(std::move(aut_f), aps)),
                             std::move(aut_nf))->is_empty();
            }
          // sl2(aut_f) x sl2(aut_nf)
        case '4':
            {
              return product(sl2(std::move(aut_f), aps),
                             sl2(std::move(aut_nf), aps))->is_empty();
            }
          // sl2(cl(aut_f)) x aut_nf
        case '5':
            {
              return product(sl2(closure(std::move(aut_f)), aps),
                             std::move(aut_nf))->is_empty();
            }
          // (cl(sl2(aut_f)) x aut_nf
        case '6':
            {
              return product(closure(sl2(std::move(aut_f), aps)),
                             std::move(aut_nf))->is_empty();
            }
          // on-the-fly sl(aut_f) x sl(aut_nf)
        case '7':
            {
              auto slf = std::make_shared<tgbasl>(aut_f, aps);
              auto slnf = std::make_shared<tgbasl>(aut_nf, aps);
              return product(slf, slnf)->is_empty();
            }
          // cl(aut_f) x cl(aut_nf)
        case '8':
            {
              return product(closure(std::move(aut_f)),
                             closure(std::move(aut_nf)))->is_empty();
            }
        default:
          throw std::runtime_error("invalid value for SPOT_STUTTER_CHECK.");
          break;
        }
    }
}
