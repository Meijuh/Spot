// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2012, 2013, 2014, 2015 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
// Copyright (C) 2006 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#ifndef SPOT_LTLVISIT_CONTAIN_HH
# define SPOT_LTLVISIT_CONTAIN_HH

#include "ltlast/formula.hh"
#include "tgbaalgos/ltl2tgba_fm.hh"
#include "misc/hash.hh"
#include <map>

namespace spot
{
  namespace ltl
  {
    /// Check containment between LTL formulae.
    class SPOT_API language_containment_checker
    {
      struct record_
      {
	const_tgba_digraph_ptr translation;
	typedef std::map<const record_*, bool> incomp_map;
	incomp_map incompatible;
      };
      typedef std::unordered_map<const formula*, record_> trans_map;
    public:
      /// This class uses spot::ltl_to_tgba_fm to translate LTL
      /// formulae.  See that function for the meaning of these options.
      language_containment_checker(const bdd_dict_ptr& dict, bool exprop,
				   bool symb_merge,
				   bool branching_postponement,
				   bool fair_loop_approx);

      ~language_containment_checker();

      /// Clear the cache.
      void clear();

      /// Check whether L(l) is a subset of L(g).
      bool contained(const formula* l, const formula* g);
      /// Check whether L(!l) is a subset of L(g).
      bool neg_contained(const formula* l, const formula* g);
      /// Check whether L(l) is a subset of L(!g).
      bool contained_neg(const formula* l, const formula* g);

      /// Check whether L(l) = L(g).
      bool equal(const formula* l, const formula* g);

    protected:
      bool incompatible_(record_* l, record_* g);

      record_* register_formula_(const formula* f);

      /* Translation options */
      bdd_dict_ptr dict_;
      bool exprop_;
      bool symb_merge_;
      bool branching_postponement_;
      bool fair_loop_approx_;
      /* Translation Maps */
      trans_map translated_;
    };
  }
}

#endif // SPOT_LTLVISIT_CONTAIN_HH
