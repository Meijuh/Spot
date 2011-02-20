// Copyright (C) 2009, 2010, 2011 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
// Copyright (C) 2003, 2005 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include "formula.hh"
#include "misc/hash.hh"
#include <iostream>

namespace spot
{
  namespace ltl
  {
    size_t formula::max_count = 0;

    formula*
    formula::clone() const
    {
      const_cast<formula*>(this)->ref_();
      return const_cast<formula*>(this);
    }

    formula::~formula()
    {
    }

    void
    formula::destroy() const
    {
      if (const_cast<formula*>(this)->unref_())
	delete this;
    }

    void
    formula::ref_()
    {
      // Not reference counted by default.
    }

    bool
    formula::unref_()
    {
      // Not reference counted by default.
      return false;
    }

    std::ostream&
    print_formula_props(std::ostream& out, const formula* f, bool abbr)
    {
      const char* comma = abbr ? "" : ", ";
      const char* sep = "";

#define proprint(m, a, l)			\
      if (f->m())				\
	{					\
	  out << sep; out << (abbr ? a : l);	\
	  sep = comma;				\
	}

      proprint(is_boolean, "B", "Boolean formula");
      proprint(is_sugar_free_boolean, "&", "without Boolean sugar");
      proprint(is_in_nenoform, "!", "in negative normal form");
      proprint(is_X_free, "x", "without X operator");
      proprint(is_sugar_free_ltl, "f", "without LTL sugar");
      proprint(is_ltl_formula, "L", "LTL formula");
      proprint(is_eltl_formula, "E", "ELTL formula");
      proprint(is_psl_formula, "P", "PSL formula");
      proprint(is_sere_formula, "S", "SERE formula");
      proprint(is_eventual, "e", "pure eventuality");
      proprint(is_universal, "u", "purely universal");
      proprint(is_marked, "+", "marked");
      proprint(accepts_eword, "0", "accepts the empty word");
      return out;
    }
  }
}
