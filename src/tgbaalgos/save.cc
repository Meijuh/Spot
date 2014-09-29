// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2012, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE)
// Copyright (C) 2003, 2004, 2005 Laboratoire d'Informatique de Paris
// 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
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

#include <ostream>
#include "save.hh"
#include "tgba/bddprint.hh"
#include "ltlvisit/tostring.hh"
#include "ltlast/atomic_prop.hh"
#include "reachiter.hh"
#include "misc/escape.hh"

namespace spot
{
  namespace
  {
    class save_bfs: public tgba_reachable_iterator_breadth_first
    {
    public:
      save_bfs(const const_tgba_ptr& a, std::ostream& os)
	: tgba_reachable_iterator_breadth_first(a), os_(os)
      {
      }

      void
      start()
      {
	os_ << "acc = ";
	aut_->acc().format_quoted(os_, aut_->acc().all_sets())
	  << ";\n";
      }

      void
      process_state(const state* s, int, tgba_succ_iterator* si)
      {
	const bdd_dict_ptr d = aut_->get_dict();
	std::string cur = escape_str(aut_->format_state(s));
	if (si->first())
	  do
	    {
	      state* dest = si->current_state();
	      os_ << '"' << cur << "\", \"";
	      escape_str(os_, aut_->format_state(dest));
	      os_ << "\", \"";
	      escape_str(os_, bdd_format_formula(d, si->current_condition()));
	      os_ << "\",";
	      if (si->current_acceptance_conditions())
		aut_->acc().format_quoted(os_ << ' ',
					  si->current_acceptance_conditions());
	      os_ << ";\n";
	      dest->destroy();
	    }
	  while (si->next());
      }

    private:
      std::ostream& os_;
    };
  }

  std::ostream&
  tgba_save_reachable(std::ostream& os, const_tgba_ptr g)
  {
    save_bfs b(g, os);
    b.run();
    return os;
  }
}
