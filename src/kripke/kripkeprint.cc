// Copyright (C) 2011 Laboratoire de Recherche et Developpement
// de l'Epita (LRDE)
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


#include "kripkeprint.hh"
#include "kripkeexplicit.hh"
#include "../tgba/bddprint.hh"
#include "misc/escape.hh"
#include <iostream>

namespace spot
{
  KripkePrinter::KripkePrinter(const kripke* automata,
                               std::ostream& os)
    : tgba_reachable_iterator_breadth_first(automata), os_(os)
  {
  }

  void KripkePrinter::start()
  {
  }

  void KripkePrinter::process_state(const state* s,
                                    int,
                                    tgba_succ_iterator* si)
  {
    const bdd_dict* d = automata_->get_dict();
    std::string cur = automata_->format_state(s);
    os_ << "\"";
    escape_str(os_, automata_->format_state(s));
    os_ << "\", \"";
    const kripke* automata = down_cast<const kripke*>
      (automata_);
    assert(automata);
    escape_str(os_, bdd_format_formula(d,
                                       automata->state_condition(s)));

    os_ << "\",";
    for (si->first(); !si->done(); si->next())
    {
      state* dest = si->current_state();
      os_ << " \"";
      escape_str(os_, automata_->format_state(dest));
      os_ << "\"";
    }
    os_ << ";" << std::endl;
  }

} // End namespace Spot
