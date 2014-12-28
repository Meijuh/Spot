// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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


#include "common_aoutput.hh"
#include "common_post.hh"
#include "common_cout.hh"

#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/lbtt.hh"
#include "tgbaalgos/hoa.hh"
#include "tgbaalgos/neverclaim.hh"
#include "tgbaalgos/save.hh"

automaton_format_t automaton_format = Dot;
const char* opt_dot = nullptr;
const char* hoa_opt = nullptr;
const char* opt_name = nullptr;

void
automaton_printer::print(const spot::tgba_digraph_ptr& aut,
			 // Input location for errors and statistics.
			 const char* filename,
			 // Time and input automaton for statistics
			 double time,
			 const spot::const_hoa_aut_ptr& haut)
{
  // Name the output automaton.
  if (opt_name)
    {
      name.str("");
      namer.print(haut, aut, filename, time);
      aut->set_named_prop("automaton-name", new std::string(name.str()));
    }

  // Output it.
  switch (automaton_format)
    {
    case Count:
    case Quiet:
      // Do not output anything.
      break;
    case Dot:
      spot::dotty_reachable(std::cout, aut,
			    (type == spot::postprocessor::BA)
			    || (type == spot::postprocessor::Monitor),
			    opt_dot);
      break;
    case Lbtt:
      spot::lbtt_reachable(std::cout, aut, type == spot::postprocessor::BA);
      break;
    case Lbtt_t:
      spot::lbtt_reachable(std::cout, aut, false);
      break;
    case Hoa:
      spot::hoa_reachable(std::cout, aut, hoa_opt) << '\n';
      break;
    case Spot:
      spot::tgba_save_reachable(std::cout, aut);
      break;
    case Spin:
      spot::never_claim_reachable(std::cout, aut);
      break;
    case Stats:
      statistics.print(haut, aut, filename, time) << '\n';
      break;
    }
  flush_cout();
}
