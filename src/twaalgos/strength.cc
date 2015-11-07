// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2011, 2013, 2014, 2015 Laboratoire de Recherche
// et Développement de l'Epita (LRDE)
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

#include "strength.hh"
#include "misc/hash.hh"
#include "isweakscc.hh"
#include <deque>

namespace spot
{
  namespace
  {
    template <bool terminal>
    bool is_type_automaton(const const_twa_graph_ptr& aut, scc_info* si)
    {
      // Create an scc_info if the user did not give one to us.
      bool need_si = !si;
      if (need_si)
	si = new scc_info(aut);
      si->determine_unknown_acceptance();

      bool result = true;
      unsigned n = si->scc_count();
      for (unsigned i = 0; i < n; ++i)
	{
	  if (si->is_trivial(i))
	    continue;
	  bool first = true;
	  acc_cond::mark_t m = 0U;
	  for (auto src: si->states_of(i))
	    for (auto& t: aut->out(src))
	      if (si->scc_of(t.dst) == i)
		{
		  if (first)
		    {
		      first = false;
		      m = t.acc;
		    }
		  else if (m != t.acc)
		    {
		      result = false;
		      goto exit;
		    }
		}
	  if (terminal && si->is_accepting_scc(i) && !is_complete_scc(*si, i))
	    {
	      result = false;
	      break;
	    }
	}
    exit:
      if (need_si)
	delete si;
      return result;
    }
  }

  bool
  is_terminal_automaton(const const_twa_graph_ptr& aut, scc_info* si)
  {
    return aut->prop_terminal() || is_type_automaton<true>(aut, si);
  }

  bool
  is_weak_automaton(const const_twa_graph_ptr& aut, scc_info* si)
  {
    return aut->prop_weak() || is_type_automaton<false>(aut, si);
  }

  bool is_safety_mwdba(const const_twa_graph_ptr& aut)
  {
    if (!(aut->acc().is_buchi() || aut->acc().is_tt()))
      throw std::runtime_error
	("is_safety_mwdba() should be called on a Buchi automaton");

    for (auto& t: aut->edges())
      if (!aut->acc().accepting(t.acc))
	return false;
    return true;
  }



}
