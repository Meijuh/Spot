// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement de
// l'Epita.
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

#include "tgbagraph.hh"
#include "ltlast/constant.hh"

namespace spot
{

  void tgba_digraph::merge_transitions()
  {
    for (auto& s: g_.states())
      {
	// Map a pair (dest state, acc) to the first transition seen
	// with such characteristic.

	typedef std::pair<graph_t::state, acc_cond::mark_t> key_t;
	std::unordered_map<key_t, graph_t::transition, pair_hash> trmap;

	auto t = g_.out_iteraser(s);
	while (t)
	  {
	    // Simply skip false transitions.
	    if (t->cond == bddfalse)
	      {
		t.erase();
		continue;
	      }

	    key_t k(t->dst, t->acc);
	    auto p = trmap.emplace(k, t.trans());
	    if (!p.second)
	      {
		// A previous transitions exists for k.  Merge the
		// condition, and schedule the transition for removal.
		g_.trans_data(p.first->second).cond |= t->cond;
		t.erase();
	      }
	    else
	      {
		++t;
	      }
	  }
      }
    g_.defrag();
  }

}
