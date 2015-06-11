// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014, 2015 Laboratoire de Recherche et
// Developpement de l'Epita (LRDE).
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

#include "cycles.hh"
#include "ltlast/formula.hh"
#include "isweakscc.hh"

namespace spot
{
  namespace
  {
    // Look for a non-accepting cycle.
    class weak_checker final : public enumerate_cycles
    {
    public:
      bool result;

      weak_checker(const scc_info& map)
	: enumerate_cycles(map), result(true)
      {
      }

      virtual bool
      cycle_found(unsigned start) override
      {
	dfs_stack::const_reverse_iterator i = dfs_.rbegin();
	acc_cond::mark_t acc = 0U;
	for (;;)
	  {
	    acc |= aut_->edge_storage(i->succ).acc;
	    if (i->s == start)
	      break;
	    ++i;
	    // The const cast is here to please old g++ versions.
	    // At least version 4.0 needs it.
	    assert(i != const_cast<const dfs_stack&>(dfs_).rend());
	  }
	if (!aut_->acc().accepting(acc))
	  {
	    // We have found an non-accepting cycle, so the SCC is not
	    // weak.
	    result = false;
	    return false;
	  }
	return true;
      }

    };
  }

  bool
  is_inherently_weak_scc(scc_info& map, unsigned scc)
  {
     // Weak SCCs are inherently weak.
    if (is_weak_scc(map, scc))
      return true;
    // If the SCC is accepting, but one cycle is not, the SCC is not
    // weak.
    weak_checker w(map);
    w.run(scc);
    return w.result;
  }

  bool
  is_weak_scc(scc_info& map, unsigned scc)
  {
    // Rejecting SCCs are weak.
    if (map.is_rejecting_scc(scc))
      return true;
    // If all transitions use the same acceptance set, the SCC is weak.
    return map.used_acc_of(scc).size() == 1;
  }

  bool
  is_complete_scc(scc_info& map, unsigned scc)
  {
    auto a = map.get_aut();
    for (auto s: map.states_of(scc))
      {
	bool has_succ = false;
	bdd sumall = bddfalse;
	for (auto& t: a->out(s))
	  {
	    has_succ = true;
	    if (map.scc_of(t.dst) == scc)
	      sumall |= t.cond;
	    if (sumall == bddtrue)
	      break;
	  }
	if (!has_succ || sumall != bddtrue)
	  return false;
      }
    return true;
  }

  bool
  is_terminal_scc(scc_info& map, unsigned scc)
  {
    // If all transitions use all acceptance conditions, the SCC is weak.
    return (map.is_accepting_scc(scc)
	    && map.used_acc_of(scc).size() == 1
	    && is_complete_scc(map, scc));
  }
}
