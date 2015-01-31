// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#ifndef SPOT_TGBAALGOS_MASK_HH
# define SPOT_TGBAALGOS_MASK_HH

#include "tgba/tgbagraph.hh"

namespace spot
{
  /// \brief Clone and mask an automaton.
  ///
  /// Copy the transition of the automaton \a old, into the automaton
  /// \a cpy, creating new states at the same time.  The argument \a
  /// trans should behave as a fonction with the following prototype:
  /// <code>
  ///   void (*trans) (bdd& cond, acc_cond::mark_t& acc, unsigned dst)
  /// </code>
  /// It can modify either the condition or the acceptance sets of
  /// the transitions.  Set the condition to bddfalse to remove it
  /// (this will also remove the destination state and its descendants
  /// if they are not reachable by another transition).

  template<typename Trans>
  void transform_mask(const const_tgba_digraph_ptr& old,
		      tgba_digraph_ptr& cpy,
		      Trans trans)
  {
    std::vector<unsigned> todo;
    std::vector<unsigned> seen(old->num_states(), -1U);

    auto new_state =
      [&](unsigned old_state) -> unsigned
      {
	unsigned tmp = seen[old_state];
	if (tmp == -1U)
	  {
	    tmp = cpy->new_state();
	    seen[old_state] = tmp;
	    todo.push_back(old_state);
	  }
	return tmp;
      };

    new_state(old->get_init_state_number());
    while (!todo.empty())
      {
	unsigned old_src = todo.back();
	todo.pop_back();

	unsigned new_src = seen[old_src];
	assert(new_src != -1U);

	for (auto& t: old->out(old_src))
	  {
	    bdd cond = t.cond;
	    acc_cond::mark_t acc = t.acc;
	    trans(cond, acc, t.dst);

	    if (cond != bddfalse)
	      cpy->new_transition(new_src,
				  new_state(t.dst),
				  cond, acc);
	  }
      }
  }

  /// \brief Remove all transitions that are in some given acceptance sets.
  SPOT_API
  tgba_digraph_ptr mask_acc_sets(const const_tgba_digraph_ptr& in,
				 acc_cond::mark_t to_remove);


}


#endif // SPOT_TGBAALGOS_MASK_HH
