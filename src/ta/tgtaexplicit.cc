// Copyright (C) 2010, 2011 Laboratoire de Recherche et Developpement
// de l Epita (LRDE).
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

#include "ltlast/atomic_prop.hh"
#include "ltlast/constant.hh"
#include "tgtaexplicit.hh"
#include "tgba/formula2bdd.hh"
#include "misc/bddop.hh"
#include "ltlvisit/tostring.hh"

#include "tgba/bddprint.hh"

namespace spot
{

  tgta_explicit::tgta_explicit(const tgba* tgba, bdd all_acceptance_conditions,
      state_ta_explicit* artificial_initial_state) :
    ta_explicit(tgba, all_acceptance_conditions, artificial_initial_state)
  {
  }

  state*
  tgta_explicit::get_init_state() const
  {
    return ta_explicit::get_artificial_initial_state();
  }

  tgba_succ_iterator*
  tgta_explicit::succ_iter(const spot::state* state, const spot::state*,
      const tgba*) const
  {
    return ta_explicit::succ_iter(state);
  }

  bdd
  tgta_explicit::compute_support_conditions(const spot::state* in) const
  {
    return get_tgba()->support_conditions(
        ((const state_ta_explicit*) in)->get_tgba_state());
  }

  bdd
  tgta_explicit::compute_support_variables(const spot::state* in) const
  {
    return get_tgba()->support_variables(
        ((const state_ta_explicit*) in)->get_tgba_state());
  }

  bdd_dict*
  tgta_explicit::get_dict() const
  {
    return ta_explicit::get_dict();
  }

  bdd
  tgta_explicit::all_acceptance_conditions() const
  {

    return ta_explicit::all_acceptance_conditions();
  }

  bdd
  tgta_explicit::neg_acceptance_conditions() const
  {
    return get_tgba()->neg_acceptance_conditions();
  }

  std::string
  tgta_explicit::format_state(const spot::state* s) const
  {
    return ta_explicit::format_state(s);
  }

  spot::tgba_succ_iterator*
  tgta_explicit::succ_iter_by_changeset(const spot::state* s, bdd chngset) const
  {
    return ta_explicit::succ_iter(s, chngset);
  }

}