// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2011, 2012, 2013, 2014 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANta_explicitBILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more deta_explicitils.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include "misc/hash.hh"
#include <list>
#include "twa/twa.hh"
#include <set>
#include "ltlast/formula.hh"
#include <cassert>
#include "misc/bddlt.hh"
#include "taexplicit.hh"
#include "tgta.hh"

namespace spot
{

  /// Explicit representation of a spot::tgta.
  /// \ingroup ta_representation
  class SPOT_API tgta_explicit : public tgta
  {
  public:
    tgta_explicit(const const_twa_ptr& tgba,
		  unsigned n_acc,
		  state_ta_explicit* artificial_initial_state);

    // tgba interface
    virtual spot::state* get_init_state() const;

    virtual twa_succ_iterator*
    succ_iter(const spot::state* local_state) const;

    virtual bdd_dict_ptr
    get_dict() const;

    const_ta_explicit_ptr get_ta() const { return ta_; }
    ta_explicit_ptr get_ta() { return ta_; }

    virtual std::string format_state(const spot::state* s) const;

    virtual twa_succ_iterator*
    succ_iter_by_changeset(const spot::state* s, bdd change_set) const;
  protected:
    virtual bdd compute_support_conditions(const spot::state* state) const;

    ta_explicit_ptr ta_;
  };

  typedef std::shared_ptr<tgta_explicit> tgta_explicit_ptr;
  typedef std::shared_ptr<const tgta_explicit> const_tgta_explicit_ptr;

  inline tgta_explicit_ptr make_tgta_explicit(const const_twa_ptr& tgba,
					      unsigned n_acc,
					      state_ta_explicit*
					      artificial_initial_state = 0)
  {
    return std::make_shared<tgta_explicit>(tgba, n_acc,
					   artificial_initial_state);
  }
}
