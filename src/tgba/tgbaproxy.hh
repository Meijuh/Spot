// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et
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

#pragma once

#include "tgba.hh"

namespace spot
{
  /// \ingroup twa_on_the_fly_algorithms
  /// \brief A TGBA proxy.
  ///
  /// This implements a simple proxy to an existing
  /// TGBA, forwarding all methods to the original.
  /// By itself this class is pointless: better use the
  /// original automaton right away.  However it is useful
  /// to inherit from this class and override some of its
  /// methods to implement some on-the-fly algorithm.
  class SPOT_API twa_proxy: public twa
  {
  protected:
    twa_proxy(const const_twa_ptr& original);

  public:
    virtual ~twa_proxy();

    virtual state* get_init_state() const;

    virtual twa_succ_iterator*
    succ_iter(const state* state) const;

    virtual std::string format_state(const state* state) const;

    virtual std::string
    transition_annotation(const twa_succ_iterator* t) const;

    virtual state* project_state(const state* s, const const_twa_ptr& t) const;

  protected:
    virtual bdd compute_support_conditions(const state* state) const;
    const_twa_ptr original_;
  };
}
