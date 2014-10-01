// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2013, 2014 Laboratoire de Recherche et
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

#ifndef SPOT_TGBA_TGBASL_HH
# define SPOT_TGBA_TGBASL_HH

#include "tgba.hh"

namespace spot
{
  class SPOT_API tgbasl : public tgba
  {
  public:
    tgbasl(const const_tgba_ptr& a, bdd ap);

    virtual ~tgbasl();

    virtual state* get_init_state() const;

    virtual tgba_succ_iterator* succ_iter(const state* state) const;

    virtual std::string format_state(const state* state) const;

  protected:
    virtual bdd compute_support_conditions(const state* state) const;

  private:
    const_tgba_ptr a_;
    bdd aps_;
  };
}

#endif
