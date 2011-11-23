// Copyright (C) 2010, 2011 Laboratoire de Recherche et Developpement
// de l Epita_explicit (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANta_explicitBILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more deta_explicitils.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#ifndef SPOT_TA_TGBTA_HH
# define SPOT_TA_TGBTA_HH

#include "tgba/tgba.hh"

namespace spot
{
  class tgbta : public tgba
  {

  protected:
    tgbta();
  public:

    virtual
    ~tgbta();
    virtual tgba_succ_iterator*
    succ_iter_by_changeset(const spot::state* s, bdd change_set) const =0;

  };

}

#endif // SPOT_TA_TGBTA_HH
