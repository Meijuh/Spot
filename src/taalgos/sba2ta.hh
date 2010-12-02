// Copyright (C) 2010 Laboratoire de Recherche et Developpement
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

#ifndef SPOT_TGBAALGOS_SBA2TA_HH
# define SPOT_TGBAALGOS_SBA2TA_HH

#include "misc/hash.hh"
#include <list>
#include <map>
#include <set>
#include "tgba/tgbatba.hh"
#include "ltlast/formula.hh"
#include <cassert>
#include "misc/bddlt.hh"
#include "ta/taexplicit.hh"


namespace spot
{
  ta* sba_to_ta(const tgba_sba_proxy* tgba_to_convert, bdd atomic_propositions_set);


  void compute_livelock_acceptance_states(ta_explicit* testing_automata);

}

#endif // SPOT_TGBAALGOS_SBA2TA_HH
