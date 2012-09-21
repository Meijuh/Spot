// Copyright (C) 2012 Laboratoire de Recherche et Developpement de
// l'Epita (LRDE).
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

#ifndef SPOT_TGBAALGOS_ISWEAKSCC_HH
# define SPOT_TGBAALGOS_ISWEAKSCC_HH

#include "scc.hh"

namespace spot
{
  /// \addtogroup tgba_misc
  /// @{

  /// \brief Whether the SCC number \a scc in \a map is weak.
  ///
  /// An SCC is weak if either its cycles are all accepting, or they
  /// are all non-accepting.
  ///
  /// The scc_map \a map should have been built already.  The absence
  /// of accepting cycle is easy to check (the scc_map can tell
  /// whether the SCC is non-accepting already).  For the accepting
  /// SCCs, this function enumerates all cycles in the given SCC (it
  /// stops if it find a non-accepting cycle).
  bool is_weak_scc(scc_map& map, unsigned scc);

  /// @}
}


#endif // SPOT_TGBAALGOS_ISWEAKSCC_HH
