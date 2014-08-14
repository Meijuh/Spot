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

#ifndef SPOT_SABAALGOS_SABADOTTY_HH
# define SPOT_SABAALGOS_SABADOTTY_HH

#include "misc/common.hh"
#include <iosfwd>
#include "saba/saba.hh"

namespace spot
{
  /// \ingroup saba_io
  /// \brief Print reachable states in dot format.
  SPOT_API std::ostream&
  saba_dotty_reachable(std::ostream& os,
                       const const_saba_ptr& g);
}

#endif // SPOT_SABAALGOS_SABADOTTY_HH
