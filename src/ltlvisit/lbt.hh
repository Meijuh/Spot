// -*- coding: utf-8 -*-
// Copyright (C) 2012 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#ifndef SPOT_LTLVISIT_LBT_HH
# define SPOT_LTLVISIT_LBT_HH

#include <ltlast/formula.hh>
#include <iosfwd>

namespace spot
{
  namespace ltl
  {
    /// \addtogroup ltl_io
    /// @{

    /// \brief Output an LTL formula as a string in LBT's format.
    ///
    /// The formula must be an LTL formula (ELTL and PSL operators
    /// are not supported).  The M and W operator will be output
    /// as-is, because this is accepted by LBTT, however if you
    /// plan to use the output with other tools, you should probably
    /// rewrite these two operators using unabbreviate_wm().
    ///
    /// \param f The formula to translate.
    /// \param os The stream where it should be output.
    std::ostream&
    to_lbt_string(const formula* f, std::ostream& os);
    /// @}
  }
}

#endif // SPOT_LTLVISIT_TOSTRING_HH