// Copyright (C) 2009, 2010, 2011 Laboratoire de Recherche et D�veloppement
// de l'Epita (LRDE).
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

#ifndef SPOT_TAALGOS_MINIMIZE_HH
# define SPOT_TAALGOS_MINIMIZE_HH

# include "ta/ta.hh"
# include "ta/tgta.hh"
# include "ta/taexplicit.hh"

namespace spot
{
  /// \addtogroup ta_reduction
  /// @{


  /// \brief Construct a simplified TA by merging bisimilar states.
  ///
  /// A TA automaton can be simplified by merging bisimilar states:
  /// Two states are bisimilar if the automaton can accept the
  ///    same executions starting for either of these states. This can be
  /// achieved using any algorithm based on partition refinement
  ///
  /// For more detail about this type of algorithm, see the following paper:
  /// \verbatim
  /// @InProceedings{valmari.09.icatpn,
  /// author = {Antti Valmari},
  /// title = {Bisimilarity Minimization in in O(m logn) Time},
  /// booktitle = {Proceedings of the 30th International Conference on
  ///                the Applications and Theory of Petri Nets
  ///                (ICATPN'09)},
  /// series = {Lecture Notes in Computer Science},
  /// publisher = {Springer},
  /// isbn = {978-3-642-02423-8},
  /// pages = {123--142},
  /// volume = 5606,
  ///  url = {http://dx.doi.org/10.1007/978-3-642-02424-5_9},
  /// year = {2009}
  /// }
  /// \endverbatim
  ///
  /// \param ta_ the TA automaton to convert into a simplified TA
  ta*
  minimize_ta(const ta* ta_);



  /// \brief Construct a simplified TGTA by merging bisimilar states.
  ///
  /// A TGTA automaton can be simplified by merging bisimilar states:
  /// Two states are bisimilar if the automaton can accept the
  /// same executions starting for either of these states. This can be
  /// achieved using same algorithm used to simplify a TA taking into account
  /// the acceptance conditions of the outgoing transitions.
  ///
  /// \param tgta_ the TGTA automaton to convert into a simplified TGTA
  tgta*
  minimize_tgta(const tgta* tgta_);

/// @}
}

#endif /* !SPOT_TAALGOS_MINIMIZE_HH */