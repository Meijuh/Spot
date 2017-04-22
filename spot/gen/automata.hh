// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Developpement de
// l'EPITA (LRDE).
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

#include <spot/twa/twagraph.hh>

namespace spot
{
  namespace gen
  {
    /// \brief A family of co-Büchi automata.
    ///
    /// ks_cobuchi(n) is a co-Büchi automaton of size 2n+1 that is
    /// good-for-games and that has no equivalent deterministic co-Büchi
    /// automaton with less than 2^n / (2n+1) states.
    /// For details and other classes, see:
    ///
    /// @InProceedings{kuperberg2015determinisation,
    ///     author={Kuperberg, Denis and Skrzypczak, Micha{\l}},
    ///     title={On Determinisation of Good-for-Games Automata},
    ///     booktitle={International Colloquium on Automata, Languages, and
    ///                Programming},
    ///     pages={299--310},
    ///     year={2015},
    ///     organization={Springer}
    /// }
    ///
    /// \pre n>0
    SPOT_API twa_graph_ptr
    ks_cobuchi(unsigned n);
  }
}
