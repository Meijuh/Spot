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

#include <spot/misc/common.hh>
#include <spot/twa/fwd.hh>
#include <spot/twa/bdddict.hh>

namespace spot
{
  namespace gen
  {
    enum aut_pattern_id {
      AUT_BEGIN = 256,
      /// \brief A family of co-Büchi automata.
      ///
      /// Builds a co-Büchi automaton of size 2n+1 that is
      /// good-for-games and that has no equivalent deterministic
      /// co-Büchi automaton with less than 2^n / (2n+1) states.
      ///
      /// Only defined for n>0
      ///
      /** \verbatim
          @InProceedings{   kuperberg.15.icalp,
            author        = {Denis Kuperberg and Micha{\l} Skrzypczak },
            title         = {On Determinisation of Good-for-Games Automata},
            booktitle     = {Proceedings of the 42nd International Colloquium on
                            Automata, Languages, and Programming (ICALP'15)},
            pages         = {299--310},
            year          = {2015},
            publisher     = {Springer},
            series        = {Lecture Notes in Computer Science},
            volume        = 9135,
            doi           = {10.1007/978-3-662-47666-6_24}
          }
          \endverbatim */
      AUT_KS_COBUCHI = AUT_BEGIN,
      /// \brief Hard-to-complement non-deterministic Büchi automata
      ///
      /// Build a non-deterministic Büchi automaton with 3n+1 states
      /// and whose complementary language requires an automaton with
      /// at least n! states if Streett acceptance is used.
      ///
      /// Only defined for n>0.  The automaton constructed corresponds
      /// to the right part of Fig.1 in the following paper, except
      /// that only state q_1 is initial.  (The fact that states q_2,
      /// q_3, ..., and q_n are not initial as in the paper does not
      /// change the recognized language.)
      ///
      /** \verbatim
          @InProceedings{loding.99.fstts,
            author	= {Christof L{\"o}ding},
            title	= {Optimal Bounds for Transformations of
                           $\omega$-Automata},
            booktitle	= {Proceedings of the 19th Conference on Foundations of
                           Software Technology and Theoretical Computer Science
                           (FSTTCS'99)},
            year        = 1999,
            publisher	= {Springer},
            pages       = {97--109},
            series	= {Lecture Notes in Computer Science},
            volume	= 1738,
            doi		= {10.1007/3-540-46691-6_8}
          }
          \endverbatim */
      AUT_L_NBA,
      AUT_END
    };

    /// \brief generate an automaton from a known pattern
    ///
    /// The pattern is specified using one value from the aut_pattern_id
    /// enum.  See the man page of the `genaut` binary for a
    /// description of those patterns, and bibliographic references.
    ///
    /// In case you want to combine this automaton with other
    /// automata, pass the bdd_dict to use to make sure that all share
    /// the same.
    SPOT_API twa_graph_ptr
    aut_pattern(aut_pattern_id pattern, int n,
                spot::bdd_dict_ptr dict = make_bdd_dict());

    /// \brief convert an aut_pattern_it value into a name
    ///
    /// The returned name is suitable to be used as an option
    /// key for the genaut binary.
    SPOT_API const char* aut_pattern_name(aut_pattern_id pattern);
  }
}
