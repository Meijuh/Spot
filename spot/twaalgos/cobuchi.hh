// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include <spot/misc/bitvect.hh>
#include <spot/twa/fwd.hh>

#include <vector>

namespace spot
{
  /// A vector of nca_st_info is given as argument to nsa_to_nca() or
  /// dnf_to_nca(). Each nca_st_info has information about a state that must be
  /// seen infinitely often.
  /// For a state 's' visited infinitely often by a run, the information
  /// provided is:
  ///  - the clause number satisfied by the run (from left to right)
  ///  - the state number of 's'
  ///  - destinations of all outgoing edges of 's' (represented as a bitvect)
  struct nca_st_info
  {
    unsigned clause_num;
    unsigned state_num;
    bitvect* all_dst;

    nca_st_info(unsigned clause, unsigned st, bitvect* dst)
    {
      clause_num = clause;
      state_num = st;
      all_dst = dst;
    }

    ~nca_st_info()
    {
      delete all_dst;
    }
  };

  typedef std::vector<struct nca_st_info*> vect_nca_info;

  /// \brief Converts a nondet Streett-like aut. to a nondet. co-Büchi aut.
  ///
  /// This function works in top of the augmented subset construction algorithm
  /// and is described in section 3.1 of:
  /** \verbatim
      @Article{boker.2009.lcs,
        author    = {Udi Boker and Orna Kupferman},
        title     = {Co-Büching Them All},
        booktitle = {Foundations of Software Science and Computational
                     Structures - 14th International Conference, FOSSACS 2011}
        year      = {2011},
        pages     = {184--198},
        url       = {\url{www.cs.huji.ac.il/~ornak/publications/fossacs11b.pdf}}
      }
      \endverbatim */
  /// This implementation is quite different from the described algorithm. It
  /// is made to work with automaton with Street-like acceptance (including
  /// Büchi).
  ///
  /// \a aut The automaton to convert.
  /// \a named_states name each state for easier debugging.
  /// \a nca_info retrieve information about state visited infinitely often.
  SPOT_API twa_graph_ptr
  nsa_to_nca(const const_twa_graph_ptr& aut,
             bool named_states = false,
             vect_nca_info* nca_info = nullptr);

  /// \brief Converts an aut. with acceptance in DNF to a nondet. co-Büchi aut.
  ///
  /// This function converts the Rabin-like automaton into a Strett-like
  /// automaton and then calls nsa_to_nca() on it. It is described in section
  /// 3.2 of:
  /** \verbatim
      @Article{boker.2009.lcs,
        author    = {Udi Boker and Orna Kupferman},
        title     = {Co-Büching Them All},
        booktitle = {Foundations of Software Science and Computational
                     Structures - 14th International Conference, FOSSACS 2011}
        year      = {2011},
        pages     = {184--198},
        url       = {\url{www.cs.huji.ac.il/~ornak/publications/fossacs11b.pdf}}
      }
      \endverbatim */
  ///
  /// \a aut The automaton to convert.
  /// \a named_states name each state for easier debugging.
  /// \a nca_info retrieve information about state visited infinitely often.
  SPOT_API twa_graph_ptr
  dnf_to_nca(const const_twa_graph_ptr& aut,
             bool named_states = false,
             vect_nca_info* nca_info = nullptr);

  /// \brief Converts any ω-automata to det. co-buchi (when possible)
  ///
  /// The resulting automaton will always recognize at least the same language.
  /// Actually, it can recognize more if the original language can not be
  /// expressed using a co-Büchi acceptance condition.
  SPOT_API twa_graph_ptr
  to_dca(const const_twa_graph_ptr& aut, bool named_states = false);
}
