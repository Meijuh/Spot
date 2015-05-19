// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement
// de l'Epita.
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

#include <set>

#include "misc/bddlt.hh"
#include "twa/twagraph.hh"

namespace spot
{
  class safra_state
  {
    class node
    {
    public:
      using brace_t = size_t;

      bool operator==(const node& other) const;
      bool operator<(const node& other) const;
      void disable_construction() { in_construction_ = false; }
      void truncate_braces(const std::vector<unsigned>& rem_succ_of,
                           std::vector<size_t>& nb_braces);
      void renumber(const std::vector<unsigned>& decr_by);
      node(unsigned id)
        : id_(id), in_construction_(true) {}
      node(unsigned id, brace_t b_id, bool in_construction = true)
        : id_(id), braces_(1, b_id), in_construction_(in_construction) {}
      node(unsigned id, std::vector<brace_t> b, bool in_construction = true)
        : id_(id), braces_(b), in_construction_(in_construction) {}
      // The name used to identify a state
      unsigned id_;
      // The list of braces the state is nested in.
      std::vector<brace_t> braces_;
      // Hack to have two comparision functions during construction and after
      // construction
      // During construction only the nodes id matterns as the braces are under
      // construction. After construction (id, braces) is what distinguishes a
      // node.
      bool in_construction_;
    };

  public:
    typedef std::vector<std::pair<safra_state, bdd>> succs_t;
    bool operator<(const safra_state& other) const;
    // Print each sub-state with their associated braces of a safra state
    void print_debug(unsigned state_id);
    safra_state(unsigned state_number, bool init_state = false);
    // Given a certain transition_label, compute all the successors of that
    // label, and return that new node.
    succs_t compute_succs(const const_twa_graph_ptr& aut) const;
    // Used when creating the list of successors
    // A new intermediate node is created with  src's braces and with dst as id
    // A merge is done if dst already existed in *this
    void update_succ(const node& src, unsigned dst, const acc_cond::mark_t acc);
    // Return the emitted color, red or green
    unsigned finalize_construction();
    // A list of nodes similar to the ones of a
    // safra tree.  These are constructed in the same way as the powerset
    // algorithm.
    std::set<node> nodes_;
    // A counter that indicates the nomber of states within a brace.
    // This enables us to compute the red value
    std::vector<size_t> nb_braces_;
    // A bitfield to know if a brace can emit green.
    std::vector<bool> is_green_;
    unsigned color_;
  };

  SPOT_API twa_graph_ptr
  tgba_determinisation(const const_twa_graph_ptr& aut);
}
