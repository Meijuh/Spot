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
#include <map>

#include "misc/bddlt.hh"
#include "twa/twagraph.hh"

namespace spot
{
  namespace node_helper
  {
    using brace_t = unsigned;
    void renumber(std::vector<brace_t>& braces,
                  const std::vector<unsigned>& decr_by);
    void truncate_braces(std::vector<brace_t>& braces,
                         const std::vector<unsigned>& rem_succ_of,
                         std::vector<size_t>& nb_braces);
  };

  class safra_state
  {
  public:
    using nodes_t = std::map<unsigned, std::vector<node_helper::brace_t>>;
    using succs_t =  std::vector<std::pair<safra_state, unsigned>>;
    bool operator<(const safra_state& other) const;
    // Printh the number of states in each brace
    safra_state(unsigned state_number, bool init_state = false);
    // Given a certain transition_label, compute all the successors of that
    // label, and return that new node.
    void compute_succs(const const_twa_graph_ptr& aut,
                          const std::vector<unsigned>& bddnums,
                          std::unordered_map<bdd,
                                             std::pair<unsigned, unsigned>,
                                             bdd_hash>& deltas,
                           succs_t& res) const;
    // The outermost brace of each node cannot be green
    void ungreenify_last_brace();
    // Used when creating the list of successors
    // A new intermediate node is created with  src's braces and with dst as id
    // A merge is done if dst already existed in *this
    void update_succ(const std::vector<node_helper::brace_t>& braces,
                     unsigned dst, const acc_cond::mark_t acc);
    // Return the emitted color, red or green
    unsigned finalize_construction();
    // A list of nodes similar to the ones of a
    // safra tree.  These are constructed in the same way as the powerset
    // algorithm.
    nodes_t nodes_;
    // A counter that indicates the nomber of states within a brace.
    // This enables us to compute the red value
    std::vector<size_t> nb_braces_;
    // A bitfield to know if a brace can emit green.
    std::vector<bool> is_green_;
    unsigned color_;
  };

  SPOT_API twa_graph_ptr
  tgba_determinisation(const const_twa_graph_ptr& aut,
                       bool bisimulation = false,
                       bool pretty_print = false,
                       bool emit_scc = false);
}
