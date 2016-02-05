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

#include <spot/misc/bddlt.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/sccinfo.hh>

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
    using state_t = unsigned;
    using color_t = unsigned;
    using bdd_id_t = unsigned;
    using nodes_t = std::map<state_t, std::vector<node_helper::brace_t>>;
    using succs_t =  std::vector<std::pair<safra_state, bdd_id_t>>;
    using safra_node_t = std::pair<state_t, std::vector<node_helper::brace_t>>;

    bool operator<(const safra_state& other) const;
    // Printh the number of states in each brace
    safra_state(state_t state_number, bool init_state = false,
                bool acceptance_scc = false);
    // Given a certain transition_label, compute all the successors of that
    // label, and return that new node.
    void
    compute_succs(const const_twa_graph_ptr& aut,
                  succs_t& res,
                  const scc_info& scc,
                  const std::map<int, bdd>& implications,
                  const std::vector<bool>& is_connected,
                  std::unordered_map<bdd, unsigned, bdd_hash>& bdd2num,
                  std::vector<bdd>& all_bdds,
                  bool scc_opt,
                  bool use_bisimulation,
                  bool use_stutter) const;
    // Compute successor for transition ap
    safra_state
    compute_succ(const const_twa_graph_ptr& aut,
                 const bdd& ap,
                 const scc_info& scc,
                 const std::map<int, bdd>& implications,
                 const std::vector<bool>& is_connected,
                 bool scc_opt,
                 bool use_bisimulation) const;
   // scc_id has to be an accepting SCC.  This function tries to find a node
    // who lives in that SCC and if it does, we return the brace_id of that SCC.
    unsigned find_scc_brace_id(unsigned scc_id, const scc_info& scc);
    // The outermost brace of each node cannot be green
    void ungreenify_last_brace();
    // When a nodes a implies a node b, remove the node a.
    void merge_redundant_states(const std::map<int, bdd>& implications,
                                const scc_info& scc,
                                const std::vector<bool>& is_connected);
    // Used when creating the list of successors
    // A new intermediate node is created with  src's braces and with dst as id
    // A merge is done if dst already existed in *this
    void update_succ(const std::vector<node_helper::brace_t>& braces,
                     state_t dst, const acc_cond::mark_t acc);
    // Return the emitted color, red or green
    color_t finalize_construction();
    // A list of nodes similar to the ones of a
    // safra tree.  These are constructed in the same way as the powerset
    // algorithm.
    nodes_t nodes_;
    // A counter that indicates the nomber of states within a brace.
    // This enables us to compute the red value
    std::vector<size_t> nb_braces_;
    // A bitfield to know if a brace can emit green.
    std::vector<bool> is_green_;
    color_t color_;
  };

  SPOT_API twa_graph_ptr
  tgba_determinisation(const const_twa_graph_ptr& aut,
                       bool bisimulation = false,
                       bool pretty_print = false,
                       bool scc_opt = false,
                       bool use_bisimulation = false,
                       bool complete = false,
                       bool use_stutter = false);
}
