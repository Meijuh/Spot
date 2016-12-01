// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015, 2016 Laboratoire de Recherche et
// Développement de l'Epita.
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

#include <vector>
#include <spot/twa/twagraph.hh>

namespace spot
{
  /// \brief Compute an SCC map and gather assorted information.
  ///
  /// This takes twa_graph as input and compute its SCCs.  This
  /// class maps all input states to their SCCs, and vice-versa.
  /// It allows iterating over all SCCs of the automaton, and check
  /// their acceptance or non-acceptance.
  ///
  /// Additionally this class can be used on alternating automata, but
  /// in this case, universal transitions are handled like existential
  /// transitions.  It still make sense to check which states belong
  /// to the same SCC, but the acceptance information computed by
  /// this class is meaningless.
  class SPOT_API scc_info
  {
  public:
    typedef std::vector<unsigned> scc_succs;

    class scc_node
    {
      friend class scc_info;
    protected:
      scc_succs succ_;
      acc_cond::mark_t acc_;
      std::vector<unsigned> states_; // States of the component
      bool trivial_:1;
      bool accepting_:1;        // Necessarily accepting
      bool rejecting_:1;        // Necessarily rejecting
      bool useful_:1;
    public:
      scc_node():
        acc_(0U), trivial_(true), accepting_(false),
        rejecting_(false), useful_(false)
      {
      }

      scc_node(acc_cond::mark_t acc, bool trivial):
        acc_(acc), trivial_(trivial), accepting_(false),
        rejecting_(false), useful_(false)
      {
      }

      bool is_trivial() const
      {
        return trivial_;
      }

      /// \brief True if we are sure that the SCC is accepting
      ///
      /// Note that both is_accepting() and is_rejecting() may return
      /// false if an SCC interesects a mix of Fin and Inf sets.
      bool is_accepting() const
      {
        return accepting_;
      }

      // True if we are sure that the SCC is rejecting
      ///
      /// Note that both is_accepting() and is_rejecting() may return
      /// false if an SCC interesects a mix of Fin and Inf sets.
      bool is_rejecting() const
      {
        return rejecting_;
      }

      bool is_useful() const
      {
        return useful_;
      }

      acc_cond::mark_t acc_marks() const
      {
        return acc_;
      }

      const std::vector<unsigned>& states() const
      {
        return states_;
      }

      const scc_succs& succ() const
      {
        return succ_;
      }
    };

  protected:

    std::vector<unsigned> sccof_;
    std::vector<scc_node> node_;
    const_twa_graph_ptr aut_;

    // Update the useful_ bits.  Called automatically.
    void determine_usefulness();

    const scc_node& node(unsigned scc) const
    {
      return node_[scc];
    }

  public:
    scc_info(const_twa_graph_ptr aut);

    const_twa_graph_ptr get_aut() const
    {
      return aut_;
    }

    unsigned scc_count() const
    {
      return node_.size();
    }

    bool reachable_state(unsigned st) const
    {
      return scc_of(st) != -1U;
    }

    unsigned scc_of(unsigned st) const
    {
      return sccof_[st];
    }

    auto begin() const
      SPOT_RETURN(node_.begin());
    auto end() const
      SPOT_RETURN(node_.end());
    auto cbegin() const
      SPOT_RETURN(node_.cbegin());
    auto cend() const
      SPOT_RETURN(node_.cend());
    auto rbegin() const
      SPOT_RETURN(node_.rbegin());
    auto rend() const
      SPOT_RETURN(node_.rend());

    const std::vector<unsigned>& states_of(unsigned scc) const
    {
      return node(scc).states();
    }

    unsigned one_state_of(unsigned scc) const
    {
      return states_of(scc).front();
    }

    /// \brief Get number of the SCC containing the initial state.
    unsigned initial() const
    {
      SPOT_ASSERT(scc_count() - 1 == scc_of(aut_->get_init_state_number()));
      return scc_count() - 1;
    }

    const scc_succs& succ(unsigned scc) const
    {
      return node(scc).succ();
    }

    bool is_trivial(unsigned scc) const
    {
      return node(scc).is_trivial();
    }

    acc_cond::mark_t acc(unsigned scc) const
    {
      return node(scc).acc_marks();
    }

    bool is_accepting_scc(unsigned scc) const
    {
      return node(scc).is_accepting();
    }

    bool is_rejecting_scc(unsigned scc) const
    {
      return node(scc).is_rejecting();
    }

    // Study the SCC that are currently reported neither as accepting
    // nor rejecting because of the presence of Fin sets
    void determine_unknown_acceptance();

    bool is_useful_scc(unsigned scc) const
    {
      return node(scc).is_useful();
    }

    bool is_useful_state(unsigned st) const
    {
      return reachable_state(st) && node(scc_of(st)).is_useful();
    }

    /// \brief Return the set of all used acceptance combinations, for
    /// each accepting SCC.
    std::vector<std::set<acc_cond::mark_t>> used_acc() const;

    std::set<acc_cond::mark_t> used_acc_of(unsigned scc) const;

    acc_cond::mark_t acc_sets_of(unsigned scc) const;

    std::vector<bool> weak_sccs() const;

    bdd scc_ap_support(unsigned scc) const;
  };


  /// \brief Dump the SCC graph of \a aut on \a out.
  ///
  /// If \a sccinfo is not given, it will be computed.
  SPOT_API std::ostream&
  dump_scc_info_dot(std::ostream& out,
                    const_twa_graph_ptr aut, scc_info* sccinfo = nullptr);

}
