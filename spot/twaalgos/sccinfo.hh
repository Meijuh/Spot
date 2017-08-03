// -*- coding: utf-8 -*-
// Copyright (C) 2014-2017 Laboratoire de Recherche et Développement
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

#include <vector>
#include <spot/twa/twagraph.hh>

namespace spot
{
  class scc_info;

  namespace internal
  {
    struct keep_all
    {
      template <typename Iterator>
      bool operator()(Iterator, Iterator) const noexcept
      {
        return true;
      }
    };

    // Keep only transitions that have at least one destination in the
    // current SCC.
    struct keep_inner_scc
    {
    private:
      const std::vector<unsigned>& sccof_;
      unsigned desired_scc_;
    public:
      keep_inner_scc(const std::vector<unsigned>& sccof, unsigned desired_scc)
        : sccof_(sccof), desired_scc_(desired_scc)
      {
      }

      template <typename Iterator>
      bool operator()(Iterator begin, Iterator end) const noexcept
      {
        bool want = false;
        while (begin != end)
          if (sccof_[*begin++] == desired_scc_)
            {
              want = true;
              break;
            }
        return want;
      }
    };

    template <typename Graph, typename Filter>
    class SPOT_API scc_edge_iterator
    {
    public:
      typedef typename std::conditional<std::is_const<Graph>::value,
                                        const typename Graph::edge_storage_t,
                                        typename Graph::edge_storage_t>::type
        value_type;
      typedef value_type& reference;
      typedef value_type* pointer;
      typedef std::ptrdiff_t difference_type;
      typedef std::forward_iterator_tag iterator_category;

      typedef std::vector<unsigned>::const_iterator state_iterator;

      typedef typename std::conditional<std::is_const<Graph>::value,
                                        const typename Graph::edge_vector_t,
                                        typename Graph::edge_vector_t>::type
        tv_t;

      typedef typename std::conditional<std::is_const<Graph>::value,
                                        const typename Graph::state_vector,
                                        typename Graph::state_vector>::type
        sv_t;
      typedef const typename Graph::dests_vector_t dv_t;
    protected:

      state_iterator pos_;
      state_iterator end_;
      unsigned t_;
      tv_t* tv_;
      sv_t* sv_;
      dv_t* dv_;

      Filter filt_;

      void inc_state_maybe_()
      {
        while (!t_ && (++pos_ != end_))
          t_ = (*sv_)[*pos_].succ;
      }

      void inc_()
      {
        t_ = (*tv_)[t_].next_succ;
        inc_state_maybe_();
      }

      bool ignore_current()
      {
        unsigned dst = (*this)->dst;
        if ((int)dst >= 0)
          // Non-universal branching => a single destination.
          return !filt_(&(*this)->dst, 1 + &(*this)->dst);
        // Universal branching => multiple destinations.
        const unsigned* d = dv_->data() + ~dst;
        return !filt_(d + 1, d + *d + 1);
      }

    public:
      scc_edge_iterator(state_iterator begin, state_iterator end,
                        tv_t* tv, sv_t* sv, dv_t* dv, Filter filt) noexcept
        : pos_(begin), end_(end), t_(0), tv_(tv), sv_(sv), dv_(dv), filt_(filt)
      {
        if (pos_ == end_)
          return;

        t_ = (*sv_)[*pos_].succ;
        inc_state_maybe_();
        while (pos_ != end_ && ignore_current())
          inc_();
      }

      scc_edge_iterator& operator++()
      {
        do
          inc_();
        while (pos_ != end_ && ignore_current());
        return *this;
      }

      scc_edge_iterator operator++(int)
      {
        scc_edge_iterator old = *this;
        ++*this;
        return old;
      }

      bool operator==(scc_edge_iterator o) const
      {
        return pos_ == o.pos_ && t_ == o.t_;
      }

      bool operator!=(scc_edge_iterator o) const
      {
        return pos_ != o.pos_ || t_ != o.t_;
      }

      reference operator*() const
      {
        return (*tv_)[t_];
      }

      pointer operator->() const
      {
        return &**this;
      }
    };


    template <typename Graph, typename Filter>
    class SPOT_API scc_edges
    {
    public:
      typedef scc_edge_iterator<Graph, Filter> iter_t;
      typedef typename iter_t::tv_t tv_t;
      typedef typename iter_t::sv_t sv_t;
      typedef typename iter_t::dv_t dv_t;
      typedef typename iter_t::state_iterator state_iterator;
    private:
      state_iterator begin_;
      state_iterator end_;
      tv_t* tv_;
      sv_t* sv_;
      dv_t* dv_;
      Filter filt_;
    public:

      scc_edges(state_iterator begin, state_iterator end,
                tv_t* tv, sv_t* sv, dv_t* dv, Filter filt) noexcept
        : begin_(begin), end_(end), tv_(tv), sv_(sv), dv_(dv), filt_(filt)
      {
      }

      iter_t begin() const
      {
        return {begin_, end_, tv_, sv_, dv_, filt_};
      }

      iter_t end() const
      {
        return {end_, end_, nullptr, nullptr, nullptr, filt_};
      }
    };
  }


  /// Storage for SCC related information.
  class SPOT_API scc_info_node
  {
  public:
    typedef std::vector<unsigned> scc_succs;
    friend class scc_info;
  protected:
    scc_succs succ_;
    acc_cond::mark_t acc_;
    acc_cond::mark_t common_;
    std::vector<unsigned> states_; // States of the component
    bool trivial_:1;
    bool accepting_:1;        // Necessarily accepting
    bool rejecting_:1;        // Necessarily rejecting
    bool useful_:1;
  public:
    scc_info_node():
      acc_(0U), trivial_(true), accepting_(false),
      rejecting_(false), useful_(false)
    {
    }

    scc_info_node(acc_cond::mark_t acc,
                  acc_cond::mark_t common, bool trivial):
      acc_(acc), common_(common),
      trivial_(trivial), accepting_(false),
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

    acc_cond::mark_t common_marks() const
    {
      return common_;
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
    // scc_node used to be an inner class, but Swig 3.0.10 does not
    // support that yet.
    typedef scc_info_node scc_node;
    typedef scc_info_node::scc_succs scc_succs;
    /// @{
    /// \brief An edge_filter may be called on each edge to decide what
    /// to do with it.
    ///
    /// The edge filter is called with an edge and a destination.  (In
    /// existential automata the destination is already given by the
    /// edge, but in alternating automata, one edge may have several
    /// destinations, and in this case the filter will be called for
    /// each destination.)  The filter should return a value from
    /// edge_filter_choice.
    ///
    /// \c keep means to use the edge normally, as if no filter had
    /// been given.  \c ignore means to pretend the edge does not
    /// exist (if the destination is only reachable through this edge,
    /// it will not be visited). \c cut also ignores the edge, but
    /// it remembers to visit the destination state (as if it were an
    /// initial state) in case it is not reachable otherwise.
    ///
    /// Note that successors between SCCs can only be maintained for
    /// edges that are kept.  If some edges are ignored or cut, the
    /// SCC graph that you can explore with scc_info::initial() and
    /// scc_info::succ() will be restricted to the portion reachable
    /// with "keep" edges.  Additionally SCCs might be created when
    /// edges are cut, but those will not be reachable from
    /// scc_info::initial()..
    enum class edge_filter_choice { keep, ignore, cut };
    typedef edge_filter_choice
      (*edge_filter)(const twa_graph::edge_storage_t& e, unsigned dst,
                     void* filter_data);
    /// @}

  protected:

    std::vector<unsigned> sccof_;
    std::vector<scc_node> node_;
    const_twa_graph_ptr aut_;
    unsigned initial_state_;
    edge_filter filter_;
    void* filter_data_;

    // Update the useful_ bits.  Called automatically.
    void determine_usefulness();

    const scc_node& node(unsigned scc) const
    {
      return node_[scc];
    }

  public:

    // Use ~0U instead of -1U to work around a bug in Swig.
    // See https://github.com/swig/swig/issues/993
    scc_info(const_twa_graph_ptr aut,
             unsigned initial_state = ~0U,
             edge_filter filter = nullptr,
             void* filter_data = nullptr);

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

    std::vector<scc_node>::const_iterator begin() const
    {
      return node_.begin();
    }

    std::vector<scc_node>::const_iterator end() const
    {
      return node_.end();
    }

    std::vector<scc_node>::const_iterator cbegin() const
    {
      return node_.cbegin();
    }

    std::vector<scc_node>::const_iterator cend() const
    {
      return node_.cend();
    }

    std::vector<scc_node>::const_reverse_iterator rbegin() const
    {
      return node_.rbegin();
    }

    std::vector<scc_node>::const_reverse_iterator rend() const
    {
      return node_.rend();
    }

    const std::vector<unsigned>& states_of(unsigned scc) const
    {
      return node(scc).states();
    }

    /// \brief A fake container to iterate over all edges leaving any
    /// state of an SCC.
    ///
    /// The difference with inner_edges_of() is that edges_of() include
    /// outgoing edges from all the states, even if they leave the SCC.
    internal::scc_edges<const twa_graph::graph_t, internal::keep_all>
    edges_of(unsigned scc) const
    {
      auto& states = states_of(scc);
      return {states.begin(), states.end(),
              &aut_->edge_vector(), &aut_->states(),
              &aut_->get_graph().dests_vector(),
              internal::keep_all()};
    }

    /// \brief A fake container to iterate over all edges between
    /// states of an SCC.
    ///
    /// The difference with edges_of() is that inner_edges_of()
    /// ignores edges leaving the SCC are ignored.  In the case of
    /// alternating automaton, an edge is considered to be part of the
    /// SCC of one of its destination is in the SCC.
    internal::scc_edges<const twa_graph::graph_t, internal::keep_inner_scc>
    inner_edges_of(unsigned scc) const
    {
      auto& states = states_of(scc);
      return {states.begin(), states.end(),
              &aut_->edge_vector(), &aut_->states(),
              &aut_->get_graph().dests_vector(),
              internal::keep_inner_scc(sccof_, scc)};
    }

    unsigned one_state_of(unsigned scc) const
    {
      return states_of(scc).front();
    }

    /// \brief Get number of the SCC containing the initial state.
    unsigned initial() const
    {
      SPOT_ASSERT(filter_ || scc_count() - 1 == scc_of(initial_state_));
      return scc_of(initial_state_);
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

    /// sets that contain at least one transition of the SCC
    acc_cond::mark_t acc_sets_of(unsigned scc) const
    {
      // FIXME: Why do we have two name for this method?
      return acc(scc);
    }

    /// sets that contain the entire SCC
    acc_cond::mark_t common_sets_of(unsigned scc) const
    {
      return node(scc).common_marks();
    }

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
