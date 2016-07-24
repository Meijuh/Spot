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

#include <spot/misc/common.hh>
#include <vector>
#include <type_traits>
#include <tuple>
#include <cassert>
#include <iterator>
#include <algorithm>
#include <iostream>
#include <type_traits>

namespace spot
{
  template <typename State_Data, typename Edge_Data, bool Alternating = false>
  class SPOT_API digraph;

  namespace internal
  {
#ifndef SWIG
    template <typename Of, typename ...Args>
    struct first_is_base_of
    {
      static const bool value = false;
    };

    template <typename Of, typename Arg1, typename ...Args>
    struct first_is_base_of<Of, Arg1, Args...>
    {
      static const bool value =
        std::is_base_of<Of, typename std::decay<Arg1>::type>::value;
    };
#endif

    // The boxed_label class stores Data as an attribute called
    // "label" if boxed is true.  It is an empty class if Data is
    // void, and it simply inherits from Data if boxed is false.
    //
    // The data() method offers an homogeneous access to the Data
    // instance.
    template <typename Data, bool boxed = !std::is_class<Data>::value>
    struct SPOT_API boxed_label
    {
      typedef Data data_t;
      Data label;

#ifndef SWIG
      template <typename... Args,
                typename = typename std::enable_if<
                  !first_is_base_of<boxed_label, Args...>::value>::type>
        boxed_label(Args&&... args)
        noexcept(std::is_nothrow_constructible<Data, Args...>::value)
        : label{std::forward<Args>(args)...}
      {
      }
#endif

      // if Data is a POD type, G++ 4.8.2 wants default values for all
      // label fields unless we define this default constructor here.
      explicit boxed_label()
        noexcept(std::is_nothrow_constructible<Data>::value)
      {
      }

      Data& data()
      {
        return label;
      }

      const Data& data() const
      {
        return label;
      }

      bool operator<(const boxed_label& other) const
      {
        return label < other.label;
      }
    };

    template <>
    struct SPOT_API boxed_label<void, true>: public std::tuple<>
    {
      typedef std::tuple<> data_t;
      std::tuple<>& data()
      {
        return *this;
      }

      const std::tuple<>& data() const
      {
        return *this;
      }

    };

    template <typename Data>
    struct SPOT_API boxed_label<Data, false>: public Data
    {
      typedef Data data_t;

#ifndef SWIG
      template <typename... Args,
                typename = typename std::enable_if<
                  !first_is_base_of<boxed_label, Args...>::value>::type>
        boxed_label(Args&&... args)
        noexcept(std::is_nothrow_constructible<Data, Args...>::value)
        : Data{std::forward<Args>(args)...}
      {
      }
#endif

      // if Data is a POD type, G++ 4.8.2 wants default values for all
      // label fields unless we define this default constructor here.
      explicit boxed_label()
        noexcept(std::is_nothrow_constructible<Data>::value)
      {
      }

      Data& data()
      {
        return *this;
      }

      const Data& data() const
      {
        return *this;
      }
    };

    //////////////////////////////////////////////////
    // State storage for digraphs
    //////////////////////////////////////////////////

    // We have two implementations, one with attached State_Data, and
    // one without.

    template <typename Edge, typename State_Data>
    struct SPOT_API distate_storage final: public State_Data
    {
      Edge succ = 0; // First outgoing edge (used when iterating)
      Edge succ_tail = 0;        // Last outgoing edge (used for
                                // appending new edges)
#ifndef SWIG
      template <typename... Args,
                typename = typename std::enable_if<
                  !first_is_base_of<distate_storage, Args...>::value>::type>
      distate_storage(Args&&... args)
        noexcept(std::is_nothrow_constructible<State_Data, Args...>::value)
        : State_Data{std::forward<Args>(args)...}
      {
      }
#endif
    };

    //////////////////////////////////////////////////
    // Edge storage
    //////////////////////////////////////////////////

    // Again two implementation: one with label, and one without.

    template <typename StateIn,
              typename StateOut, typename Edge, typename Edge_Data>
    struct SPOT_API edge_storage final: public Edge_Data
    {
      typedef Edge edge;

      StateOut dst;                // destination
      Edge next_succ;        // next outgoing edge with same
                                // source, or 0
      StateIn src;                // source

      explicit edge_storage()
        noexcept(std::is_nothrow_constructible<Edge_Data>::value)
        : Edge_Data{}
      {
      }

#ifndef SWIG
      template <typename... Args>
      edge_storage(StateOut dst, Edge next_succ,
                    StateIn src, Args&&... args)
        noexcept(std::is_nothrow_constructible<Edge_Data, Args...>::value
                 && std::is_nothrow_constructible<StateOut, StateOut>::value
                 && std::is_nothrow_constructible<Edge, Edge>::value)
        : Edge_Data{std::forward<Args>(args)...},
        dst(dst), next_succ(next_succ), src(src)
      {
      }
#endif

      bool operator<(const edge_storage& other) const
      {
        if (src < other.src)
          return true;
        if (src > other.src)
          return false;
        // This might be costly if the destination is a vector
        if (dst < other.dst)
          return true;
        if (dst > other.dst)
          return false;
        return this->data() < other.data();
      }

      bool operator==(const edge_storage& other) const
      {
        return src == other.src &&
          dst == other.dst &&
          this->data() == other.data();
      }
    };

    //////////////////////////////////////////////////
    // Edge iterator
    //////////////////////////////////////////////////

    // This holds a graph and a edge number that is the start of
    // a list, and it iterates over all the edge_storage_t elements
    // of that list.

    template <typename Graph>
    class SPOT_API edge_iterator: public
    std::iterator<std::forward_iterator_tag,
                  typename
                  std::conditional<std::is_const<Graph>::value,
                                   const typename Graph::edge_storage_t,
                                   typename Graph::edge_storage_t>::type>
    {
      typedef
        std::iterator<std::forward_iterator_tag,
                      typename
                      std::conditional<std::is_const<Graph>::value,
                                       const typename Graph::edge_storage_t,
                                       typename Graph::edge_storage_t>::type>
        super;
    public:
      typedef typename Graph::edge edge;

      edge_iterator() noexcept
        : g_(nullptr), t_(0)
      {
      }

      edge_iterator(Graph* g, edge t) noexcept
        : g_(g), t_(t)
      {
      }

      bool operator==(edge_iterator o) const
      {
        return t_ == o.t_;
      }

      bool operator!=(edge_iterator o) const
      {
        return t_ != o.t_;
      }

      typename super::reference
      operator*()
      {
        return g_->edge_storage(t_);
      }

      const typename super::reference
      operator*() const
      {
        return g_->edge_storage(t_);
      }

      typename super::pointer
      operator->()
      {
        return &g_->edge_storage(t_);
      }

      const typename super::pointer
      operator->() const
      {
        return &g_->edge_storage(t_);
      }

      edge_iterator operator++()
      {
        t_ = operator*().next_succ;
        return *this;
      }

      edge_iterator operator++(int)
      {
        edge_iterator ti = *this;
        t_ = operator*().next_succ;
        return ti;
      }

      operator bool() const
      {
        return t_;
      }

      edge trans() const
      {
        return t_;
      }

    protected:
      Graph* g_;
      edge t_;
    };

    template <typename Graph>
    class SPOT_API killer_edge_iterator: public edge_iterator<Graph>
    {
      typedef edge_iterator<Graph> super;
    public:
      typedef typename Graph::state_storage_t state_storage_t;
      typedef typename Graph::edge edge;

      killer_edge_iterator(Graph* g, edge t, state_storage_t& src) noexcept
        : super(g, t), src_(src), prev_(0)
      {
      }

      killer_edge_iterator operator++()
      {
        prev_ = this->t_;
        this->t_ = this->operator*().next_succ;
        return *this;
      }

      killer_edge_iterator operator++(int)
      {
        killer_edge_iterator ti = *this;
        ++*this;
        return ti;
      }

      // Erase the current edge and advance the iterator.
      void erase()
      {
        edge next = this->operator*().next_succ;

        // Update source state and previous edges
        if (prev_)
          {
            this->g_->edge_storage(prev_).next_succ = next;
          }
        else
          {
            if (src_.succ == this->t_)
              src_.succ = next;
          }
        if (src_.succ_tail == this->t_)
          {
            src_.succ_tail = prev_;
            SPOT_ASSERT(next == 0);
          }

        // Erased edges have themselves as next_succ.
        this->operator*().next_succ = this->t_;

        // Advance iterator to next edge.
        this->t_ = next;

        ++this->g_->killed_edge_;
      }

    protected:
      state_storage_t& src_;
      edge prev_;
    };


    //////////////////////////////////////////////////
    // State OUT
    //////////////////////////////////////////////////

    // Fake container listing the outgoing edges of a state.

    template <typename Graph>
    class SPOT_API state_out
    {
    public:
      typedef typename Graph::edge edge;
      state_out(Graph* g, edge t) noexcept
        : g_(g), t_(t)
      {
      }

      edge_iterator<Graph> begin()
      {
        return {g_, t_};
      }

      edge_iterator<Graph> end()
      {
        return {};
      }

      void recycle(edge t)
      {
        t_ = t;
      }

    protected:
      Graph* g_;
      edge t_;
    };

    //////////////////////////////////////////////////
    // all_trans
    //////////////////////////////////////////////////

    template <typename Graph>
    class SPOT_API all_edge_iterator: public
      std::iterator<std::forward_iterator_tag,
                    typename
                    std::conditional<std::is_const<Graph>::value,
                                     const typename Graph::edge_storage_t,
                                     typename Graph::edge_storage_t>::type>
    {
      typedef
        std::iterator<std::forward_iterator_tag,
                      typename
                      std::conditional<std::is_const<Graph>::value,
                                       const typename Graph::edge_storage_t,
                                       typename Graph::edge_storage_t>::type>
        super;

      typedef typename std::conditional<std::is_const<Graph>::value,
                                        const typename Graph::edge_vector_t,
                                        typename Graph::edge_vector_t>::type
        tv_t;

      unsigned t_;
      tv_t& tv_;

      void skip_()
      {
        unsigned s = tv_.size();
        do
          ++t_;
        while (t_ < s && tv_[t_].next_succ == t_);
      }

    public:
      all_edge_iterator(unsigned pos, tv_t& tv) noexcept
        : t_(pos), tv_(tv)
      {
        skip_();
      }

      all_edge_iterator(tv_t& tv) noexcept
        : t_(tv.size()), tv_(tv)
      {
      }

      all_edge_iterator& operator++()
      {
        skip_();
        return *this;
      }

      all_edge_iterator operator++(int)
      {
        all_edge_iterator old = *this;
        ++*this;
        return old;
      }

      bool operator==(all_edge_iterator o) const
      {
        return t_ == o.t_;
      }

      bool operator!=(all_edge_iterator o) const
      {
        return t_ != o.t_;
      }

      typename super::reference
      operator*()
      {
        return tv_[t_];
      }

      const typename super::reference
      operator*() const
      {
        return tv_[t_];
      }

      const typename super::pointer
      operator->()
      {
        return &tv_[t_];
      }

      typename super::pointer
      operator->() const
      {
        return &tv_[t_];
      }
    };


    template <typename Graph>
    class SPOT_API all_trans
    {
    public:
      typedef typename std::conditional<std::is_const<Graph>::value,
                                        const typename Graph::edge_vector_t,
                                        typename Graph::edge_vector_t>::type
        tv_t;
      typedef all_edge_iterator<Graph> iter_t;
    private:
      tv_t& tv_;
    public:

      all_trans(tv_t& tv) noexcept
        : tv_(tv)
      {
      }

      iter_t begin()
      {
        return {0, tv_};
      }

      iter_t end()
      {
        return {tv_};
      }
    };

  } // namespace internal


  /// \brief A directed graph
  ///
  /// \tparam State_Data data to attach to states
  /// \tparam Edge_Data data to attach to edges
  /// \tparam Alternating whether the automaton should be alternating
  template <typename State_Data, typename Edge_Data, bool Alternating>
  class digraph
  {
    friend class internal::edge_iterator<digraph>;
    friend class internal::edge_iterator<const digraph>;
    friend class internal::killer_edge_iterator<digraph>;

  public:
    typedef internal::edge_iterator<digraph> iterator;
    typedef internal::edge_iterator<const digraph> const_iterator;

    /// Whether the automaton is alternating
    static constexpr bool alternating()
    {
      return Alternating;
    }

    // Extra data to store on each state or edge.
    typedef State_Data state_data_t;
    typedef Edge_Data edge_data_t;

    // State and edges are identified by their indices in some
    // vector.
    typedef unsigned state;
    typedef unsigned edge;

    // The type of an output state (when seen from a edge)
    // depends on the kind of graph we build
    typedef typename std::conditional<Alternating,
                                      std::vector<state>,
                                      state>::type out_state;

    typedef internal::distate_storage<edge,
                                      internal::boxed_label<State_Data>>
      state_storage_t;
    typedef internal::edge_storage<state, out_state, edge,
                                    internal::boxed_label<Edge_Data>>
      edge_storage_t;
    typedef std::vector<state_storage_t> state_vector;
    typedef std::vector<edge_storage_t> edge_vector_t;
  protected:
    state_vector states_;
    edge_vector_t edges_;
    // Number of erased edges.
    unsigned killed_edge_;
  public:
    /// \brief Construct an empty graph
    ///
    /// Construct an empty graph, and reserve space for \a max_states
    /// states and \a max_trans edges.  These are not hard
    /// limits, but just hints to pre-allocate a data structure that
    /// may hold that much items.
    digraph(unsigned max_states = 10, unsigned max_trans = 0)
      : killed_edge_(0)
    {
      states_.reserve(max_states);
      if (max_trans == 0)
        max_trans = max_states * 2;
      edges_.reserve(max_trans + 1);
      // Edge number 0 is not used, because we use this index
      // to mark the absence of a edge.
      edges_.resize(1);
      // This causes edge 0 to be considered as dead.
      edges_[0].next_succ = 0;
    }

    /// The number of states in the automaton
    unsigned num_states() const
    {
      return states_.size();
    }

    /// \brief The number of edges in the automaton
    ///
    /// Killed edges are omitted.
    unsigned num_edges() const
    {
      return edges_.size() - killed_edge_ - 1;
    }

    /// \brief Create a new states
    ///
    /// All arguments are forwarded to the State_Data constructor.
    ///
    /// \return a state number
    template <typename... Args>
    state new_state(Args&&... args)
    {
      state s = states_.size();
      states_.emplace_back(std::forward<Args>(args)...);
      return s;
    }

    /// \brief Create n new states
    ///
    /// All arguments are forwarded to the State_Data constructor of
    /// each of the n states.
    ///
    /// \return the first state number
    template <typename... Args>
    state new_states(unsigned n, Args&&... args)
    {
      state s = states_.size();
      states_.reserve(s + n);
      while (n--)
        states_.emplace_back(std::forward<Args>(args)...);
      return s;
    }

    /// @{
    /// \brief return a reference to the storage of a state
    ///
    /// The storage includes any of the user-supplied State_Data, plus
    /// some custom fields needed to find the outgoing transitions.
    state_storage_t&
    state_storage(state s)
    {
      return states_[s];
    }

    const state_storage_t&
    state_storage(state s) const
    {
      return states_[s];
    }
    ///@}

    ///@{
    /// \brief return the State_Data associated to a state
    ///
    /// This does not use State_Data& as return type, because
    /// State_Data might be void.
    typename state_storage_t::data_t&
    state_data(state s)
    {
      return states_[s].data();
    }

    const typename state_storage_t::data_t&
    state_data(state s) const
    {
      return states_[s].data();
    }
    ///@}

    ///@{
    /// \brief return a reference to the storage of an edge
    ///
    /// The storage includes any of the user-supplied Edge_Data, plus
    /// some custom fields needed to find the next transitions.
    edge_storage_t&
    edge_storage(edge s)
    {
      return edges_[s];
    }

    const edge_storage_t&
    edge_storage(edge s) const
    {
      return edges_[s];
    }
    ///@}

    ///@{
    /// \brief return the Edgeg_Data of an edge.
    ///
    /// This does not use Edge_Data& as return type, because
    /// Edge_Data might be void.
    typename edge_storage_t::data_t&
    edge_data(edge s)
    {
      return edges_[s].data();
    }

    const typename edge_storage_t::data_t&
    edge_data(edge s) const
    {
      return edges_[s].data();
    }
    ///@}

    /// \brief Create a new edge
    ///
    /// \param src the source state
    /// \param dst the destination state
    /// \param args arguments to forward to the Edge_Data constructor
    template <typename... Args>
    edge
    new_edge(state src, out_state dst, Args&&... args)
    {
      edge t = edges_.size();
      edges_.emplace_back(dst, 0, src, std::forward<Args>(args)...);

      edge st = states_[src].succ_tail;
      SPOT_ASSERT(st < t || !st);
      if (!st)
        states_[src].succ = t;
      else
        edges_[st].next_succ = t;
      states_[src].succ_tail = t;
      return t;
    }

    /// Convert a storage reference into a state number
    state index_of_state(const state_storage_t& ss) const
    {
      SPOT_ASSERT(!states_.empty());
      return &ss - &states_.front();
    }

    /// Conveart a storage reference into an edge number
    edge index_of_edge(const edge_storage_t& tt) const
    {
      SPOT_ASSERT(!edges_.empty());
      return &tt - &edges_.front();
    }

    /// @{
    /// \brief Return a fake container with all edges leaving \a src
    internal::state_out<digraph>
    out(state src)
    {
      return {this, states_[src].succ};
    }

    internal::state_out<digraph>
    out(state_storage_t& src)
    {
      return out(index_of_state(src));
    }

    internal::state_out<const digraph>
    out(state src) const
    {
      return {this, states_[src].succ};
    }

    internal::state_out<const digraph>
    out(state_storage_t& src) const
    {
      return out(index_of_state(src));
    }
    /// @}

    /// @{
    ///
    /// \brief Return a fake container with all edges leaving \a src,
    /// allowing erasure.
    internal::killer_edge_iterator<digraph>
    out_iteraser(state_storage_t& src)
    {
      return {this, src.succ, src};
    }

    internal::killer_edge_iterator<digraph>
    out_iteraser(state src)
    {
      return out_iteraser(state_storage(src));
    }
    ///@}

    /// @{
    ///
    /// \brief Return the vector of states.
    const state_vector& states() const
    {
      return states_;
    }

    state_vector& states()
    {
      return states_;
    }
    /// @}

    /// @{
    ///
    /// \brief Return a fake container with all edges (exluding erased
    /// edges)
    internal::all_trans<const digraph> edges() const
    {
      return edges_;
    }

    internal::all_trans<digraph> edges()
    {
      return edges_;
    }
    /// @}

    /// @{
    /// \brief Return the vector of all edges.
    ///
    /// When using this method, beware that the first entry (edge #0)
    /// is not a real edge, and that any edge with next_succ pointing
    /// to itself is an erased edge.
    ///
    /// You should probably use edges() instead.
    const edge_vector_t& edge_vector() const
    {
      return edges_;
    }

    edge_vector_t& edge_vector()
    {
      return edges_;
    }
    /// @}

    /// \brief Test whether the given edge is valid.
    ///
    /// An edge is valid if its number is less than the total number
    /// of edges, and it does not correspond to an erased (dead) edge.
    ///
    /// \see is_dead_edge()
    bool is_valid_edge(edge t) const
    {
      // Erased edges have their next_succ pointing to
      // themselves.
      return (t < edges_.size() &&
              edges_[t].next_succ != t);
    }

    /// @{
    /// \brief Tests whether an edge has been erased.
    ///
    /// \see is_valid_edge
    bool is_dead_edge(unsigned t) const
    {
      return edges_[t].next_succ == t;
    }

    bool is_dead_edge(const edge_storage_t& t) const
    {
      return t.next_succ == index_of_edge(t);
    }
    /// @}


    /// Dump the state and edge storage for debugging
    void dump_storage(std::ostream& o) const
    {
      unsigned tend = edges_.size();
      for (unsigned t = 1; t < tend; ++t)
        {
          o << 't' << t << ": (s"
            << edges_[t].src << ", s"
            << edges_[t].dst << ") t"
            << edges_[t].next_succ << '\n';
        }
      unsigned send = states_.size();
      for (unsigned s = 0; s < send; ++s)
        {
          o << 's' << s << ": t"
            << states_[s].succ << " t"
            << states_[s].succ_tail << '\n';
        }
    }

    /// \brief Remove all dead edges.
    ///
    /// The edges_ vector is left in a state that is incorrect and
    /// should eventually be fixed by a call to chain_edges_() before
    /// any iteration on the successor of a state is performed.
    void remove_dead_edges_()
    {
      if (killed_edge_ == 0)
        return;
      auto i = std::remove_if(edges_.begin() + 1, edges_.end(),
                              [this](const edge_storage_t& t) {
                                return this->is_dead_edge(t);
                              });
      edges_.erase(i, edges_.end());
      killed_edge_ = 0;
    }

    /// \brief Sort all edge according to a predicate
    ///
    /// This will invalidate all iterators, and also destroy edge
    /// chains.  Call chain_edges_() immediately afterwards unless you
    /// know what you are doing.
    template<class Predicate = std::less<edge_storage_t>>
    void sort_edges_(Predicate p = Predicate())
    {
      //std::cerr << "\nbefore\n";
      //dump_storage(std::cerr);
      std::stable_sort(edges_.begin() + 1, edges_.end(), p);
    }

    /// \brief Reconstruct the chain of outgoing edges
    ///
    /// Should be called only when it is known that all edges
    /// with the same destination are consecutive in the vector.
    void chain_edges_()
    {
      state last_src = -1U;
      edge tend = edges_.size();
      for (edge t = 1; t < tend; ++t)
        {
          state src = edges_[t].src;
          if (src != last_src)
            {
              states_[src].succ = t;
              if (last_src != -1U)
                {
                  states_[last_src].succ_tail = t - 1;
                  edges_[t - 1].next_succ = 0;
                }
              while (++last_src != src)
                {
                  states_[last_src].succ = 0;
                  states_[last_src].succ_tail = 0;
                }
            }
          else
            {
              edges_[t - 1].next_succ = t;
            }
        }
      if (last_src != -1U)
        {
          states_[last_src].succ_tail = tend - 1;
          edges_[tend - 1].next_succ = 0;
        }
      unsigned send = states_.size();
      while (++last_src != send)
        {
          states_[last_src].succ = 0;
          states_[last_src].succ_tail = 0;
        }
      //std::cerr << "\nafter\n";
      //dump_storage(std::cerr);
    }

    /// \brief Rename all the states in the edge vector.
    ///
    /// The edges_ vector is left in a state that is incorrect and
    /// should eventually be fixed by a call to chain_edges_() before
    /// any iteration on the successor of a state is performed.
    void rename_states_(const std::vector<unsigned>& newst)
    {
      SPOT_ASSERT(newst.size() == states_.size());
      unsigned tend = edges_.size();
      for (unsigned t = 1; t < tend; t++)
        {
          edges_[t].dst = newst[edges_[t].dst];
          edges_[t].src = newst[edges_[t].src];
        }
    }

    /// \brief Rename and remove states.
    ///
    /// \param newst A vector indicating how each state should be renumbered.
    /// Use -1U to erase a state.
    /// \param used_states the number of states used (after renumbering)
    void defrag_states(std::vector<unsigned>&& newst, unsigned used_states)
    {
      SPOT_ASSERT(newst.size() == states_.size());
      SPOT_ASSERT(used_states > 0);

      //std::cerr << "\nbefore defrag\n";
      //dump_storage(std::cerr);

      // Shift all states in states_, as indicated by newst.
      unsigned send = states_.size();
      for (state s = 0; s < send; ++s)
        {
          state dst = newst[s];
          if (dst == s)
            continue;
          if (dst == -1U)
            {
              // This is an erased state.  Mark all its edges as
              // dead (i.e., t.next_succ should point to t for each of
              // them).
              auto t = states_[s].succ;
              while (t)
                std::swap(t, edges_[t].next_succ);
              continue;
            }
          states_[dst] = std::move(states_[s]);
        }
      states_.resize(used_states);

      // Shift all edges in edges_.  The algorithm is
      // similar to remove_if, but it also keeps the correspondence
      // between the old and new index as newidx[old] = new.
      unsigned tend = edges_.size();
      std::vector<edge> newidx(tend);
      unsigned dest = 1;
      for (edge t = 1; t < tend; ++t)
        {
          if (is_dead_edge(t))
            continue;
          if (t != dest)
            edges_[dest] = std::move(edges_[t]);
          newidx[t] = dest;
          ++dest;
        }
      edges_.resize(dest);
      killed_edge_ = 0;

      // Adjust next_succ and dst pointers in all edges.
      for (edge t = 1; t < dest; ++t)
        {
          auto& tr = edges_[t];
          tr.next_succ = newidx[tr.next_succ];
          tr.dst = newst[tr.dst];
          tr.src = newst[tr.src];
          SPOT_ASSERT(tr.dst != -1U);
        }

      // Adjust succ and succ_tails pointers in all states.
      for (auto& s: states_)
        {
          s.succ = newidx[s.succ];
          s.succ_tail = newidx[s.succ_tail];
        }

      //std::cerr << "\nafter defrag\n";
      //dump_storage(std::cerr);
    }
  };
}
