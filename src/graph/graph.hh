// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement de
// l'Epita.
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

#ifndef SPOT_GRAPH_GRAPH_HH
# define SPOT_GRAPH_GRAPH_HH

#include "misc/common.hh"
#include <vector>
#include <type_traits>
#include <tuple>
#include <cassert>
#include <iterator>

namespace spot
{
  template <typename State_Data, typename Trans_Data, bool Alternating = false>
  class SPOT_API digraph;

  namespace internal
  {
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

      template <typename... Args>
      boxed_label(Args&&... args):
	label{std::forward<Args>(args)...}
      {
      }

      // if Data is a POD type, G++ 4.8.2 wants default values for all
      // label fields unless we define this default constructor here.
      explicit boxed_label()
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

      template <typename... Args>
      boxed_label(Args&&... args):
	Data{std::forward<Args>(args)...}
      {
      }

      // if Data is a POS type, G++ 4.8.2 wants default values for all
      // label fields unless we define this default constructor here.
      explicit boxed_label()
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

    template <typename Transition, typename State_Data>
    struct SPOT_API distate_storage: public State_Data
    {
      Transition succ; // First outgoing transition (used when iterating)
      Transition succ_tail;	// Last outgoing transition (used for
				// appending new transitions)

      template <typename... Args>
      distate_storage(Args&&... args):
	State_Data{std::forward<Args>(args)...},
	succ(0),
	succ_tail(0)
      {
      }
    };

    //////////////////////////////////////////////////
    // Transition storage
    //////////////////////////////////////////////////

    // Again two implementation: one with label, and one without.

    template <typename State, typename Transition, typename Trans_Data>
    struct SPOT_API trans_storage: public Trans_Data
    {
      typedef Transition transition;

      State dst;		// destination
      Transition next_succ;	// next outgoing transition with same
				// source, or 0
      explicit trans_storage()
	: Trans_Data{}
      {
      }

      template <typename... Args>
      trans_storage(State dst, Transition next_succ, Args&&... args)
	: Trans_Data{std::forward<Args>(args)...},
	  dst(dst), next_succ(next_succ)
      {
      }
    };

    //////////////////////////////////////////////////
    // Transition iterator
    //////////////////////////////////////////////////

    // This holds a graph and a transition number that is the start of
    // a list, and it iterates over all the trans_storage_t elements
    // of that list.

    template <typename Graph>
    class SPOT_API trans_iterator:
      std::iterator<std::forward_iterator_tag,
		    typename
		    std::conditional<std::is_const<Graph>::value,
				     const typename Graph::trans_storage_t,
				     typename Graph::trans_storage_t>::type>
    {
      typedef
	std::iterator<std::forward_iterator_tag,
		      typename
		      std::conditional<std::is_const<Graph>::value,
				       const typename Graph::trans_storage_t,
				       typename Graph::trans_storage_t>::type>
	super;
    public:
      typedef typename Graph::transition transition;

      trans_iterator()
	: g_(nullptr), t_(0)
      {
      }

      trans_iterator(Graph* g, transition t): g_(g), t_(t)
      {
      }

      bool operator==(trans_iterator o)
      {
	return t_ == o.t_;
      }

      bool operator!=(trans_iterator o)
      {
	return t_ != o.t_;
      }

      typename super::reference
      operator*()
      {
	return g_->trans_storage(t_);
      }

      typename super::pointer
      operator->()
      {
	return &g_->trans_storage(t_);
      }

      trans_iterator operator++()
      {
	t_ = operator*().next_succ;
	return *this;
      }

      trans_iterator operator++(int)
      {
	trans_iterator ti = *this;
	t_ = operator*().next_succ;
	return ti;
      }

      operator bool() const
      {
	return t_;
      }

    protected:
      Graph* g_;
      transition t_;
    };

    //////////////////////////////////////////////////
    // State OUT
    //////////////////////////////////////////////////

    // Fake container listing the outgoing transitions of a state.

    template <typename Graph>
    class SPOT_API state_out
    {
    public:
      typedef typename Graph::transition transition;
      state_out(Graph* g, transition t):
	g_(g), t_(t)
      {
      }

      trans_iterator<Graph> begin()
      {
	return {g_, t_};
      }

      trans_iterator<Graph> end()
      {
	return {};
      }

      void recycle(transition t)
      {
	t_ = t;
      }

    protected:
      Graph* g_;
      transition t_;
    };

  }

  // The actual graph implementation

  template <typename State_Data, typename Trans_Data, bool Alternating>
  class digraph
  {
    friend class internal::trans_iterator<digraph>;
    friend class internal::trans_iterator<const digraph>;

  public:
    typedef internal::trans_iterator<digraph> iterator;
    typedef internal::trans_iterator<const digraph> const_iterator;

    static constexpr bool alternating()
    {
      return Alternating;
    }

    // Extra data to store on each state or transition.
    typedef State_Data state_data_t;
    typedef Trans_Data trans_data_t;

    // State and transitions are identified by their indices in some
    // vector.
    typedef unsigned state;
    typedef unsigned transition;

    // The type of an output state (when seen from a transition)
    // depends on the kind of graph we build
    typedef typename std::conditional<Alternating,
				      std::vector<state>,
				      state>::type out_state;

    typedef internal::distate_storage<transition,
				      internal::boxed_label<State_Data>>
      state_storage_t;
    typedef internal::trans_storage<out_state, transition,
				    internal::boxed_label<Trans_Data>>
      trans_storage_t;
    typedef std::vector<state_storage_t> state_vector;
    typedef std::vector<trans_storage_t> trans_vector;
  protected:
    state_vector states_;
    trans_vector transitions_;

  public:
    /// \brief construct an empty graph
    ///
    /// Construct an empty graph, and reserve space for \a max_states
    /// states and \a max_trans transitions.  These are not hard
    /// limits, but just hints to pre-allocate a data structure that
    /// may hold that much items.
    digraph(unsigned max_states = 10, unsigned max_trans = 0)
    {
      states_.reserve(max_states);
      if (max_trans == 0)
	max_trans = max_states * 2;
      transitions_.reserve(max_trans + 1);
      // Transition number 0 is not used, because we use this index
      // to mark the absence of a transition.
      transitions_.resize(1);
    }

    unsigned num_states() const
    {
      return states_.size();
    }

    unsigned num_transitions() const
    {
      return transitions_.size();
    }

    template <typename... Args>
    state new_state(Args&&... args)
    {
      state s = states_.size();
      states_.emplace_back(std::forward<Args>(args)...);
      return s;
    }

    template <typename... Args>
    state new_states(unsigned n, Args&&... args)
    {
      state s = states_.size();
      while (n--)
	states_.emplace_back(std::forward<Args>(args)...);
      return s;
    }

    state_storage_t&
    state_storage(state s)
    {
      assert(s < states_.size());
      return states_[s];
    }

    const state_storage_t&
    state_storage(state s) const
    {
      assert(s < states_.size());
      return states_[s];
    }

    // Do not use State_Data& as return type, because State_Data might
    // be void.
    typename state_storage_t::data_t&
    state_data(state s)
    {
      assert(s < states_.size());
      return states_[s].data();
    }

    // May not be called on states with no data.
    const typename state_storage_t::data_t&
    state_data(state s) const
    {
      assert(s < states_.size());
      return states_[s].data();
    }

    trans_storage_t&
    trans_storage(transition s)
    {
      assert(s < transitions_.size());
      return transitions_[s];
    }

    const trans_storage_t&
    trans_storage(transition s) const
    {
      assert(s < transitions_.size());
      return transitions_[s];
    }

    typename trans_storage_t::data_t&
    trans_data(transition s)
    {
      assert(s < transitions_.size());
      return transitions_[s].data();
    }

    const typename trans_storage_t::data_t&
    trans_data(transition s) const
    {
      assert(s < transitions_.size());
      return transitions_[s].data();
    }

    template <typename... Args>
    transition
    new_transition(state src, out_state dst, Args&&... args)
    {
      assert(src < states_.size());

      transition t = transitions_.size();
      transitions_.emplace_back(dst, 0, std::forward<Args>(args)...);

      transition st = states_[src].succ_tail;
      assert(st < t || !st);
      if (!st)
	states_[src].succ = t;
      else
	transitions_[st].next_succ = t;
      states_[src].succ_tail = t;
      return t;
    }

    internal::state_out<digraph>
    out(state src)
    {
      return {this, states_[src].succ};
    }

    internal::state_out<const digraph>
    out(state src) const
    {
      return {this, states_[src].succ};
    }

    unsigned nb_states() const
    {
      return states_.size();
    }

    unsigned nb_trans() const
    {
      return transitions_.size();
    }

    const state_vector& states() const
    {
      return states_;
    }

    state_vector& states()
    {
      return states_;
    }

  };

}

#endif // SPOT_GRAPH_GRAPH_HH
