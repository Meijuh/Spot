// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et Développement
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

#include "fwd.hh"
#include "graph/graph.hh"
#include "graph/ngraph.hh"
#include "twa/bdddict.hh"
#include "twa/twa.hh"
#include "twaalgos/dupexp.hh"
#include "ltlast/formula.hh"
#include <sstream>

namespace spot
{

  struct SPOT_API twa_graph_state: public spot::state
  {
  public:
    twa_graph_state():
      spot::state()
    {
    }

    virtual ~twa_graph_state() noexcept
    {
    }

    virtual int compare(const spot::state* other) const
    {
      auto o = down_cast<const twa_graph_state*>(other);
      assert(o);

      // Do not simply return "other - this", it might not fit in an int.
      if (o < this)
	return -1;
      if (o > this)
	return 1;
      return 0;
    }

    virtual size_t hash() const
    {
      return
	reinterpret_cast<const char*>(this) - static_cast<const char*>(nullptr);
    }

    virtual twa_graph_state*
    clone() const
    {
      return const_cast<twa_graph_state*>(this);
    }

    virtual void destroy() const
    {
    }
  };

  struct SPOT_API twa_graph_trans_data
  {
    bdd cond;
    acc_cond::mark_t acc;

    explicit twa_graph_trans_data()
      : cond(bddfalse), acc(0)
    {
    }

    twa_graph_trans_data(bdd cond, acc_cond::mark_t acc = 0U)
      : cond(cond), acc(acc)
    {
    }

    bool operator<(const twa_graph_trans_data& other) const
    {
      if (cond.id() < other.cond.id())
	return true;
      if (cond.id() > other.cond.id())
	return false;
      return acc < other.acc;
    }

    bool operator==(const twa_graph_trans_data& other) const
    {
      return cond.id() == other.cond.id() &&
        acc == other.acc;
    }
  };


  template<class Graph>
  class SPOT_API twa_graph_succ_iterator final:
    public twa_succ_iterator
  {
  private:
    typedef typename Graph::transition transition;
    typedef typename Graph::state_data_t state;
    const Graph* g_;
    transition t_;
    transition p_;

  public:
    twa_graph_succ_iterator(const Graph* g, transition t)
      : g_(g), t_(t)
    {
    }

    virtual void recycle(transition t)
    {
      t_ = t;
    }

    virtual bool first()
    {
      p_ = t_;
      return p_;
    }

    virtual bool next()
    {
      p_ = g_->trans_storage(p_).next_succ;
      return p_;
    }

    virtual bool done() const
    {
      return !p_;
    }

    virtual twa_graph_state* current_state() const
    {
      assert(!done());
      return const_cast<twa_graph_state*>
	(&g_->state_data(g_->trans_storage(p_).dst));
    }

    virtual bdd current_condition() const
    {
      assert(!done());
      return g_->trans_data(p_).cond;
    }

    virtual acc_cond::mark_t current_acceptance_conditions() const
    {
      assert(!done());
      return g_->trans_data(p_).acc;
    }

    transition pos() const
    {
      return p_;
    }

  };

  class SPOT_API twa_graph final: public twa
  {
  public:
    typedef digraph<twa_graph_state, twa_graph_trans_data> graph_t;
    typedef graph_t::trans_storage_t trans_storage_t;

  protected:
    graph_t g_;
    mutable unsigned init_number_;

  public:
    twa_graph(const bdd_dict_ptr& dict)
      : twa(dict),
	init_number_(0)
    {
    }

    explicit twa_graph(const const_twa_graph_ptr& other, prop_set p)
      : twa(other->get_dict()),
        g_(other->g_), init_number_(other->init_number_)
      {
	copy_acceptance_of(other);
	copy_ap_of(other);
	prop_copy(other, p);
      }

    virtual ~twa_graph()
    {
      get_dict()->unregister_all_my_variables(this);
      // Prevent this state from being destroyed by ~twa(),
      // as the state will be destroyed when g_ is destroyed.
      last_support_conditions_input_ = 0;
    }

    // FIXME: Once we ditch GCC 4.6, we can using a template aliases
    // (supported from GCC 4.7 onward) instead of this.
    template <typename State_Name,
	      typename Name_Hash = std::hash<State_Name>,
	      typename Name_Equal = std::equal_to<State_Name>>
    struct namer
    {
      typedef named_graph<graph_t, State_Name, Name_Hash, Name_Equal> type;
    };

    template <typename State_Name,
	      typename Name_Hash = std::hash<State_Name>,
	      typename Name_Equal = std::equal_to<State_Name>>
    typename namer<State_Name, Name_Hash, Name_Equal>::type*
    create_namer()
    {
      return new named_graph<graph_t, State_Name, Name_Hash, Name_Equal>(g_);
    }

    typename namer<const ltl::formula*>::type*
    create_formula_namer()
    {
      return create_namer<const ltl::formula*>();
    }

    void
    release_formula_namer(typename namer<const ltl::formula*>::type* namer,
			  bool keep_names);

    graph_t& get_graph()
    {
      return g_;
    }

    const graph_t& get_graph() const
    {
      return g_;
    }

    unsigned num_states() const
    {
      return g_.num_states();
    }

    unsigned num_transitions() const
    {
      return g_.num_transitions();
    }

    void set_init_state(graph_t::state s)
    {
      assert(s < num_states());
      init_number_ = s;
    }

    void set_init_state(const state* s)
    {
      set_init_state(state_number(s));
    }

    graph_t::state get_init_state_number() const
    {
      if (num_states() == 0)
	const_cast<graph_t&>(g_).new_state();
      return init_number_;
    }

    // FIXME: The return type ought to be const.
    virtual twa_graph_state* get_init_state() const
    {
      if (num_states() == 0)
	const_cast<graph_t&>(g_).new_state();
      return const_cast<twa_graph_state*>(state_from_number(init_number_));
    }

    virtual twa_succ_iterator*
    succ_iter(const state* st) const
    {
      auto s = down_cast<const typename graph_t::state_storage_t*>(st);
      assert(s);
      assert(!s->succ || g_.valid_trans(s->succ));

      if (this->iter_cache_)
	{
	  auto it =
	    down_cast<twa_graph_succ_iterator<graph_t>*>(this->iter_cache_);
	  it->recycle(s->succ);
	  this->iter_cache_ = nullptr;
	  return it;
	}
      return new twa_graph_succ_iterator<graph_t>(&g_, s->succ);
    }

    graph_t::state
    state_number(const state* st) const
    {
      auto s = down_cast<const typename graph_t::state_storage_t*>(st);
      assert(s);
      return s - &g_.state_storage(0);
    }

    const twa_graph_state*
    state_from_number(graph_t::state n) const
    {
      return &g_.state_data(n);
    }

    std::string format_state(unsigned n) const
    {
      std::stringstream ss;
      ss << n;
      return ss.str();
    }

    virtual std::string format_state(const state* st) const
    {
      return format_state(state_number(st));
    }

    twa_graph_trans_data& trans_data(const twa_succ_iterator* it)
    {
      auto* i = down_cast<const twa_graph_succ_iterator<graph_t>*>(it);
      return g_.trans_data(i->pos());
    }

    twa_graph_trans_data& trans_data(unsigned t)
    {
      return g_.trans_data(t);
    }

    const twa_graph_trans_data& trans_data(const twa_succ_iterator* it) const
    {
      auto* i = down_cast<const twa_graph_succ_iterator<graph_t>*>(it);
      return g_.trans_data(i->pos());
    }

    const twa_graph_trans_data& trans_data(unsigned t) const
    {
      return g_.trans_data(t);
    }

    trans_storage_t& trans_storage(const twa_succ_iterator* it)
    {
      auto* i = down_cast<const twa_graph_succ_iterator<graph_t>*>(it);
      return g_.trans_storage(i->pos());
    }

    trans_storage_t& trans_storage(unsigned t)
    {
      return g_.trans_storage(t);
    }

    const trans_storage_t
      trans_storage(const twa_succ_iterator* it) const
    {
      auto* i = down_cast<const twa_graph_succ_iterator<graph_t>*>(it);
      return g_.trans_storage(i->pos());
    }

    const trans_storage_t trans_storage(unsigned t) const
    {
      return g_.trans_storage(t);
    }

    unsigned new_state()
    {
      return g_.new_state();
    }

    unsigned new_states(unsigned n)
    {
      return g_.new_states(n);
    }

    unsigned new_transition(unsigned src, unsigned dst,
			    bdd cond, acc_cond::mark_t acc = 0U)
    {
      return g_.new_transition(src, dst, cond, acc);
    }

    unsigned new_acc_transition(unsigned src, unsigned dst,
				bdd cond, bool acc = true)
    {
      if (acc)
	return g_.new_transition(src, dst, cond, acc_.all_sets());
      else
	return g_.new_transition(src, dst, cond);
    }

#ifndef SWIG
    auto out(unsigned src) const
      SPOT_RETURN(g_.out(src));
    auto out(unsigned src)
      SPOT_RETURN(g_.out(src));

    auto states() const
      SPOT_RETURN(g_.states());
    auto states()
      SPOT_RETURN(g_.states());

    auto transitions() const
      SPOT_RETURN(g_.transitions());
    auto transitions()
      SPOT_RETURN(g_.transitions());

    auto transition_vector() const
      SPOT_RETURN(g_.transition_vector());
    auto transition_vector()
      SPOT_RETURN(g_.transition_vector());

    auto is_dead_transition(const graph_t::trans_storage_t& t) const
      SPOT_RETURN(g_.is_dead_transition(t));
#endif

    virtual bdd compute_support_conditions(const state* s) const
    {
      bdd sum = bddfalse;
      for (auto& t: out(state_number(s)))
	sum |= t.cond;
      return sum;
    }

    /// Iterate over all transitions, and merge those with compatible
    /// extremities and acceptance.
    void merge_transitions();

    /// Remove all states without successors.
    void purge_dead_states();

    /// Remove all unreachable states.
    void purge_unreachable_states();

    bool state_is_accepting(unsigned s) const
    {
      assert(has_state_based_acc() || acc_.num_sets() == 0);
      for (auto& t: g_.out(s))
	// Stop at the first transition, since the remaining should be
	// labeled identically.
	return acc_.accepting(t.acc);
      return false;
    }

    bool state_is_accepting(const state* s) const
    {
      return state_is_accepting(state_number(s));
    }

    bool operator==(const twa_graph& aut) const
    {
      if (num_states() != aut.num_states() ||
          num_transitions() != aut.num_transitions() ||
          acc().num_sets() != aut.acc().num_sets())
        return false;
      auto& trans1 = transition_vector();
      auto& trans2 = aut.transition_vector();
      return std::equal(trans1.begin() + 1, trans1.end(),
                        trans2.begin() + 1);
    }
  };

  inline twa_graph_ptr make_twa_graph(const bdd_dict_ptr& dict)
  {
    return std::make_shared<twa_graph>(dict);
  }

  inline twa_graph_ptr make_twa_graph(const twa_graph_ptr& aut,
					    twa::prop_set p)
  {
    return std::make_shared<twa_graph>(aut, p);
  }

  inline twa_graph_ptr make_twa_graph(const const_twa_graph_ptr& aut,
					    twa::prop_set p)
  {
    return std::make_shared<twa_graph>(aut, p);
  }

  inline twa_graph_ptr make_twa_graph(const const_twa_ptr& aut,
					    twa::prop_set p)
  {
    auto a = std::dynamic_pointer_cast<const twa_graph>(aut);
    if (a)
      return std::make_shared<twa_graph>(a, p);
    else
      return tgba_dupexp_dfs(aut, p);
  }
}
