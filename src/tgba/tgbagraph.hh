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

#ifndef SPOT_TGBA_TGBAGRAPH_HH
# define SPOT_TGBA_TGBAGRAPH_HH

#include "graph/graph.hh"
#include "graph/ngraph.hh"
#include "tgba/bdddict.hh"
#include "tgba/tgba.hh"
#include "misc/bddop.hh"
#include <sstream>

namespace spot
{

  struct SPOT_API tgba_graph_state: public spot::state
  {
  public:
    tgba_graph_state():
      spot::state()
    {
    }

    virtual ~tgba_graph_state() noexcept
    {
    }

    virtual int compare(const spot::state* other) const
    {
      auto o = down_cast<const tgba_graph_state*>(other);
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

    virtual tgba_graph_state*
    clone() const
    {
      return const_cast<tgba_graph_state*>(this);
    }

    virtual void destroy() const
    {
    }
  };

  struct SPOT_API tgba_graph_trans_data
  {
    bdd cond;
    bdd acc;

    explicit tgba_graph_trans_data()
      : cond(bddfalse), acc(bddfalse)
    {
    }

    tgba_graph_trans_data(bdd cond, bdd acc = bddfalse)
      : cond(cond), acc(acc)
    {
    }
  };


  template<class Graph>
  class SPOT_API tgba_digraph_succ_iterator: public tgba_succ_iterator
  {
  private:
    typedef typename Graph::transition transition;
    typedef typename Graph::state_data_t state;
    const Graph* g_;
    transition t_;
    transition p_;

  public:
    tgba_digraph_succ_iterator(const Graph* g, transition t)
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

    virtual tgba_graph_state* current_state() const
    {
      assert(!done());
      return const_cast<tgba_graph_state*>
	(&g_->state_data(g_->trans_storage(p_).dst));
    }

    virtual bdd current_condition() const
    {
      assert(!done());
      return g_->trans_data(p_).cond;
    }

    virtual bdd current_acceptance_conditions() const
    {
      assert(!done());
      return g_->trans_data(p_).acc;
    }

    transition pos() const
    {
      return p_;
    }

  };

  class SPOT_API tgba_digraph: public tgba
  {
  public:
    typedef digraph<tgba_graph_state, tgba_graph_trans_data> graph_t;

  protected:
    graph_t g_;
    bdd_dict* dict_;
    bdd all_acceptance_conditions_;
    bdd neg_acceptance_conditions_;
    mutable unsigned init_number_;

  public:
    tgba_digraph(bdd_dict* dict)
      : dict_(dict),
	all_acceptance_conditions_(bddfalse),
	neg_acceptance_conditions_(bddtrue),
	init_number_(0)
    {
    }

    virtual ~tgba_digraph()
    {
      dict_->unregister_all_my_variables(this);
      // Prevent this state from being destroyed by ~tgba(),
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

    graph_t& get_graph()
    {
      return g_;
    }

    const graph_t& get_graph() const
    {
      return g_;
    }

    virtual bdd_dict* get_dict() const
    {
      return this->dict_;
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

    virtual graph_t::state get_init_state_number() const
    {
      if (num_states() == 0)
	const_cast<graph_t&>(g_).new_state();
      return init_number_;
    }

    // FIXME: The return type ought to be const.
    virtual tgba_graph_state* get_init_state() const
    {
      if (num_states() == 0)
	const_cast<graph_t&>(g_).new_state();
      return const_cast<tgba_graph_state*>(state_from_number(init_number_));
    }

    virtual tgba_succ_iterator*
    succ_iter(const state* st) const
    {
      auto s = down_cast<const typename graph_t::state_storage_t*>(st);
      assert(s);
      assert(!s->succ || g_.valid_trans(s->succ));

      if (this->iter_cache_)
	{
	  auto it =
	    down_cast<tgba_digraph_succ_iterator<graph_t>*>(this->iter_cache_);
	  it->recycle(s->succ);
	  this->iter_cache_ = nullptr;
	  return it;
	}
      return new tgba_digraph_succ_iterator<graph_t>(&g_, s->succ);
    }

    graph_t::state
    state_number(const state* st) const
    {
      auto s = down_cast<const typename graph_t::state_storage_t*>(st);
      assert(s);
      return s - &g_.state_storage(0);
    }

    const tgba_graph_state*
    state_from_number(graph_t::state n) const
    {
      return &g_.state_data(n);
    }

    virtual std::string format_state(const state* st) const
    {
      std::stringstream ss;
      ss << state_number(st);
      return ss.str();
    }

    tgba_graph_trans_data& trans_data(const tgba_succ_iterator* it)
    {
      auto* i = down_cast<const tgba_digraph_succ_iterator<graph_t>*>(it);
      return g_.trans_data(i->pos());
    }

    tgba_graph_trans_data& trans_data(unsigned t)
    {
      return g_.trans_data(t);
    }

    void set_acceptance_conditions(bdd all);
    bdd set_single_acceptance_set();

    unsigned new_state()
    {
      return g_.new_state();
    }

    unsigned new_states(unsigned n)
    {
      return g_.new_states(n);
    }

    unsigned new_transition(unsigned src, unsigned dst,
			    bdd cond, bdd acc = bddfalse)
    {
      return g_.new_transition(src, dst, cond, acc);
    }

    unsigned new_acc_transition(unsigned src, unsigned dst,
				bdd cond, bool acc = true)
    {
      if (acc)
	return g_.new_transition(src, dst, cond, all_acceptance_conditions_);
      else
	return g_.new_transition(src, dst, cond);
    }

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

    /// \brief Copy the acceptance conditions of another tgba.
    void copy_acceptance_conditions_of(const tgba *a)
    {
      set_acceptance_conditions(a->neg_acceptance_conditions());
    }

    void copy_ap_of(const tgba* a)
    {
      dict_->register_all_propositions_of(a, this);
    }

    virtual bdd all_acceptance_conditions() const
    {
      return all_acceptance_conditions_;
    }

    virtual bdd neg_acceptance_conditions() const
    {
      return neg_acceptance_conditions_;
    }

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

  protected:
    unsigned bprops_ = 0;

  public:
    enum bprop {
      StateBasedAcc = 1,
      SingleAccSet = 2,
      SBA = StateBasedAcc | SingleAccSet,
    };

    bool get_bprop(bprop p) const
    {
      return (bprops_ & p) == p;
    }

    void set_bprop(bprop p)
    {
      bprops_ |= p;
    }

    void clear_bprop(bprop p)
    {
      bprops_ &= ~p;
    }

    bool state_is_accepting(unsigned s) const
    {
      assert(get_bprop(StateBasedAcc));
      for (auto& t: g_.out(s))
	// Stop at the first transition, since the remaining should be
	// labeled identically.
	return t.acc == all_acceptance_conditions_;
      return false;
    }

    bool state_is_accepting(const state* s) const
    {
      return state_is_accepting(state_number(s));
    }

  };

}

#endif // SPOT_TGBA_TGBAGRAPH_HH
