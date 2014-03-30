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
#include "tgba/bdddict.hh"
#include "tgba/tgba.hh"
#include "misc/bddop.hh"
#include <sstream>

namespace spot
{

  struct SPOT_API tgba_graph_state: public spot::state
  {
  public:
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

    tgba_graph_trans_data(bdd cond, bdd acc)
      : cond(cond), acc(acc)
    {
    }
  };


  template<class Graph>
  class tgba_digraph_succ_iterator: public tgba_succ_iterator
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

  class tgba_digraph: public tgba
  {
  protected:
    typedef digraph<tgba_graph_state, tgba_graph_trans_data> graph_t;
    graph_t g_;
    bdd_dict* dict_;
    bdd all_acceptance_conditions_;
    bdd neg_acceptance_conditions_;
    mutable const tgba_graph_state* init_;

  public:
    tgba_digraph(bdd_dict* dict)
      : dict_(dict), init_(nullptr)
    {
    }

    virtual ~tgba_digraph()
    {
      dict_->unregister_all_my_variables(this);
      // Prevent this state from being destroyed by ~tgba(),
      // as the state will be destroyed when g_ is destroyed.
      last_support_conditions_input_ = 0;
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
      init_ = &g_.state_data(s);
    }

    void set_init_state(const state* s)
    {
      init_ = down_cast<const tgba_graph_state*>(s);
      assert(init_);
    }

    virtual tgba_graph_state* get_init_state() const
    {
      if (num_states() == 0)
	const_cast<graph_t&>(g_).new_state();
      if (!init_)
	init_ = &g_.state_data(0);
      return const_cast<tgba_graph_state*>(init_);
    }

    virtual graph_t::state get_init_state_number() const
    {
      if (num_states() == 0)
	const_cast<graph_t&>(g_).new_state();
      if (!init_)
	return 0;
      return state_number(init_);
    }

    virtual tgba_succ_iterator*
    succ_iter(const state* st) const
    {
      auto s = down_cast<const typename graph_t::state_storage_t*>(st);
      assert(s);
      assert(s->succ < g_.num_transitions());

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

    const state*
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


    void set_acceptance_conditions(bdd all)
    {
      bdd sup = bdd_support(all);
      this->dict_->register_acceptance_variables(sup, this);
      neg_acceptance_conditions_ = bddtrue;
      while (sup != bddtrue)
	{
	  neg_acceptance_conditions_ &= bdd_nithvar(bdd_var(sup));
	  sup = bdd_high(sup);
	}
      all_acceptance_conditions_ =
	compute_all_acceptance_conditions(neg_acceptance_conditions_);
    }

    /// \brief Copy the acceptance conditions of another tgba.
    void copy_acceptance_conditions_of(const tgba *a)
    {
      set_acceptance_conditions(a->neg_acceptance_conditions());
    }

    virtual bdd all_acceptance_conditions() const
    {
      return all_acceptance_conditions_;
    }

    virtual bdd neg_acceptance_conditions() const
    {
      return neg_acceptance_conditions_;
    }

    virtual bdd compute_support_conditions(const state*) const
    {
      return bddtrue;
    }
  };

}

#endif // SPOT_TGBA_TGBAGRAPH_HH
