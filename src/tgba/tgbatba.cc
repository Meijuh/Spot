// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2011, 2012, 2013, 2014 Laboratoire de Recherche
// et Développement de l'Epita.
// Copyright (C) 2003, 2004, 2005 Laboratoire d'Informatique de Paris
// 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
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

#include <cassert>
#include "tgbatba.hh"
#include "bddprint.hh"
#include "ltlast/constant.hh"
#include "misc/hashfunc.hh"

namespace spot
{
  namespace
  {
    /// \brief A state for spot::tgba_tba_proxy.
    ///
    /// This state is in fact a pair of states: the state from the tgba
    /// automaton, and a state of the "counter" (we use a pointer
    /// to the position in the cycle_acc_ list).
    class state_tba_proxy: public state
    {
      typedef tgba_tba_proxy::cycle_list::const_iterator iterator;
    public:
      state_tba_proxy(state* s, iterator acc)
	:	s_(s), acc_(acc)
      {
      }

      // Note: There is a default copy constructor, needed by
      // std::unordered_set.  It does not clone the state "s", because the
      // destructor will not destroy it either.  Actually, the states
      // are all destroyed in the tgba_tba_proxy destructor.

      virtual
      ~state_tba_proxy()
      {
      }

      void
      destroy() const
      {
      }

      state*
      real_state() const
      {
	return s_;
      }

      bdd
      acceptance_cond() const
      {
	return *acc_;
      }

      iterator
      acceptance_iterator() const
      {
	return acc_;
      }

      virtual int
      compare(const state* other) const
      {
	const state_tba_proxy* o = down_cast<const state_tba_proxy*>(other);
	assert(o);
	// Do not simply return "o - this", it might not fit in an int.
	if (o < this)
	  return -1;
	if (o > this)
	  return 1;
	return 0;
      }

      virtual size_t
      hash() const
      {
	return wang32_hash(s_->hash()) ^ wang32_hash(acc_->id());
      }

      virtual
      state_tba_proxy* clone() const
      {
	return const_cast<state_tba_proxy*>(this);
      }

    private:
      state* s_;
      iterator acc_;
    };

    struct state_tba_proxy_hash
    {
      size_t
      operator()(const state_tba_proxy& s) const
      {
	return s.state_tba_proxy::hash();
      }
    };

    struct state_tba_proxy_equal
    {
      bool
      operator()(const state_tba_proxy& left,
		 const state_tba_proxy& right) const
      {
	if (left.acceptance_iterator() != right.acceptance_iterator())
	  return false;
	return left.real_state()->compare(right.real_state()) == 0;
      }
    };

    typedef std::unordered_set<state_tba_proxy,
			       state_tba_proxy_hash,
			       state_tba_proxy_equal> uniq_map_t;

    typedef std::pair<const state_tba_proxy*, bool> state_ptr_bool_t;

    struct state_ptr_bool_hash:
      public std::unary_function<const state_ptr_bool_t&,
				 size_t>
    {
      size_t
      operator()(const state_ptr_bool_t& s) const
      {
	if (s.second)
	  return s.first->hash() ^ 12421;
	else
	  return s.first->hash();
      }
    };

    struct state_ptr_bool_equal:
      public std::binary_function<const state_ptr_bool_t&,
				  const state_ptr_bool_t&, bool>
    {
      bool
      operator()(const state_ptr_bool_t& left,
		 const state_ptr_bool_t& right) const
      {
	if (left.second != right.second)
	  return false;
	return left.first->compare(right.first) == 0;
      }
    };

    /// \brief Iterate over the successors of tgba_tba_proxy computed
    /// on the fly.
    class tgba_tba_proxy_succ_iterator: public tgba_succ_iterator
    {
      typedef tgba_tba_proxy::cycle_list list;
      typedef tgba_tba_proxy::cycle_list::const_iterator iterator;
    public:
      tgba_tba_proxy_succ_iterator(tgba::succ_iterable&& iterable,
				   iterator expected,
				   const list& cycle,
				   bdd the_acceptance_cond,
				   const tgba_tba_proxy* aut)
	: the_acceptance_cond_(the_acceptance_cond)
      {
	recycle(std::move(iterable), expected, cycle, aut);
      }

      void recycle(tgba::succ_iterable&& iterable,
		   iterator expected,
		   const list& cycle,
		   const tgba_tba_proxy* aut)
      {
	if (!transmap_.empty())
	  {
	    translist_.clear();
	    transmap_.clear();
	  }

	for (auto it: iterable)
	  {
	    bool accepting;
	    bdd acc = it->current_acceptance_conditions();
	    // As an extra optimization step, gather the acceptance
	    // conditions common to all outgoing transitions of the
	    // destination state.  We will later add these to "acc" to
	    // pretend they are already present on this transition.
	    state* odest = it->current_state();
	    bdd otheracc =
	      aut->common_acceptance_conditions_of_original_state(odest);

	    // A transition in the *EXPECTED acceptance set should
	    // be directed to the next acceptance set.  If the
	    // current transition is also in the next acceptance
	    // set, then go to the one after, etc.
	    //
	    // See Denis Oddoux's PhD thesis for a nice
	    // explanation (in French).
	    // @PhDThesis{	  oddoux.03.phd,
	    //   author	= {Denis Oddoux},
	    //   title	= {Utilisation des automates alternants pour un
	    // 		  model-checking efficace des logiques
	    //		  temporelles lin{\'e}aires.},
	    //   school	= {Universit{\'e}e Paris 7},
	    //   year	= {2003},
	    //   address= {Paris, France},
	    //   month	= {December}
	    // }
	    iterator next = expected;
	    // Consider both the current acceptance sets, and the
	    // acceptance sets common to the outgoing transition of
	    // the destination state.
	    acc |= otheracc;
	    while (next != cycle.end() && bdd_implies(*next, acc))
	      ++next;
	    if (next != cycle.end())
	      {
		accepting = false;
	      }
	    else
	      {
		// The transition is accepting.
		accepting = true;
		// Skip as much acceptance conditions as we can on our cycle.
		next = cycle.begin();
		while (next != expected && bdd_implies(*next, acc))
		  ++next;
	      }
	    state_tba_proxy* dest =
	      down_cast<state_tba_proxy*>(aut->create_state(odest, next));
	    // Is DEST already reachable with the same value of ACCEPTING?
	    state_ptr_bool_t key(dest, accepting);
	    transmap_t::iterator id = transmap_.find(key);
	    if (id == transmap_.end()) // No
	      {
		mapit_t pos =
		  transmap_.emplace(key, it->current_condition()).first;
		// Keep the order of the transitions in the
		// degeneralized automaton related to the order of the
		// transitions in the input automaton: in the past we
		// used to simply iterate over transmap_ in whatever
		// order the transitions were stored, but the output
		// would change between different runs depending on
		// the memory address of the states.  Now we keep the
		// order using translist_.  We only arrange it
		// slightly so that accepting transitions come first:
		// this way they are processed early during
		// emptiness-check.
		if (accepting)
		  translist_.push_front(pos);
		else
		  translist_.push_back(pos);
	      }
	    else // Yes, combine labels.
	      {
		id->second |= it->current_condition();
		dest->destroy();
	      }
	  }
      }

      virtual
      ~tgba_tba_proxy_succ_iterator()
      {
      }

      // iteration

      bool
      first()
      {
	it_ = translist_.begin();
	return it_ != translist_.end();
      }

      bool
      next()
      {
	++it_;
	return it_ != translist_.end();
      }

      bool
      done() const
      {
	return it_ == translist_.end();
      }

      // inspection

      state_tba_proxy*
      current_state() const
      {
	return (*it_)->first.first->clone();
      }

      bdd
      current_condition() const
      {
	return (*it_)->second;
      }

      bdd
      current_acceptance_conditions() const
      {
	return (*it_)->first.second ? the_acceptance_cond_ : bddfalse;
      }

    protected:
      const bdd the_acceptance_cond_;

      typedef std::unordered_map<state_ptr_bool_t, bdd,
				 state_ptr_bool_hash,
				 state_ptr_bool_equal> transmap_t;
      transmap_t transmap_;
      typedef transmap_t::const_iterator mapit_t;
      typedef std::list<mapit_t> translist_t;
      translist_t translist_;
      translist_t::const_iterator it_;
    };

  } // anonymous

  tgba_tba_proxy::tgba_tba_proxy(const tgba* a)
    : a_(a), uniq_map_(new uniq_map_t)
  {
    // We will use one acceptance condition for this automata.
    // Let's call it Acc[True].
    bdd_dict* d = get_dict();
    d->register_all_variables_of(a, this);
    d->unregister_all_typed_variables(bdd_dict::acc, this);

    int v = d
      ->register_acceptance_variable(ltl::constant::true_instance(), this);
    the_acceptance_cond_ = bdd_ithvar(v);

    if (a->number_of_acceptance_conditions() == 0)
      {
	acc_cycle_.push_front(bddtrue);
      }
    else
      {
	// Build a cycle of expected acceptance conditions.
	//
	// The order is arbitrary, but it turns out that using
	// push_back instead of push_front often gives better results
	// because acceptance conditions at the beginning if the
	// cycle are more often used in the automaton.  (This
	// surprising fact is probably related to the order in which we
	// declare the BDD variables during the translation.)
	bdd all = a_->all_acceptance_conditions();
	while (all != bddfalse)
	  {
	    bdd next = bdd_satone(all);
	    all -= next;
	    acc_cycle_.push_back(next);
	  }
      }
  }

  tgba_tba_proxy::~tgba_tba_proxy()
  {
    get_dict()->unregister_all_my_variables(this);

    accmap_t::const_iterator i = accmap_.begin();
    while (i != accmap_.end())
      {
	// Advance the iterator before deleting the key.
	const state* s = i->first;
	++i;
	s->destroy();
      }
    i = accmapu_.begin();
    while (i != accmapu_.end())
      {
	// Advance the iterator before deleting the key.
	const state* s = i->first;
	++i;
	s->destroy();
      }

    uniq_map_t* m = static_cast<uniq_map_t*>(uniq_map_);
    uniq_map_t::const_iterator j = m->begin();
    while (j != m->end())
      {
	const state* s = j->real_state();
	++j;
	s->destroy();
      }
    delete m;

    // This has already been destroyed.
    // Prevent destroying by tgba::~tgba.
    this->last_support_conditions_input_ = 0;
  }

  state*
  tgba_tba_proxy::create_state(state* s, cycle_list::const_iterator acc) const
  {
    uniq_map_t* m = static_cast<uniq_map_t*>(uniq_map_);
    state_tba_proxy st(s, acc);

    std::pair<uniq_map_t::iterator, bool> res = m->insert(st);
    if (!res.second)
      s->destroy();

    return const_cast<state_tba_proxy*>(&(*res.first));
  }



  state*
  tgba_tba_proxy::get_init_state() const
  {
    return create_state(a_->get_init_state(), acc_cycle_.begin());
  }

  tgba_succ_iterator*
  tgba_tba_proxy::succ_iter(const state* st) const
  {
    const state_tba_proxy* s = down_cast<const state_tba_proxy*>(st);
    assert(s);
    const state* rs = s->real_state();

    if (iter_cache_)
      {
	tgba_tba_proxy_succ_iterator* res =
	  down_cast<tgba_tba_proxy_succ_iterator*>(iter_cache_);
	res->recycle(a_->succ(rs),
		     s->acceptance_iterator(), acc_cycle_, this);
	iter_cache_ = nullptr;
	return res;
      }
    return new tgba_tba_proxy_succ_iterator(a_->succ(rs),
					    s->acceptance_iterator(),
					    acc_cycle_, the_acceptance_cond_,
					    this);
  }

  bdd
  tgba_tba_proxy::common_acceptance_conditions_of_original_state(const state* s)
    const
  {
    // Lookup cache
    accmap_t::const_iterator i = accmap_.find(s);
    if (i != accmap_.end())
      return i->second;

    bdd common = a_->all_acceptance_conditions();
    for (auto it: a_->succ(s))
      {
	common &= it->current_acceptance_conditions();
	if (common == bddfalse)
	  break;
      }

    // Populate cache
    accmap_[s->clone()] = common;
    return common;
  }

  bdd
  tgba_tba_proxy::union_acceptance_conditions_of_original_state(const state* s)
    const
  {
    // Lookup cache
    accmap_t::const_iterator i = accmapu_.find(s);
    if (i != accmapu_.end())
      return i->second;

    bdd common = bddfalse;
    for (auto it: a_->succ(s))
      common |= it->current_acceptance_conditions();

    // Populate cache
    accmapu_[s->clone()] = common;
    return common;
  }

  bdd_dict*
  tgba_tba_proxy::get_dict() const
  {
    return a_->get_dict();
  }

  std::string
  tgba_tba_proxy::format_state(const state* state) const
  {
    const state_tba_proxy* s = down_cast<const state_tba_proxy*>(state);
    assert(s);
    std::string a = bdd_format_accset(get_dict(), s->acceptance_cond());
    if (a != "")
      a = " " + a;
    return a_->format_state(s->real_state()) + a;
  }

  state*
  tgba_tba_proxy::project_state(const state* s, const tgba* t) const
  {
    const state_tba_proxy* s2 = down_cast<const state_tba_proxy*>(s);
    assert(s2);
    if (t == this)
      return s2->clone();
    return a_->project_state(s2->real_state(), t);
  }


  bdd
  tgba_tba_proxy::all_acceptance_conditions() const
  {
    return the_acceptance_cond_;
  }

  bdd
  tgba_tba_proxy::neg_acceptance_conditions() const
  {
    return !the_acceptance_cond_;
  }

  bdd
  tgba_tba_proxy::compute_support_conditions(const state* state) const
  {
    const state_tba_proxy* s =
      down_cast<const state_tba_proxy*>(state);
    assert(s);
    return a_->support_conditions(s->real_state());
  }

}
