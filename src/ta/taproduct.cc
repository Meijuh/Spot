// Copyright (C) 2010 Laboratoire de Recherche et Developpement
// de l Epita (LRDE).
//
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#include "taproduct.hh"
#include <cassert>
#include "misc/hashfunc.hh"

namespace spot
{

  ////////////////////////////////////////////////////////////
  // state_ta_product

  state_ta_product::state_ta_product(const state_ta_product& o) :
    state(), ta_state_(o.get_ta_state()), kripke_state_(
        o.get_kripke_state()->clone())
  {
  }

  state_ta_product::~state_ta_product()
  {
    //see ta_product::free_state() method
    kripke_state_->destroy();
  }

  int
  state_ta_product::compare(const state* other) const
  {
    const state_ta_product* o = down_cast<const state_ta_product*> (other);
    assert(o);
    int res = ta_state_->compare(o->get_ta_state());
    if (res != 0)
      return res;
    return kripke_state_->compare(o->get_kripke_state());
  }

  size_t
  state_ta_product::hash() const
  {
    // We assume that size_t is 32-bit wide.
    return wang32_hash(ta_state_->hash()) ^ wang32_hash(kripke_state_->hash());
  }

  state_ta_product*
  state_ta_product::clone() const
  {
    return new state_ta_product(*this);
  }

  ////////////////////////////////////////////////////////////
  // ta_succ_iterator_product
  ta_succ_iterator_product::ta_succ_iterator_product(const state_ta_product* s,
      const ta* t, const kripke* k) :
    source_(s), ta_(t), kripke_(k)
  {
    kripke_source_condition = kripke_->state_condition(s->get_kripke_state());

    kripke_succ_it_ = kripke_->succ_iter(s->get_kripke_state());
    kripke_current_dest_state = 0;
    ta_succ_it_ = 0;
    current_state_ = 0;
  }

  ta_succ_iterator_product::~ta_succ_iterator_product()
  {
    // ta_->free_state(current_state_);
    delete current_state_;
    current_state_ = 0;
    delete ta_succ_it_;
    delete kripke_succ_it_;
    if (kripke_current_dest_state != 0)
      kripke_current_dest_state->destroy();
  }

  void
  ta_succ_iterator_product::step_()
  {
    if (!ta_succ_it_->done())
      ta_succ_it_->next();
    if (ta_succ_it_->done())
      {
        delete ta_succ_it_;
        ta_succ_it_ = 0;
        next_kripke_dest();
      }
  }

  void
  ta_succ_iterator_product::next_kripke_dest()
  {
    if (!kripke_succ_it_)
      return;

    if (kripke_current_dest_state == 0)
      {
        kripke_succ_it_->first();
      }
    else
      {
        kripke_current_dest_state->destroy();
        kripke_current_dest_state = 0;
        kripke_succ_it_->next();
      }

    // If one of the two successor sets is empty initially, we reset
    // kripke_succ_it_, so that done() can detect this situation easily.  (We
    // choose to reset kripke_succ_it_ because this variable is already used by
    // done().)
    if (kripke_succ_it_->done())
      {
        delete kripke_succ_it_;
        kripke_succ_it_ = 0;
        return;
      }

    kripke_current_dest_state = kripke_succ_it_->current_state();
    bdd kripke_current_dest_condition = kripke_->state_condition(
        kripke_current_dest_state);
    is_stuttering_transition_ = (kripke_source_condition
        == kripke_current_dest_condition);
    if (is_stuttering_transition_)
      {
        current_condition_ = bddfalse;
      }
    else
      {
        current_condition_ = bdd_setxor(kripke_source_condition,
            kripke_current_dest_condition);
        ta_succ_it_ = ta_->succ_iter(source_->get_ta_state(),
            current_condition_);
        ta_succ_it_->first();
      }

  }

  void
  ta_succ_iterator_product::first()
  {

    next_kripke_dest();

    if (!done())
      next_non_stuttering_();
  }

  void
  ta_succ_iterator_product::next()
  {
    delete current_state_;
    current_state_ = 0;
    if (is_stuttering_transition())
      {
        next_kripke_dest();
      }
    else
      step_();

    if (!done())
      next_non_stuttering_();

  }

  void
  ta_succ_iterator_product::next_non_stuttering_()
  {

    while (!done())
      {

        if (is_stuttering_transition_)
          {
            //if stuttering transition, the TA automata stays in the same state
            current_state_ = new state_ta_product(source_->get_ta_state(),
                kripke_current_dest_state->clone());
            return;
          }

        if (!ta_succ_it_->done())
          {
            current_state_ = new state_ta_product(ta_succ_it_->current_state(),
                kripke_current_dest_state->clone());
            return;
          }

        step_();
      }
  }

  bool
  ta_succ_iterator_product::done() const
  {
    return !kripke_succ_it_ || kripke_succ_it_->done();
  }

  state_ta_product*
  ta_succ_iterator_product::current_state() const
  {
    //assert(!done());
    //if stuttering transition, the TA automata stays in the same state
    //    if (is_stuttering_transition())
    //      return new state_ta_product(source_->get_ta_state(),
    //          kripke_succ_it_->current_state());
    //
    //    return new state_ta_product(ta_succ_it_->current_state(),
    //        kripke_succ_it_->current_state());
    return current_state_->clone();
  }

  bool
  ta_succ_iterator_product::is_stuttering_transition() const
  {
    //    assert(!done());
    //    bdd kripke_source_condition = kripke_->state_condition(source_->get_kripke_state());
    //    state * kripke_succ_it_current_state = kripke_succ_it_->current_state();
    //    bdd kripke_current_dest_condition = kripke_->state_condition(kripke_succ_it_current_state);
    //    delete kripke_succ_it_current_state;

    return is_stuttering_transition_;
  }

  bdd
  ta_succ_iterator_product::current_condition() const
  {
    // assert(!done());
    //    bdd kripke_source_condition = kripke_->state_condition(source_->get_kripke_state());
    //    state * kripke_succ_it_current_state = kripke_succ_it_->current_state();
    //    bdd kripke_current_dest_condition = kripke_->state_condition(kripke_succ_it_current_state);
    //    delete kripke_succ_it_current_state;
    //    return bdd_setxor(kripke_source_condition, kripke_current_dest_condition);

    return current_condition_;
  }

  ////////////////////////////////////////////////////////////
  // ta_product


  ta_product::ta_product(const ta* testing_automata,
      const kripke* kripke_structure) :
    dict_(testing_automata->get_dict()), ta_(testing_automata), kripke_(
        kripke_structure)
  {
    assert(dict_ == kripke_structure->get_dict());
    dict_->register_all_variables_of(&ta_, this);
    dict_->register_all_variables_of(&kripke_, this);

  }

  ta_product::~ta_product()
  {
    dict_->unregister_all_my_variables(this);
  }

  const ta::states_set_t
  ta_product::get_initial_states_set() const
  {
    //build initial states set

    ta::states_set_t ta_init_states_set;
    ta::states_set_t::const_iterator it;

    ta::states_set_t initial_states_set;
    state* kripke_init_state = kripke_->get_init_state();
    bdd kripke_init_state_condition = kripke_->state_condition(
        kripke_init_state);

    spot::state* artificial_initial_state = ta_->get_artificial_initial_state();

    if (artificial_initial_state != 0)
      {
        ta_succ_iterator* ta_init_it_ = ta_->succ_iter(
            artificial_initial_state, kripke_init_state_condition);
        for (ta_init_it_->first(); !ta_init_it_->done(); ta_init_it_->next())
          {
            ta_init_states_set.insert(ta_init_it_->current_state());
          }
        delete ta_init_it_;

      }
    else
      {
        ta_init_states_set = ta_->get_initial_states_set();
      }

    for (it = ta_init_states_set.begin(); it != ta_init_states_set.end(); it++)
      {

        if ((artificial_initial_state != 0) || (kripke_init_state_condition
            == ta_->get_state_condition(*it)))
          {
            state_ta_product* stp = new state_ta_product((*it),
                kripke_init_state->clone());

            initial_states_set.insert(stp);
          }

      }

    kripke_init_state->destroy();
    return initial_states_set;
  }

  ta_succ_iterator_product*
  ta_product::succ_iter(const state* s) const
  {
    const state_ta_product* stp = down_cast<const state_ta_product*> (s);
    assert(s);

    return new ta_succ_iterator_product(stp, ta_, kripke_);
  }

  bdd_dict*
  ta_product::get_dict() const
  {
    return dict_;
  }

  std::string
  ta_product::format_state(const state* state) const
  {
    const state_ta_product* s = down_cast<const state_ta_product*> (state);
    assert(s);
    return kripke_->format_state(s->get_kripke_state()) + " * \n"
        + ta_->format_state(s->get_ta_state());
  }

  bool
  ta_product::is_accepting_state(const spot::state* s) const
  {
    const state_ta_product* stp = down_cast<const state_ta_product*> (s);
    assert(stp);

    return ta_->is_accepting_state(stp->get_ta_state());
  }

  bool
  ta_product::is_livelock_accepting_state(const spot::state* s) const
  {
    const state_ta_product* stp = down_cast<const state_ta_product*> (s);
    assert(stp);

    return ta_->is_livelock_accepting_state(stp->get_ta_state());
  }

  spot::state*
  ta_product::get_artificial_initial_state() const
  {
    return 0;
  }

  //TODO BUG FIX
  bool
  ta_product::is_initial_state(const spot::state* s) const
  {
    const state_ta_product* stp = down_cast<const state_ta_product*> (s);
    assert(stp);

    state* ta_s = stp->get_ta_state();
    state* kr_s = stp->get_kripke_state();

    return (ta_->is_initial_state(ta_s))
        && ((kripke_->get_init_state())->compare(kr_s) == 0)
        && ((kripke_->state_condition(kr_s))
            == (ta_->get_state_condition(ta_s)));
  }

  bool
  ta_product::is_hole_state_in_ta_component(const spot::state* s) const
  {
    const state_ta_product* stp = down_cast<const state_ta_product*> (s);
    ta_succ_iterator* ta_succ_iter = get_ta()->succ_iter(stp->get_ta_state());
    bool is_hole_state = ta_succ_iter->done();
    delete ta_succ_iter;
    return is_hole_state;
  }

  bdd
  ta_product::get_state_condition(const spot::state* s) const
  {
    const state_ta_product* stp = down_cast<const state_ta_product*> (s);
    assert(stp);
    state* ta_s = stp->get_ta_state();
    return ta_->get_state_condition(ta_s);
  }

  void
  ta_product::free_state(const spot::state* s) const
  {

    const state_ta_product* stp = down_cast<const state_ta_product*> (s);
    assert(stp);
    ta_->free_state(stp->get_ta_state());
    delete stp;

  }

}
