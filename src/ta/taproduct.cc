// Copykripke_structure (C) 2010 Laboratoire de Recherche et Developpement
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
    delete kripke_state_;
  }

  int
  state_ta_product::compare(const state* other) const
  {
    const state_ta_product* o = dynamic_cast<const state_ta_product*> (other);
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
    kripke_succ_it_ = k->succ_iter(s->get_kripke_state());
    current_state_ = 0;
  }

  ta_succ_iterator_product::~ta_succ_iterator_product()
  {
    // ta_->free_state(current_state_);
    delete current_state_;
    current_state_ = 0;
    delete ta_succ_it_;
    delete kripke_succ_it_;
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
        kripke_succ_it_->next();
      }
  }

  void
  ta_succ_iterator_product::first()
  {
    if (!kripke_succ_it_)
      return;

    ta_succ_it_ = 0;
    kripke_succ_it_->first();
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

    next_non_stuttering_();
  }

  void
  ta_succ_iterator_product::next()
  {
    delete current_state_;
    current_state_ = 0;
    if (is_stuttering_transition())
      {
        ta_succ_it_ = 0;
        kripke_succ_it_->next();
      }
    else
      step_();

    if (!done())
      next_non_stuttering_();
  }

  void
  ta_succ_iterator_product::next_non_stuttering_()
  {

    bdd sc = kripke_->state_condition(source_->get_kripke_state());

    while (!done())
      {
        state * kripke_succ_it_current_state = kripke_succ_it_->current_state();
        bdd dc = kripke_->state_condition(kripke_succ_it_current_state);

        is_stuttering_transition_ = (sc == dc);
        if (is_stuttering_transition_)
          {
            //if stuttering transition, the TA automata stays in the same state
            current_state_ = new state_ta_product(source_->get_ta_state(),
                kripke_succ_it_current_state);
            current_condition_ = bddtrue;
            return;
          }

        if (ta_succ_it_ == 0){
            current_condition_ = bdd_setxor(sc, dc);
            ta_succ_it_ = ta_->succ_iter(source_->get_ta_state(), current_condition_);
            ta_succ_it_->first();
        }

        if (!ta_succ_it_->done())
          {
            current_state_ = new state_ta_product(ta_succ_it_->current_state(),
                kripke_succ_it_current_state);
            return;
          }

        delete kripke_succ_it_current_state;
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
    //    bdd sc = kripke_->state_condition(source_->get_kripke_state());
    //    state * kripke_succ_it_current_state = kripke_succ_it_->current_state();
    //    bdd dc = kripke_->state_condition(kripke_succ_it_current_state);
    //    delete kripke_succ_it_current_state;

    return is_stuttering_transition_;
  }

  bdd
  ta_succ_iterator_product::current_condition() const
  {
    // assert(!done());
    //    bdd sc = kripke_->state_condition(source_->get_kripke_state());
    //    state * kripke_succ_it_current_state = kripke_succ_it_->current_state();
    //    bdd dc = kripke_->state_condition(kripke_succ_it_current_state);
    //    delete kripke_succ_it_current_state;
    //    return bdd_setxor(sc, dc);

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

    const ta::states_set_t ta_init_states_set = ta_->get_initial_states_set();
    ta::states_set_t::const_iterator it;

    ta::states_set_t initial_states_set;

    for (it = ta_init_states_set.begin(); it != ta_init_states_set.end(); it++)
      {
        state* kripke_init_state = kripke_->get_init_state();
        if ((kripke_->state_condition(kripke_init_state))
            == (ta_->get_state_condition(*it)))
          {
            state_ta_product* stp = new state_ta_product((*it),
                kripke_init_state);

            initial_states_set.insert(stp);
          }
        else
          {
            delete kripke_init_state;
          }

      }

    return initial_states_set;
  }

  ta_succ_iterator_product*
  ta_product::succ_iter(const state* s) const
  {
    const state_ta_product* stp = dynamic_cast<const state_ta_product*> (s);
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
    const state_ta_product* s = dynamic_cast<const state_ta_product*> (state);
    assert(s);
    return kripke_->format_state(s->get_kripke_state()) + " * \n"
        + ta_->format_state(s->get_ta_state());
  }

  bool
  ta_product::is_accepting_state(const spot::state* s) const
  {
    const state_ta_product* stp = dynamic_cast<const state_ta_product*> (s);

    return ta_->is_accepting_state(stp->get_ta_state());
  }

  bool
  ta_product::is_livelock_accepting_state(const spot::state* s) const
  {
    const state_ta_product* stp = dynamic_cast<const state_ta_product*> (s);

    return ta_->is_livelock_accepting_state(stp->get_ta_state());
  }

  bool
  ta_product::is_initial_state(const spot::state* s) const
  {
    const state_ta_product* stp = dynamic_cast<const state_ta_product*> (s);

    state* ta_s = stp->get_ta_state();
    state* kr_s = stp->get_kripke_state();

    return (ta_->is_initial_state(ta_s))
        && ((kripke_->get_init_state())->compare(kr_s) == 0)
        && ((kripke_->state_condition(kr_s))
            == (ta_->get_state_condition(ta_s)));
  }

  bdd
  ta_product::get_state_condition(const spot::state* s) const
  {
    const state_ta_product* stp = dynamic_cast<const state_ta_product*> (s);
    state* ta_s = stp->get_ta_state();
    return ta_->get_state_condition(ta_s);
  }

  void
  ta_product::free_state(const spot::state* s) const
  {

    const state_ta_product* stp = dynamic_cast<const state_ta_product*> (s);
    ta_->free_state(stp->get_ta_state());
    delete stp;

  }

}
