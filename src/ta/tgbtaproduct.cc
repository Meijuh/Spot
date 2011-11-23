// Copyright (C) 2012 Laboratoire de Recherche et Developpement
// de l Epita (LRDE).
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


//#define TRACE

#include <iostream>
#ifdef TRACE
#define trace std::clog
#else
#define trace while (0) std::clog
#endif

#include "tgbtaproduct.hh"
#include <string>
#include <cassert>
#include "misc/hashfunc.hh"
#include "kripke/kripke.hh"

namespace spot
{

  ////////////////////////////////////////////////////////////
  // tgbta_succ_iterator_product


  ////////////////////////////////////////////////////////////
  // tgbta_product

  tgbta_product::tgbta_product(const kripke* left, const tgbta* right) :
    tgba_product(left, right)
  {
  }

  state*
  tgbta_product::get_init_state() const
  {
    fixed_size_pool* p = const_cast<fixed_size_pool*> (&pool_);
    return new (p->allocate()) state_product(left_->get_init_state(),
        right_->get_init_state(), p);
  }

  tgba_succ_iterator*
  tgbta_product::succ_iter(const state* local_state, const state* global_state,
      const tgba* global_automaton) const
  {
    const state_product* s = down_cast<const state_product*> (local_state);
    assert(s);

    fixed_size_pool* p = const_cast<fixed_size_pool*> (&pool_);

    return new tgbta_succ_iterator_product(s, (kripke*) left_,
        (tgbta *) right_, p);
  }

  ////////////////////////////////////////////////////////////
  // tgbtgbta_succ_iterator_product
  tgbta_succ_iterator_product::tgbta_succ_iterator_product(
      const state_product* s, const kripke* k, const tgbta* t,
      fixed_size_pool* pool) :
    source_(s), tgbta_(t), kripke_(k), pool_(pool)
  {

    state * tgbta_init_state = tgbta_->get_init_state();
    if ((s->right())->compare(tgbta_init_state) == 0)
      source_ = 0;

    if (source_ == 0)
      {
        kripke_succ_it_ = 0;
        kripke_current_dest_state = kripke_->get_init_state();
        current_condition_
            = kripke_->state_condition(kripke_current_dest_state);
        tgbta_succ_it_ = tgbta_->succ_iter_by_changeset(
            tgbta_init_state, current_condition_);
        tgbta_succ_it_->first();
        trace
          << "*** tgbta_succ_it_->done() = ***" << tgbta_succ_it_->done()
              << std::endl;

      }
    else
      {
        kripke_source_condition = kripke_->state_condition(s->left());
        kripke_succ_it_ = kripke_->succ_iter(s->left());
        kripke_current_dest_state = 0;
        tgbta_succ_it_ = 0;
      }

    tgbta_init_state->destroy();
    current_state_ = 0;
  }

  tgbta_succ_iterator_product::~tgbta_succ_iterator_product()
  {
    // ta_->free_state(current_state_);
    if (current_state_ != 0)
      current_state_->destroy();
    current_state_ = 0;
    delete tgbta_succ_it_;
    delete kripke_succ_it_;
    if (kripke_current_dest_state != 0)
      kripke_current_dest_state->destroy();
  }

  void
  tgbta_succ_iterator_product::step_()
  {
    if (!tgbta_succ_it_->done())
      tgbta_succ_it_->next();
    if (tgbta_succ_it_->done())
      {
        delete tgbta_succ_it_;
        tgbta_succ_it_ = 0;
        next_kripke_dest();
      }
  }

  void
  tgbta_succ_iterator_product::next_kripke_dest()
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

    current_condition_ = bdd_setxor(kripke_source_condition,
        kripke_current_dest_condition);
    tgbta_succ_it_ = tgbta_->succ_iter_by_changeset(source_->right(),
        current_condition_);
    tgbta_succ_it_->first();

  }

  void
  tgbta_succ_iterator_product::first()
  {

    next_kripke_dest();
    trace
      << "*** first() .... if(done()) = ***" << done() << std::endl;
    if (!done())
      find_next_succ_();

  }

  void
  tgbta_succ_iterator_product::next()
  {
    current_state_->destroy();
    current_state_ = 0;

    step_();

    trace
      << "*** next() .... if(done()) = ***" << done() << std::endl;

    if (!done())
      find_next_succ_();

  }

  void
  tgbta_succ_iterator_product::find_next_succ_()
  {

    while (!done())
      {
        if (!tgbta_succ_it_->done())
          {
            current_state_ = new (pool_->allocate()) state_product(
                kripke_current_dest_state->clone(),
                tgbta_succ_it_->current_state(), pool_);
            current_acceptance_conditions_
                = tgbta_succ_it_->current_acceptance_conditions();
            return;
          }

        step_();
      }
  }

  bool
  tgbta_succ_iterator_product::done() const
  {
    if (source_ == 0)
      {
        return !tgbta_succ_it_ || tgbta_succ_it_->done();
      }
    else
      {
        return !kripke_succ_it_ || kripke_succ_it_->done();
      }

  }

  state_product*
  tgbta_succ_iterator_product::current_state() const
  {
    trace
      << "*** current_state() .... if(done()) = ***" << done() << std::endl;
    return current_state_->clone();
  }

  bdd
  tgbta_succ_iterator_product::current_condition() const
  {
    return current_condition_;
  }

  bdd
  tgbta_succ_iterator_product::current_acceptance_conditions() const
  {
    return current_acceptance_conditions_;
  }

}
