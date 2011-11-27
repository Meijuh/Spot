// Copyright (C) 2010, 2011 Laboratoire de Recherche et Developpement
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

#include "ltlast/atomic_prop.hh"
#include "ltlast/constant.hh"
#include "tgba/formula2bdd.hh"
#include "misc/bddop.hh"
#include <cassert>
#include "ltlvisit/tostring.hh"
#include <iostream>
#include "tgba/bddprint.hh"
#include "tgbaalgos/gtec/nsheap.hh"
#include <stack>
#include "tgba2ta.hh"
#include "taalgos/statessetbuilder.hh"
#include "ta/tgbtaexplicit.hh"

using namespace std;

namespace spot
{

  ta_explicit*
  build_ta(ta_explicit* ta, bdd atomic_propositions_set_,
      bool artificial_initial_state_mode,
      bool artificial_livelock_accepting_state_mode, bool degeneralized)
  {

    std::stack<state_ta_explicit*> todo;
    const tgba* tgba_ = ta->get_tgba();

    // build Initial states set:
    state* tgba_init_state = tgba_->get_init_state();

    bdd tgba_condition = tgba_->support_conditions(tgba_init_state);

    bdd satone_tgba_condition;
    while ((satone_tgba_condition = bdd_satoneset(tgba_condition,
        atomic_propositions_set_, bddtrue)) != bddfalse)
      {
        tgba_condition -= satone_tgba_condition;
        state_ta_explicit* init_state;
        if (degeneralized)
          {
            init_state = new state_ta_explicit(tgba_init_state->clone(),
                satone_tgba_condition, true,
                ((tgba_sba_proxy*) tgba_)->state_is_accepting(tgba_init_state));
          }
        else
          {
            init_state = new state_ta_explicit(tgba_init_state->clone(),
                satone_tgba_condition, true, false);
          }

        state_ta_explicit* s = ta->add_state(init_state);
        assert(s == init_state);
        ta->add_to_initial_states_set(s);

        todo.push(init_state);
      }
    tgba_init_state->destroy();

    while (!todo.empty())
      {
        state_ta_explicit* source = todo.top();
        todo.pop();

        tgba_succ_iterator* tgba_succ_it = tgba_->succ_iter(
            source->get_tgba_state());
        for (tgba_succ_it->first(); !tgba_succ_it->done(); tgba_succ_it->next())
          {
            const state* tgba_state = tgba_succ_it->current_state();
            bdd tgba_condition = tgba_succ_it->current_condition();
            bdd tgba_acceptance_conditions =
                tgba_succ_it->current_acceptance_conditions();
            bdd satone_tgba_condition;
            while ((satone_tgba_condition = bdd_satoneset(tgba_condition,
                atomic_propositions_set_, bddtrue)) != bddfalse)
              {

                tgba_condition -= satone_tgba_condition;

                bdd all_props = bddtrue;
                bdd dest_condition;
                if (satone_tgba_condition == source->get_tgba_condition())
                  while ((dest_condition = bdd_satoneset(all_props,
                      atomic_propositions_set_, bddtrue)) != bddfalse)
                    {
                      all_props -= dest_condition;
                      state_ta_explicit* new_dest;
                      if (degeneralized)
                        {

                          new_dest = new state_ta_explicit(tgba_state->clone(),
                              dest_condition, false,
                              ((tgba_sba_proxy*) tgba_)->state_is_accepting(
                                  tgba_state));

                        }
                      else
                        {
                          new_dest = new state_ta_explicit(tgba_state->clone(),
                              dest_condition, false, false);

                        }
                      state_ta_explicit* dest = ta->add_state(new_dest);

                      if (dest != new_dest)
                        {
                          // the state dest already exists in the testing automata
                          new_dest->get_tgba_state()->destroy();
                          delete new_dest;
                        }
                      else
                        {
                          todo.push(dest);
                        }

                      ta->create_transition(source, bdd_setxor(
                          source->get_tgba_condition(),
                          dest->get_tgba_condition()),
                          tgba_acceptance_conditions, dest);

                    }

              }
            tgba_state->destroy();
          }
        delete tgba_succ_it;

      }

    compute_livelock_acceptance_states(ta);
    if (artificial_livelock_accepting_state_mode)
      {

        state_ta_explicit* artificial_livelock_accepting_state =
            new state_ta_explicit(ta->get_tgba()->get_init_state(), bddtrue,
                false, false, true, 0);

        add_artificial_livelock_accepting_state(ta,
            artificial_livelock_accepting_state);

      }

    return ta;

  }

  ta_explicit*
  tgba_to_ta(const tgba* tgba_, bdd atomic_propositions_set_,
      bool artificial_initial_state_mode,
      bool artificial_livelock_accepting_state_mode, bool degeneralized)
  {
    ta_explicit* ta;

    state* tgba_init_state = tgba_->get_init_state();
    if (artificial_initial_state_mode)
      {
        state_ta_explicit* ta_init_state = new state_ta_explicit(
            tgba_init_state->clone(), bddfalse, true);

        ta = new spot::ta_explicit(tgba_, tgba_->all_acceptance_conditions(),
            ta_init_state);
      }
    else
      {
        ta = new spot::ta_explicit(tgba_, tgba_->all_acceptance_conditions());
      }
    tgba_init_state->destroy();

    // build ta automata:
    build_ta(ta, atomic_propositions_set_, artificial_initial_state_mode,
        artificial_livelock_accepting_state_mode, degeneralized);
    return ta;
  }

  void
  add_artificial_livelock_accepting_state(ta_explicit* testing_automata,
      state_ta_explicit* artificial_livelock_accepting_state)
  {

    state_ta_explicit* artificial_livelock_accepting_state_added =
        testing_automata->add_state(artificial_livelock_accepting_state);

    // unique artificial_livelock_accepting_state
    assert(artificial_livelock_accepting_state_added
        == artificial_livelock_accepting_state);

    ta::states_set_t states_set = testing_automata->get_states_set();
    ta::states_set_t::iterator it;

    std::set<bdd, bdd_less_than>* conditions_to_livelock_accepting_states =
        new std::set<bdd, bdd_less_than>;

    for (it = states_set.begin(); it != states_set.end(); it++)
      {

        state_ta_explicit* source = static_cast<state_ta_explicit*> (*it);

        conditions_to_livelock_accepting_states->clear();

        state_ta_explicit::transitions* trans = source->get_transitions();
        state_ta_explicit::transitions::iterator it_trans;

        if (trans != 0)
          for (it_trans = trans->begin(); it_trans != trans->end();)
            {
              state_ta_explicit* dest = (*it_trans)->dest;

              state_ta_explicit::transitions* dest_trans =
                  (dest)->get_transitions();
              bool dest_trans_empty = dest_trans == 0 || dest_trans->empty();

              //TODO TA++
              if (dest->is_livelock_accepting_state()
                  && (!dest->is_accepting_state() || dest_trans_empty))
                {
                  conditions_to_livelock_accepting_states->insert(
                      (*it_trans)->condition);

                }

              //remove hole successors states

              if (dest_trans_empty)
                {
                  source->get_transitions((*it_trans)->condition)->remove(
                      *it_trans);
                  delete (*it_trans);
                  it_trans = trans->erase(it_trans);
                }
              else
                {
                  it_trans++;
                }
            }

        if (conditions_to_livelock_accepting_states != 0)
          {
            std::set<bdd, bdd_less_than>::iterator it_conditions;
            for (it_conditions
                = conditions_to_livelock_accepting_states->begin(); it_conditions
                != conditions_to_livelock_accepting_states->end(); it_conditions++)
              {

                testing_automata->create_transition(source, (*it_conditions),
                    bddfalse, artificial_livelock_accepting_state,true);

              }
          }

      }
    delete conditions_to_livelock_accepting_states;

  }

  namespace
  {
    typedef std::pair<spot::state*, tgba_succ_iterator*> pair_state_iter;
  }

  void
  compute_livelock_acceptance_states(ta_explicit* testing_automata)
  {
    // We use five main data in this algorithm:
    // * sscc: a stack of strongly stuttering-connected components (SSCC)
    scc_stack_ta sscc;

    // * arc, a stack of acceptance conditions between each of these SCC,
    std::stack<bdd> arc;

    // * h: a hash of all visited nodes, with their order,
    //   (it is called "Hash" in Couvreur's paper)
    numbered_state_heap* h =
        numbered_state_heap_hash_map_factory::instance()->build(); ///< Heap of visited states.

    // * num: the number of visited nodes.  Used to set the order of each
    //   visited node,
    int num = 0;

    // * todo: the depth-first search stack.  This holds pairs of the
    //   form (STATE, ITERATOR) where ITERATOR is a tgba_succ_iterator
    //   over the successors of STATE.  In our use, ITERATOR should
    //   always be freed when TODO is popped, but STATE should not because
    //   it is also used as a key in H.
    std::stack<pair_state_iter> todo;

    // * init: the set of the depth-first search initial states
    std::stack<state*> init_set;

    ta::states_set_t::const_iterator it;
    ta::states_set_t init_states = testing_automata->get_initial_states_set();
    for (it = init_states.begin(); it != init_states.end(); it++)
      {
        state* init_state = (*it);
        init_set.push(init_state);

      }

    while (!init_set.empty())
      {
        // Setup depth-first search from initial states.
          {
            state_ta_explicit* init =
                down_cast<state_ta_explicit*> (init_set.top());
            init_set.pop();
            state_ta_explicit* init_clone = init;
            numbered_state_heap::state_index_p h_init = h->find(init_clone);

            if (h_init.first)
              continue;

            h->insert(init_clone, ++num);
            sscc.push(num);
            arc.push(bddfalse);
            sscc.top().is_accepting
                = testing_automata->is_accepting_state(init);
            tgba_succ_iterator* iter = testing_automata->succ_iter(init);
            iter->first();
            todo.push(pair_state_iter(init, iter));

          }

        while (!todo.empty())
          {

            state* curr = todo.top().first;

            numbered_state_heap::state_index_p spi = h->find(curr);
            // If we have reached a dead component, ignore it.
            if (*spi.second == -1)
              {
                todo.pop();
                continue;
              }

            // We are looking at the next successor in SUCC.
            tgba_succ_iterator* succ = todo.top().second;

            // If there is no more successor, backtrack.
            if (succ->done())
              {
                // We have explored all successors of state CURR.

                // Backtrack TODO.
                todo.pop();

                // fill rem with any component removed,
                numbered_state_heap::state_index_p spi =
                    h->index(curr);
                assert(spi.first);

                sscc.rem().push_front(curr);

                // When backtracking the root of an SSCC, we must also
                // remove that SSCC from the ROOT stacks.  We must
                // discard from H all reachable states from this SSCC.
                assert(!sscc.empty());
                if (sscc.top().index == *spi.second)
                  {
                    // removing states
                    std::list<state*>::iterator i;
                    bool is_livelock_accepting_sscc = (sscc.rem().size() > 1)
                        && ((sscc.top().is_accepting) || (sscc.top().condition
                            == testing_automata->all_acceptance_conditions()));

                    for (i = sscc.rem().begin(); i != sscc.rem().end(); ++i)
                      {
                        numbered_state_heap::state_index_p spi = h->index(
                            (*i));
                        assert(spi.first->compare(*i) == 0);
                        assert(*spi.second != -1);
                        *spi.second = -1;
                        if (is_livelock_accepting_sscc)
                          {//if it is an accepting sscc
                            //add the state to G (=the livelock-accepting states set)

                            state_ta_explicit * livelock_accepting_state =
                                down_cast<state_ta_explicit*> (*i);

                            livelock_accepting_state->set_livelock_accepting_state(
                                true);
                          }

                      }

                    assert(!arc.empty());
                    sscc.pop();
                    arc.pop();

                  }

                // automata reduction
                testing_automata->delete_stuttering_and_hole_successors(curr);

                delete succ;
                // Do not delete CURR: it is a key in H.
                continue;
              }

            // Fetch the values destination state we are interested in...
            state* dest = succ->current_state();

            bdd acc_cond = succ->current_acceptance_conditions();
            // ... and point the iterator to the next successor, for
            // the next iteration.
            succ->next();
            // We do not need SUCC from now on.


            // Are we going to a new state through a stuttering transition?
            bool is_stuttering_transition =
                testing_automata->get_state_condition(curr)
                    == testing_automata->get_state_condition(dest);
            state* dest_clone = dest;
            spi = h->find(dest_clone);

            // Is this a new state?
            if (!spi.first)
              {
                if (!is_stuttering_transition)
                  {
                    init_set.push(dest);
                    dest_clone->destroy();
                    continue;
                  }

                // Number it, stack it, and register its successors
                // for later processing.
                h->insert(dest_clone, ++num);
                sscc.push(num);
                arc.push(acc_cond);
                sscc.top().is_accepting = testing_automata->is_accepting_state(
                    dest);

                tgba_succ_iterator* iter = testing_automata->succ_iter(dest);
                iter->first();
                todo.push(pair_state_iter(dest, iter));
                continue;
              }

            // If we have reached a dead component, ignore it.
            if (*spi.second == -1)
              continue;

            trace << "***compute_livelock_acceptance_states: CYCLE***"
                << std::endl;

            if (!curr->compare(dest))
              {
                state_ta_explicit * self_loop_state =
                    down_cast<state_ta_explicit*> (curr);
                assert(self_loop_state);

                if (testing_automata->is_accepting_state(self_loop_state)
                    || (acc_cond
                        == testing_automata->all_acceptance_conditions()))
                  self_loop_state->set_livelock_accepting_state(true);
                trace
                    << "***compute_livelock_acceptance_states: CYCLE: self_loop_state***"
                    << std::endl;

              }

            // Now this is the most interesting case.  We have reached a
            // state S1 which is already part of a non-dead SSCC.  Any such
            // non-dead SSCC has necessarily been crossed by our path to
            // this state: there is a state S2 in our path which belongs
            // to this SSCC too.  We are going to merge all states between
            // this S1 and S2 into this SSCC.
            //
            // This merge is easy to do because the order of the SSCC in
            // ROOT is ascending: we just have to merge all SSCCs from the
            // top of ROOT that have an index greater to the one of
            // the SSCC of S2 (called the "threshold").
            int threshold = *spi.second;
            std::list<state*> rem;
            bool acc = false;

            while (threshold < sscc.top().index)
              {
                assert(!sscc.empty());
                assert(!arc.empty());
                acc |= sscc.top().is_accepting;
                acc_cond |= sscc.top().condition;
                acc_cond |= arc.top();
                rem.splice(rem.end(), sscc.rem());
                sscc.pop();
                arc.pop();
              }

            // Note that we do not always have
            //  threshold == sscc.top().index
            // after this loop, the SSCC whose index is threshold might have
            // been merged with a lower SSCC.

            // Accumulate all acceptance conditions into the merged SSCC.
            sscc.top().is_accepting |= acc;
            sscc.top().condition |= acc_cond;

            sscc.rem().splice(sscc.rem().end(), rem);

          }

      }
    delete h;

  }

  tgbta_explicit*
  tgba_to_tgbta(const tgba* tgba_, bdd atomic_propositions_set_)
  {

    state* tgba_init_state = tgba_->get_init_state();
    state_ta_explicit* ta_init_state = new state_ta_explicit(
        tgba_init_state->clone(), bddfalse, true);
    tgba_init_state->destroy();

    tgbta_explicit* tgbta = new spot::tgbta_explicit(tgba_,
        tgba_->all_acceptance_conditions(), ta_init_state);

    // build ta automata:
    build_ta(tgbta, atomic_propositions_set_, true, true, false);

    trace << "***tgba_to_tgbta: POST build_ta***" << std::endl;

    // adapt a ta automata to build tgbta automata :
    ta::states_set_t states_set = tgbta->get_states_set();
    ta::states_set_t::iterator it;
    tgba_succ_iterator* initial_states_iter = tgbta->succ_iter(
        tgbta->get_artificial_initial_state());
    initial_states_iter->first();
    if (initial_states_iter->done())
      return tgbta;
    bdd first_state_condition = (initial_states_iter)->current_condition();
    delete initial_states_iter;

    bdd bdd_stutering_transition = bdd_setxor(first_state_condition,
        first_state_condition);

    for (it = states_set.begin(); it != states_set.end(); it++)
      {

        state_ta_explicit* state = static_cast<state_ta_explicit*> (*it);

        state_ta_explicit::transitions* trans = state->get_transitions();
        if (state->is_livelock_accepting_state())
          {

            bool trans_empty = (trans == 0 || trans->empty());
            if (trans_empty)
              {
                trace
                    << "***tgba_to_tgbta: PRE if (state->is_livelock_accepting_state()) ... create_transition ***"
                    << std::endl;
                tgbta->create_transition(state, bdd_stutering_transition,
                    tgbta->all_acceptance_conditions(), state);
                trace
                    << "***tgba_to_tgbta: POST if (state->is_livelock_accepting_state()) ... create_transition ***"
                    << std::endl;

              } else {
                  state->set_livelock_accepting_state(false);
              }
          }

        if (state->compare(tgbta->get_artificial_initial_state()))
          tgbta->create_transition(state, bdd_stutering_transition, bddfalse,
              state);

        trace << "***tgba_to_tgbta: POST create_transition ***" << std::endl;

      }

    return tgbta;

  }

}
