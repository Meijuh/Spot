// Copyright (C) 2010 Laboratoire de Recherche et Developpement
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
#include "sba2ta.hh"


using namespace std;

namespace spot
{

  ta*
  sba_to_ta(const tgba_sba_proxy* tgba_, bdd atomic_propositions_set_)
  {

    ta_explicit* ta = new spot::ta_explicit(tgba_);

    // build I set:
    bdd init_condition;
    bdd all_props = bddtrue;
    ta::states_set_t todo;

    while ((init_condition = bdd_satoneset(all_props, atomic_propositions_set_,
        bddtrue)) != bddfalse)
      {
        all_props -= init_condition;
        state_ta_explicit* init_state = new state_ta_explicit((tgba_->get_init_state()),
            init_condition, true);
        ta->add_initial_state(init_state);
        todo.insert(init_state);
      }

    while (!todo.empty())
      {
        ta::states_set_t::iterator todo_it = todo.begin();
        state_ta_explicit* source = dynamic_cast<state_ta_explicit*> (*todo_it);
        todo.erase(todo_it);

        tgba_succ_iterator* tgba_succ_it = tgba_->succ_iter(
            source->get_tgba_state());
        for (tgba_succ_it->first(); !tgba_succ_it->done(); tgba_succ_it->next())
          {
            const state* tgba_state = tgba_succ_it->current_state();
            bdd tgba_condition = tgba_succ_it->current_condition();
            bdd satone_tgba_condition;
            while ((satone_tgba_condition = bdd_satoneset(tgba_condition,
                atomic_propositions_set_, bddtrue)) != bddfalse)
              {

                tgba_condition -= satone_tgba_condition;
                state_ta_explicit* new_dest = new state_ta_explicit(tgba_state->clone(),
                    satone_tgba_condition, false, tgba_->state_is_accepting(
                        tgba_state));

                state_ta_explicit* dest = ta->add_state(new_dest);

                if (dest != new_dest)
                  {
                    // the state dest already exists in the testing automata
                    delete new_dest->get_tgba_state();
                    delete new_dest;
                  }
                else
                  {
                    todo.insert(dest);
                  }

                ta->create_transition(source, bdd_setxor(
                    source->get_tgba_condition(), dest->get_tgba_condition()),
                    dest);

              }
            delete tgba_state;
          }
        delete tgba_succ_it;

      }

    compute_livelock_acceptance_states(ta);

    ta->delete_stuttering_transitions();

    return ta;

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
    sscc_stack sscc;

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
    ta::states_set_t init_set;

    ta::states_set_t::const_iterator it;
    for (it = (testing_automata->get_initial_states_set())->begin(); it != (testing_automata->get_initial_states_set())->end(); it++)
      {
        state* init_state = (*it);
        init_set.insert(init_state);

      }

    while (!init_set.empty())
      {
        // Setup depth-first search from an initial state.
          {
            ta::states_set_t::iterator init_set_it = init_set.begin();
            state_ta_explicit* init = dynamic_cast<state_ta_explicit*> (*init_set_it);
            init_set.erase(init_set_it);
            state_ta_explicit* init_clone = init->clone();
            numbered_state_heap::state_index_p h_init = h->find(init_clone);

            if (h_init.first)
              continue;

            h->insert(init_clone, ++num);
            sscc.push(num);
            sscc.top().is_accepting = testing_automata->is_accepting_state(init);
            sscc.top().is_initial = testing_automata->is_initial_state(init);
            tgba_succ_iterator* iter = testing_automata->succ_iter(init);
            iter->first();
            todo.push(pair_state_iter(init, iter));

          }

        while (!todo.empty())
          {

            // We are looking at the next successor in SUCC.
            tgba_succ_iterator* succ = todo.top().second;

            state* curr = todo.top().first;

            // If there is no more successor, backtrack.
            if (succ->done())
              {
                // We have explored all successors of state CURR.

                // Backtrack TODO.
                todo.pop();

                // fill rem with any component removed,
                numbered_state_heap::state_index_p spi = h->index(curr->clone());
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
                    bool is_livelock_accepting_sscc = (sscc.top().is_accepting
                        && (sscc.rem().size() > 1));
                    for (i = sscc.rem().begin(); i != sscc.rem().end(); ++i)
                      {
                        numbered_state_heap::state_index_p spi = h->index((*i)->clone());
                        assert(spi.first->compare(*i)==0);
                        assert(*spi.second != -1);
                        *spi.second = -1;
                        if (is_livelock_accepting_sscc)
                          {//if it is an accepting sscc
                            //add the state to G (=the livelock-accepting states set)

                            state_ta_explicit * livelock_accepting_state =
                                dynamic_cast<state_ta_explicit*> (*i);

                            livelock_accepting_state->set_livelock_accepting_state(
                                true);

                          }

                        if (sscc.top().is_initial)
                          {//if it is an initial sscc
                            //add the state to I (=the initial states set)

                            state_ta_explicit * initial_state =
                                dynamic_cast<state_ta_explicit*> (*i);

                            testing_automata->add_initial_state(initial_state);
                          }
                      }

                    is_livelock_accepting_sscc = testing_automata->is_livelock_accepting_state(
                        *sscc.rem().begin());
                    sscc.pop();
                    if (is_livelock_accepting_sscc && !sscc.empty())
                      {
                        sscc.top().is_accepting = true;

                        state_ta_explicit * livelock_accepting_state =
                            dynamic_cast<state_ta_explicit*> (todo.top().first);
                        livelock_accepting_state->set_livelock_accepting_state(
                            true);

                      }
                    if (sscc.top().is_initial && !sscc.empty())
                      sscc.top().is_initial = true;
                  }

                delete succ;
                // Do not delete CURR: it is a key in H.
                continue;
              }

            // Fetch the values destination state we are interested in...
            state* dest = succ->current_state();

            // ... and point the iterator to the next successor, for
            // the next iteration.
            succ->next();
            // We do not need SUCC from now on.


            // Are we going to a new state through a stuttering transition?
            bool is_stuttering_transition = testing_automata->get_state_condition(curr)
                == testing_automata->get_state_condition(dest);
            state* dest_clone = dest->clone();
            numbered_state_heap::state_index_p spi = h->find(dest_clone);

            // Is this a new state?
            if (!spi.first)
              {
                if (!is_stuttering_transition)
                  {
                    init_set.insert(dest);
                    delete dest_clone;
                    continue;
                  }

                // Number it, stack it, and register its successors
                // for later processing.
                h->insert(dest_clone, ++num);
                sscc.push(num);
                sscc.top().is_accepting = testing_automata->is_accepting_state(dest);
                sscc.top().is_initial = testing_automata->is_initial_state(dest);
                tgba_succ_iterator* iter = testing_automata->succ_iter(dest);
                iter->first();
                todo.push(pair_state_iter(dest, iter));
                continue;
              }

            // If we have reached a dead component, ignore it.
            if (*spi.second == -1)
              continue;

            if (!curr->compare(dest))
              {
                state_ta_explicit * self_loop_state = dynamic_cast<state_ta_explicit*> (curr);

                if (testing_automata->is_accepting_state(self_loop_state))
                  self_loop_state->set_livelock_accepting_state(true);

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
            bool init = false;
            while (threshold < sscc.top().index)
              {
                assert(!sscc.empty());

                acc |= sscc.top().is_accepting;
                init |= sscc.top().is_initial;

                rem.splice(rem.end(), sscc.rem());
                sscc.pop();

              }
            // Note that we do not always have
            //  threshold == sscc.top().index
            // after this loop, the SSCC whose index is threshold might have
            // been merged with a lower SSCC.

            // Accumulate all acceptance conditions into the merged SSCC.
            sscc.top().is_accepting |= acc;
            sscc.top().is_initial |= init;

            sscc.rem().splice(sscc.rem().end(), rem);

          }

      }
    delete h;

  }

}
