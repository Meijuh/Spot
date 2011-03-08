// Copyright (C) 2010, 2011 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#ifdef TRACE
#  define trace std::cerr
#else
#  define trace while (0) std::cerr
#endif

#include <set>
#include <list>
#include <sstream>
#include "minimize.hh"
#include "ltlast/allnodes.hh"
#include "misc/hash.hh"
#include "misc/bddlt.hh"
#include "ta/taproduct.hh"
#include "taalgos/statessetbuilder.hh"
#include "tgba/tgbaexplicit.hh"

namespace spot
{
  typedef Sgi::hash_set<const state*, state_ptr_hash, state_ptr_equal> hash_set;
  typedef Sgi::hash_map<const state*, unsigned, state_ptr_hash, state_ptr_equal>
      hash_map;

  namespace
  {
    static std::ostream&
    dump_hash_set(const hash_set* hs, const ta* aut, std::ostream& out)
    {
      out << "{";
      const char* sep = "";
      for (hash_set::const_iterator i = hs->begin(); i != hs->end(); ++i)
        {
          out << sep << aut->format_state(*i);
          sep = ", ";
        }
      out << "}";
      return out;
    }

    static std::string
    format_hash_set(const hash_set* hs, const ta* aut)
    {
      std::ostringstream s;
      dump_hash_set(hs, aut, s);
      return s.str();
    }
  }

  // From the base automaton and the list of sets, build the minimal
  // tgbaulting automaton
  ta*
  build_result(const ta* a, std::list<hash_set*>& sets)
  {
    tgba_explicit_number* tgba = new tgba_explicit_number(a->get_dict());
    ta_explicit* ta = new ta_explicit(tgba);

    // For each set, create a state in the tgbaulting automaton.
    // For a state s, state_num[s] is the number of the state in the minimal
    // automaton.
    hash_map state_num;
    std::list<hash_set*>::iterator sit;
    unsigned num = 0;
    for (sit = sets.begin(); sit != sets.end(); ++sit)
      {
        hash_set::iterator hit;
        hash_set* h = *sit;
        for (hit = h->begin(); hit != h->end(); ++hit)
          state_num[*hit] = num;
        ++num;
      }

    // For each transition in the initial automaton, add the corresponding
    // transition in ta.

    for (sit = sets.begin(); sit != sets.end(); ++sit)
      {
        hash_set::iterator hit;
        hash_set* h = *sit;
        hit = h->begin();
        const state* src = *hit;
        unsigned src_num = state_num[src];

        state* tgba_state = new state_explicit(tgba->add_state(src_num));
        bdd tgba_condition = bddtrue;
        bool is_initial_state = a->is_initial_state(src);
        if (is_initial_state)
          tgba_condition = a->get_state_condition(src);
        bool is_accepting_state = a->is_accepting_state(src);
        bool is_livelock_accepting_state = a->is_livelock_accepting_state(src);

        state_ta_explicit* new_src = new state_ta_explicit(tgba_state,
            tgba_condition, is_initial_state, is_accepting_state,
            is_livelock_accepting_state);

        state_ta_explicit* ta_src = ta->add_state(new_src);

        if (ta_src != new_src)
          {
            delete new_src;
            delete tgba_state;
          }
        else if (is_initial_state)
          ta->add_to_initial_states_set(new_src);

        ta_succ_iterator* succit = a->succ_iter(src);

        for (succit->first(); !succit->done(); succit->next())
          {
            const state* dst = succit->current_state();
            hash_map::const_iterator i = state_num.find(dst);

            if (i == state_num.end()) // Ignore useless destinations.
              continue;

            state* tgba_state = new state_explicit(tgba->add_state(i->second));
            bdd tgba_condition = bddtrue;
            is_initial_state = a->is_initial_state(dst);
            if (is_initial_state)
              tgba_condition = a->get_state_condition(dst);
            bool is_accepting_state = a->is_accepting_state(dst);
            bool is_livelock_accepting_state = a->is_livelock_accepting_state(
                dst);

            state_ta_explicit* new_dst = new state_ta_explicit(tgba_state,
                tgba_condition, is_initial_state, is_accepting_state,
                is_livelock_accepting_state);

            state_ta_explicit* ta_dst = ta->add_state(new_dst);

            if (ta_dst != new_dst) {
                delete new_dst;
                delete tgba_state;
              }
            else if (is_initial_state)
              ta->add_to_initial_states_set(new_dst);

            ta->create_transition(ta_src, succit->current_condition(), ta_dst);

          }
        delete succit;
      }

    return ta;
  }

  ta*
  minimize_ta(const ta* ta_)
  {

    typedef std::list<hash_set*> partition_t;
    partition_t cur_run;
    partition_t next_run;

    // The list of equivalent states.
    partition_t done;

    std::set<const state*> states_set = get_states_set(ta_);

    // livelock acceptance states
    hash_set* G = new hash_set;

    // Buchi acceptance states
    hash_set* F = new hash_set;

    // Buchi and livelock acceptance states
    hash_set* G_F = new hash_set;

    // the other states (non initial and not in G, F and G_F)
    hash_set* S = new hash_set;

    std::set<const state*>::iterator it;

    for (it = states_set.begin(); it != states_set.end(); it++)
      {
        const state* s = (*it);

        if (ta_->is_initial_state(s))
          {
            hash_set* i = new hash_set;
            i->insert(s);
            done.push_back(i);
          }
        else if (ta_->is_livelock_accepting_state(s)
            && ta_->is_accepting_state(s))
          {
            G_F->insert(s);
          }
        else if (ta_->is_accepting_state(s))
          {
            F->insert(s);
          }

        else if (ta_->is_livelock_accepting_state(s))
          {
            G->insert(s);
          }
        else
          {
            S->insert(s);
          }

      }

    hash_map state_set_map;

    // Size of ta_
    unsigned size = states_set.size();
    // Use bdd variables to number sets.  set_num is the first variable
    // available.
    unsigned set_num = ta_->get_dict()->register_anonymous_variables(size, ta_);

    std::set<int> free_var;
    for (unsigned i = set_num; i < set_num + size; ++i)
      free_var.insert(i);
    std::map<int, int> used_var;

    if (!G->empty())
      {
        unsigned s = G->size();
        used_var[set_num] = s;
        free_var.erase(set_num);
        if (s > 1)
          cur_run.push_back(G);
        else
          done.push_back(G);
        for (hash_set::const_iterator i = G->begin(); i != G->end(); ++i)
          state_set_map[*i] = set_num;

      }
    else
      delete G;

    if (!F->empty())
      {
        unsigned s = F->size();
        unsigned num = set_num + 1;
        used_var[num] = s;
        free_var.erase(num);
        if (s > 1)
          cur_run.push_back(F);
        else
          done.push_back(F);
        for (hash_set::const_iterator i = F->begin(); i != F->end(); ++i)
          state_set_map[*i] = num;
      }
    else
      delete F;

    if (!G_F->empty())
      {
        unsigned s = G_F->size();
        unsigned num = set_num + 2;
        used_var[num] = s;
        free_var.erase(num);
        if (s > 1)
          cur_run.push_back(G_F);
        else
          done.push_back(G_F);
        for (hash_set::const_iterator i = G_F->begin(); i != G_F->end(); ++i)
          state_set_map[*i] = num;
      }
    else
      delete G_F;

    if (!S->empty())
      {
        unsigned s = S->size();
        unsigned num = set_num + 3;
        used_var[num] = s;
        free_var.erase(num);
        if (s > 1)
          cur_run.push_back(S);
        else
          done.push_back(S);
        for (hash_set::const_iterator i = S->begin(); i != S->end(); ++i)
          state_set_map[*i] = num;
      }
    else
      delete S;

    // A bdd_states_map is a list of formulae (in a BDD form) associated with a
    // destination set of states.
    typedef std::map<bdd, hash_set*, bdd_less_than> bdd_states_map;

    bool did_split = true;

    while (did_split)
      {
        did_split = false;
        while (!cur_run.empty())
          {
            // Get a set to process.
            hash_set* cur = cur_run.front();
            cur_run.pop_front();

            trace
              << "processing " << format_hash_set(cur, ta_) << std::endl;

            hash_set::iterator hi;
            bdd_states_map bdd_map;
            for (hi = cur->begin(); hi != cur->end(); ++hi)
              {
                const state* src = *hi;
                bdd f = bddfalse;
                ta_succ_iterator* si = ta_->succ_iter(src);
                for (si->first(); !si->done(); si->next())
                  {
                    const state* dst = si->current_state();
                    hash_map::const_iterator i = state_set_map.find(dst);

                    if (i == state_set_map.end())
                      // The destination state is not in our
                      // partition.  This can happen if the initial
                      // FINAL and NON_FINAL supplied to the algorithm
                      // do not cover the whole automaton (because we
                      // want to ignore some useless states).  Simply
                      // ignore these states here.
                      continue;
                    f |= (bdd_ithvar(i->second) & si->current_condition());
                  }
                delete si;

                // Have we already seen this formula ?
                bdd_states_map::iterator bsi = bdd_map.find(f);
                if (bsi == bdd_map.end())
                  {
                    // No, create a new set.
                    hash_set* new_set = new hash_set;
                    new_set->insert(src);
                    bdd_map[f] = new_set;
                  }
                else
                  {
                    // Yes, add the current state to the set.
                    bsi->second->insert(src);
                  }
              }

            bdd_states_map::iterator bsi = bdd_map.begin();
            if (bdd_map.size() == 1)
              {
                // The set was not split.
                trace
                  << "set " << format_hash_set(bsi->second, ta_)
                      << " was not split" << std::endl;
                next_run.push_back(bsi->second);
              }
            else
              {
                for (; bsi != bdd_map.end(); ++bsi)
                  {
                    hash_set* set = bsi->second;
                    // Free the number associated to these states.
                    unsigned num = state_set_map[*set->begin()];
                    assert(used_var.find(num) != used_var.end());
                    unsigned left = (used_var[num] -= set->size());
                    // Make sure LEFT does not become negative (hence bigger
                    // than SIZE when read as unsigned)
                    assert(left < size);
                    if (left == 0)
                      {
                        used_var.erase(num);
                        free_var.insert(num);
                      }
                    // Pick a free number
                    assert(!free_var.empty());
                    num = *free_var.begin();
                    free_var.erase(free_var.begin());
                    used_var[num] = set->size();
                    for (hash_set::iterator hit = set->begin(); hit
                        != set->end(); ++hit)
                      state_set_map[*hit] = num;
                    // Trivial sets can't be splitted any further.
                    if (set->size() == 1)
                      {
                        trace
                          << "set " << format_hash_set(set, ta_)
                              << " is minimal" << std::endl;
                        done.push_back(set);
                      }
                    else
                      {
                        did_split = true;
                        trace
                          << "set " << format_hash_set(set, ta_)
                              << " should be processed further" << std::endl;
                        next_run.push_back(set);
                      }
                  }
              }
            delete cur;
          }
        if (did_split)
          trace
            << "splitting did occur during this pass." << std::endl;
        //elsetrace << "splitting did not occur during this pass." << std::endl;
        std::swap(cur_run, next_run);
      }

    done.splice(done.end(), cur_run);

#ifdef TRACE
    trace << "Final partition: ";
    for (partition_t::const_iterator i = done.begin(); i != done.end(); ++i)
    trace << format_hash_set(*i, ta_) << " ";
    trace << std::endl;
#endif

    // Build the tgbault.
    ta* res = build_result(ta_, done);

    // Free all the allocated memory.
    std::list<hash_set*>::iterator itdone;
    for (itdone = done.begin(); itdone != done.end(); ++itdone)
      delete *itdone;
    delete ta_;

    return res;
  }

}
