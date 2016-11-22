// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2011, 2012, 2013, 2014, 2015, 2016 Laboratoire de
// Recherche et Développement de l'Epita (LRDE).
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


//#define TRACE

#ifdef TRACE
#  define trace std::cerr
#else
#  define trace while (0) std::cerr
#endif

#include <queue>
#include <deque>
#include <set>
#include <list>
#include <vector>
#include <sstream>
#include <spot/twaalgos/minimize.hh>
#include <spot/misc/hash.hh>
#include <spot/misc/bddlt.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/powerset.hh>
#include <spot/twaalgos/gtec/gtec.hh>
#include <spot/twaalgos/strength.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/bfssteps.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/remfin.hh>

namespace spot
{
  // This is called hash_set for historical reason, but we need the
  // order inside hash_set to be deterministic.
  typedef std::set<const state*, state_ptr_less_than> hash_set;
  typedef state_map<unsigned> hash_map;

  namespace
  {
    static std::ostream&
    dump_hash_set(const hash_set* hs,
                  const const_twa_ptr& aut,
                  std::ostream& out)
    {
      out << '{';
      const char* sep = "";
      for (hash_set::const_iterator i = hs->begin(); i != hs->end(); ++i)
        {
          out << sep << aut->format_state(*i);
          sep = ", ";
        }
      out << '}';
      return out;
    }

    static std::string
    format_hash_set(const hash_set* hs, const_twa_ptr aut)
    {
      std::ostringstream s;
      dump_hash_set(hs, aut, s);
      return s.str();
    }

    // Find all states of an automaton.
    static void
    build_state_set(const const_twa_ptr& a, hash_set* seen)
    {
      std::queue<const state*> tovisit;
      // Perform breadth-first traversal.
      const state* init = a->get_init_state();
      tovisit.push(init);
      seen->insert(init);
      while (!tovisit.empty())
        {
          const state* src = tovisit.front();
          tovisit.pop();

          for (auto sit: a->succ(src))
            {
              const state* dst = sit->dst();
              // Is it a new state ?
              if (seen->find(dst) == seen->end())
                {
                  // Register the successor for later processing.
                  tovisit.push(dst);
                  seen->insert(dst);
                }
              else
                dst->destroy();
            }
        }
    }

    // From the base automaton and the list of sets, build the minimal
    // resulting automaton
    static twa_graph_ptr
    build_result(const const_twa_ptr& a,
                 std::list<hash_set*>& sets,
                 hash_set* final)
    {
      auto dict = a->get_dict();
      auto res = make_twa_graph(dict);
      res->copy_ap_of(a);
      res->prop_state_acc(true);

      // For each set, create a state in the resulting automaton.
      // For a state s, state_num[s] is the number of the state in the minimal
      // automaton.
      hash_map state_num;
      std::list<hash_set*>::iterator sit;
      for (sit = sets.begin(); sit != sets.end(); ++sit)
        {
          hash_set::iterator hit;
          hash_set* h = *sit;
          unsigned num = res->new_state();
          for (hit = h->begin(); hit != h->end(); ++hit)
            state_num[*hit] = num;
        }

      // For each transition in the initial automaton, add the corresponding
      // transition in res.

      if (!final->empty())
        res->set_buchi();

      for (sit = sets.begin(); sit != sets.end(); ++sit)
        {
          hash_set* h = *sit;

          // Pick one state.
          const state* src = *h->begin();
          unsigned src_num = state_num[src];
          bool accepting = (final->find(src) != final->end());

          // Connect it to all destinations.
          for (auto succit: a->succ(src))
            {
              const state* dst = succit->dst();
              hash_map::const_iterator i = state_num.find(dst);
              dst->destroy();
              if (i == state_num.end()) // Ignore useless destinations.
                continue;
              res->new_acc_edge(src_num, i->second,
                                succit->cond(), accepting);
            }
        }
      res->merge_edges();
      if (res->num_states() > 0)
        {
          const state* init_state = a->get_init_state();
          unsigned init_num = state_num[init_state];
          init_state->destroy();
          res->set_init_state(init_num);
        }
      return res;
    }

    struct wdba_search_acc_loop final : public bfs_steps
    {
      wdba_search_acc_loop(const const_twa_ptr& det_a,
                           unsigned scc_n, scc_info& sm,
                           power_map& pm, const state* dest)
        : bfs_steps(det_a), scc_n(scc_n), sm(sm), pm(pm), dest(dest)
      {
        seen(dest);
      }

      virtual const state*
      filter(const state* s) override
      {
        s = seen(s);
        if (sm.scc_of(std::static_pointer_cast<const twa_graph>(a_)
                      ->state_number(s)) != scc_n)
          return nullptr;
        return s;
      }

      virtual bool
      match(twa_run::step&, const state* to) override
      {
        return to == dest;
      }

      unsigned scc_n;
      scc_info& sm;
      power_map& pm;
      const state* dest;
      state_unicity_table seen;
    };


    bool
    wdba_scc_is_accepting(const const_twa_graph_ptr& det_a, unsigned scc_n,
                          const const_twa_graph_ptr& orig_a, scc_info& sm,
                          power_map& pm)
    {
      // Get some state from the SCC #n.
      const state* start = det_a->state_from_number(sm.one_state_of(scc_n));

      // Find a loop around START in SCC #n.
      wdba_search_acc_loop wsal(det_a, scc_n, sm, pm, start);
      twa_run::steps loop;
      const state* reached = wsal.search(start, loop);
      assert(reached == start);
      (void)reached;

      // Build an automaton representing this loop.
      auto loop_a = make_twa_graph(det_a->get_dict());
      twa_run::steps::const_iterator i;
      int loop_size = loop.size();
      loop_a->new_states(loop_size);
      int n;
      for (n = 1, i = loop.begin(); n < loop_size; ++n, ++i)
        {
          loop_a->new_edge(n - 1, n, i->label);
          i->s->destroy();
        }
      assert(i != loop.end());
      loop_a->new_edge(n - 1, 0, i->label);
      i->s->destroy();
      assert(++i == loop.end());

      loop_a->set_init_state(0U);

      // Check if the loop is accepting in the original automaton.
      bool accepting = false;

      // Iterate on each original state corresponding to start.
      const power_map::power_state& ps =
        pm.states_of(det_a->state_number(start));
      for (auto& s: ps)
        {
          // Construct a product between LOOP_A and ORIG_A starting in
          // S.  FIXME: This could be sped up a lot!
          if (!product(loop_a, orig_a, 0U, s)->is_empty())
            {
              accepting = true;
              break;
            }
        }

      return accepting;
    }

    static twa_graph_ptr minimize_dfa(const const_twa_graph_ptr& det_a,
                                      hash_set* final, hash_set* non_final)
    {
      typedef std::list<hash_set*> partition_t;
      partition_t cur_run;
      partition_t next_run;

      // The list of equivalent states.
      partition_t done;

      hash_map state_set_map;

      // Size of det_a
      unsigned size = final->size() + non_final->size();
      // Use bdd variables to number sets.  set_num is the first variable
      // available.
      unsigned set_num =
        det_a->get_dict()->register_anonymous_variables(size, det_a);

      std::set<int> free_var;
      for (unsigned i = set_num; i < set_num + size; ++i)
        free_var.insert(i);
      std::map<int, int> used_var;

      hash_set* final_copy;

      if (!final->empty())
        {
          unsigned s = final->size();
          used_var[set_num] = s;
          free_var.erase(set_num);
          if (s > 1)
            cur_run.emplace_back(final);
          else
            done.emplace_back(final);
          for (hash_set::const_iterator i = final->begin();
               i != final->end(); ++i)
            state_set_map[*i] = set_num;

          final_copy = new hash_set(*final);
        }
      else
        {
          final_copy = final;
        }

      if (!non_final->empty())
        {
          unsigned s = non_final->size();
          unsigned num = set_num + 1;
          used_var[num] = s;
          free_var.erase(num);
          if (s > 1)
            cur_run.emplace_back(non_final);
          else
            done.emplace_back(non_final);
          for (hash_set::const_iterator i = non_final->begin();
               i != non_final->end(); ++i)
            state_set_map[*i] = num;
        }
      else
        {
          delete non_final;
        }

      // A bdd_states_map is a list of formulae (in a BDD form)
      // associated with a destination set of states.
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

              trace << "processing " << format_hash_set(cur, det_a)
                    << std::endl;

              hash_set::iterator hi;
              bdd_states_map bdd_map;
              for (hi = cur->begin(); hi != cur->end(); ++hi)
                {
                  const state* src = *hi;
                  bdd f = bddfalse;
                  for (auto si: det_a->succ(src))
                    {
                      const state* dst = si->dst();
                      hash_map::const_iterator i = state_set_map.find(dst);
                      dst->destroy();
                      if (i == state_set_map.end())
                        // The destination state is not in our
                        // partition.  This can happen if the initial
                        // FINAL and NON_FINAL supplied to the algorithm
                        // do not cover the whole automaton (because we
                        // want to ignore some useless states).  Simply
                        // ignore these states here.
                        continue;
                      f |= (bdd_ithvar(i->second) & si->cond());
                    }

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
                  trace << "set " << format_hash_set(bsi->second, det_a)
                        << " was not split" << std::endl;
                  next_run.emplace_back(bsi->second);
                }
              else
                {
                  did_split = true;
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
                      for (hash_set::iterator hit = set->begin();
                           hit != set->end(); ++hit)
                        state_set_map[*hit] = num;
                      // Trivial sets can't be splitted any further.
                      if (set->size() == 1)
                        {
                          trace << "set " << format_hash_set(set, det_a)
                                << " is minimal" << std::endl;
                          done.emplace_back(set);
                        }
                      else
                        {
                          trace << "set " << format_hash_set(set, det_a)
                                << " should be processed further" << std::endl;
                          next_run.emplace_back(set);
                        }
                    }
                }
              delete cur;
            }
          if (did_split)
            trace << "splitting did occur during this pass." << std::endl;
          else
            trace << "splitting did not occur during this pass." << std::endl;
          std::swap(cur_run, next_run);
        }

      done.splice(done.end(), cur_run);

#ifdef TRACE
      trace << "Final partition: ";
      for (partition_t::const_iterator i = done.begin(); i != done.end(); ++i)
        trace << format_hash_set(*i, det_a) << ' ';
      trace << std::endl;
#endif

      // Build the result.
      auto res = build_result(det_a, done, final_copy);

      // Free all the allocated memory.
      delete final_copy;
      hash_map::iterator hit;
      for (hit = state_set_map.begin(); hit != state_set_map.end();)
        {
          hash_map::iterator old = hit++;
          old->first->destroy();
        }
      std::list<hash_set*>::iterator it;
      for (it = done.begin(); it != done.end(); ++it)
        delete *it;

      return res;
    }
  }

  twa_graph_ptr minimize_monitor(const const_twa_graph_ptr& a)
  {
    hash_set* final = new hash_set;
    hash_set* non_final = new hash_set;
    twa_graph_ptr det_a = tgba_powerset(a);

    // non_final contain all states.
    // final is empty: there is no acceptance condition
    build_state_set(det_a, non_final);
    auto res = minimize_dfa(det_a, final, non_final);
    res->prop_copy(a, { false, false, false, true });
    res->prop_deterministic(true);
    res->prop_weak(true);
    res->prop_state_acc(true);
    return res;
  }

  twa_graph_ptr minimize_wdba(const const_twa_graph_ptr& a)
  {
    hash_set* final = new hash_set;
    hash_set* non_final = new hash_set;

    twa_graph_ptr det_a;

    {
      power_map pm;
      det_a = tgba_powerset(a, pm);

      // For each SCC of the deterministic automaton, determine if it
      // is accepting or not.

      // This corresponds to the algorithm in Fig. 1 of "Efficient
      // minimization of deterministic weak omega-automata" written by
      // Christof Löding and published in Information Processing
      // Letters 79 (2001) pp 105--109.

      // We also keep track of whether an SCC is useless
      // (i.e., it is not the start of any accepting word).

      scc_info sm(det_a);
      sm.determine_unknown_acceptance();
      unsigned scc_count = sm.scc_count();
      // SCC that have been marked as useless.
      std::vector<bool> useless(scc_count);
      // The "color".  Even number correspond to
      // accepting SCCs.
      std::vector<unsigned> d(scc_count);

      // An even number larger than scc_count.
      unsigned k = (scc_count | 1) + 1;

      // SCC are numbered in topological order
      // (but in the reverse order as Löding's)
      for (unsigned m = 0; m < scc_count; ++m)
        {
          bool is_useless = true;
          bool transient = sm.is_trivial(m);
          auto& succ = sm.succ(m);

          if (transient && succ.empty())
            {
              // A trivial SCC without successor is useless.
              useless[m] = true;
              d[m] = k - 1;
              continue;
            }

          // Compute the minimum color l of the successors.
          // Also SCCs are useless if all their successor are
          // useless.
          unsigned l = k;
          for (unsigned j: succ)
            {
              is_useless &= useless[j];
              unsigned dj = d[j];
              if (dj < l)
                l = dj;
            }

          if (transient)
            {
              d[m] = l;
            }
          else
            {
              // Regular SCCs are accepting if any of their loop
              // corresponds to an accepted word in the original
              // automaton.
              if (wdba_scc_is_accepting(det_a, m, a, sm, pm))
                {
                  is_useless = false;
                  d[m] = l & ~1; // largest even number inferior or equal
                }
              else
                {
                  d[m] = (l - 1) | 1; // largest odd number inferior or equal
                }
            }

          useless[m] = is_useless;

          if (!is_useless)
            {
              hash_set* dest_set = (d[m] & 1) ? non_final : final;
              for (auto s: sm.states_of(m))
                dest_set->insert(det_a->state_from_number(s));
            }
        }
    }

    auto res = minimize_dfa(det_a, final, non_final);
    res->prop_copy(a, { false, false, false, true });
    res->prop_deterministic(true);
    res->prop_weak(true);
    // If the input was terminal, then the output is also terminal.
    // FIXME:
    // (1) We should have a specialized version of this function for
    // the case where the input is terminal.  See issue #120.
    // (2) It would be nice to have a more precise detection of
    // terminal automata in the output.  Calling
    // is_terminal_automaton() seems overkill here.  But maybe we can
    // add a quick check inside minimize_dfa.
    if (a->prop_terminal())
      res->prop_terminal(true);
    return res;
  }

  twa_graph_ptr
  minimize_obligation(const const_twa_graph_ptr& aut_f,
                      formula f,
                      const_twa_graph_ptr aut_neg_f,
                      bool reject_bigger)
  {
    auto min_aut_f = minimize_wdba(aut_f);

    if (reject_bigger)
      {
        // Abort if min_aut_f has more states than aut_f.
        unsigned orig_states = aut_f->num_states();
        if (orig_states < min_aut_f->num_states())
          return std::const_pointer_cast<twa_graph>(aut_f);
      }

    // If the input automaton was already weak and deterministic, the
    // output is necessary correct.
    if (aut_f->prop_weak() && aut_f->prop_deterministic())
      return min_aut_f;

    // if f is a syntactic obligation formula, the WDBA minimization
    // must be correct.
    if (f && f.is_syntactic_obligation())
      return min_aut_f;

    // If aut_f is a guarantee automaton, the WDBA minimization must be
    // correct.
    if (is_terminal_automaton(aut_f))
      return min_aut_f;

    // Build negation automaton if not supplied.
    if (!aut_neg_f)
      {
        if (f)
          {
            // If we know the formula, simply build the automaton for
            // its negation.
            aut_neg_f = ltl_to_tgba_fm(formula::Not(f), aut_f->get_dict());
            // Remove useless SCCs.
            aut_neg_f = scc_filter(aut_neg_f, true);
          }
        else if (is_deterministic(aut_f))
          {
            // If the automaton is deterministic, complementing is
            // easy.
            aut_neg_f = remove_fin(dtwa_complement(aut_f));
          }
        else
          {
            // Otherwise, we cannot check if the minimization is safe.
            return nullptr;
          }
      }

    // If the negation is a guarantee automaton, then the
    // minimization is correct.
    if (is_terminal_automaton(aut_neg_f))
      return min_aut_f;

    bool ok = false;

    if (product(min_aut_f, aut_neg_f)->is_empty())
      {
        // Complement the minimized WDBA.
        assert((bool)min_aut_f->prop_weak());
        auto neg_min_aut_f = remove_fin(dtwa_complement(min_aut_f));
        if (product(aut_f, neg_min_aut_f)->is_empty())
          // Finally, we are now sure that it was safe
          // to minimize the automaton.
          ok = true;
      }

    if (ok)
      return min_aut_f;
    return std::const_pointer_cast<twa_graph>(aut_f);
  }
}
