// -*- coding: utf-8 -*-
// Copyright (C) 2012-2018 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
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


#include <spot/twaalgos/degen.hh>
#include <spot/twa/twagraph.hh>
#include <spot/misc/hash.hh>
#include <spot/misc/hashfunc.hh>
#include <deque>
#include <vector>
#include <algorithm>
#include <iterator>
#include <memory>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twa/bddprint.hh>

//#define DEGEN_DEBUG

namespace spot
{
  namespace
  {
    // A state in the degenalized automaton corresponds to a state in
    // the TGBA associated to a level.  The level is just an index in
    // the list of acceptance sets.
    typedef std::pair<unsigned, unsigned> degen_state;

    struct degen_state_hash
    {
      size_t
      operator()(const degen_state& s) const noexcept
      {
        return wang32_hash(s.first ^ wang32_hash(s.second));
      }
    };

    // Associate the degeneralized state to its number.
    typedef std::unordered_map<degen_state, unsigned,
                               degen_state_hash> ds2num_map;

    // Queue of state to be processed.
    typedef std::deque<degen_state> queue_t;

    // Acceptance set common to all outgoing or incoming edges (of the
    // same SCC -- we do not care about the others) of some state.
    class inout_acc final
    {
      const_twa_graph_ptr a_;
      typedef std::tuple<acc_cond::mark_t, // common out
                         acc_cond::mark_t, // union out
                         acc_cond::mark_t, // common in, then common in+out
                         bool,             // has self-loop
                         bool> cache_entry; // is true state
      std::vector<cache_entry> cache_;
      unsigned last_true_state_;
      const scc_info* sm_;

      unsigned scc_of(unsigned s) const
      {
        return sm_ ? sm_->scc_of(s) : 0;
      }

      void fill_cache(unsigned s)
      {
        unsigned s1 = scc_of(s);
        acc_cond::mark_t common = a_->acc().all_sets();
        acc_cond::mark_t union_ = 0U;
        bool has_acc_self_loop = false;
        bool is_true_state = false;
        bool seen = false;
        for (auto& t: a_->out(s))
          {
            // Ignore edges that leave the SCC of s.
            unsigned d = t.dst;
            if (scc_of(d) != s1)
              continue;

            common &= t.acc;
            union_ |= t.acc;
            std::get<2>(cache_[d]) &= t.acc;

            // an accepting self-loop?
            if ((t.dst == s) && a_->acc().accepting(t.acc))
              {
                has_acc_self_loop = true;
                if (t.cond == bddtrue)
                  {
                    is_true_state = true;
                    last_true_state_ = s;
                  }
              }
            seen = true;
          }
        if (!seen)
          common = 0U;
        std::get<0>(cache_[s]) = common;
        std::get<1>(cache_[s]) = union_;
        std::get<3>(cache_[s]) = has_acc_self_loop;
        std::get<4>(cache_[s]) = is_true_state;
      }

    public:
      inout_acc(const const_twa_graph_ptr& a, const scc_info* sm):
        a_(a), cache_(a->num_states()), sm_(sm)
      {
        unsigned n = a->num_states();
        acc_cond::mark_t all = a_->acc().all_sets();
        // slot 2 will hold acceptance mark that are common to the
        // incoming transitions of each state.  For know with all
        // marks if there is some incoming edge.  The next loop will
        // constrain this value.
        for (auto& e: a_->edges())
          if (scc_of(e.src) == scc_of(e.dst))
            std::get<2>(cache_[e.dst]) = all;
        for (unsigned s = 0; s < n; ++s)
          fill_cache(s);
        for (unsigned s = 0; s < n; ++s)
          std::get<2>(cache_[s]) |= std::get<0>(cache_[s]);
      }

      // Intersection of all outgoing acceptance sets
      acc_cond::mark_t common_out_acc(unsigned s) const
      {
        assert(s < cache_.size());
        return std::get<0>(cache_[s]);
      }

      // Union of all outgoing acceptance sets
      acc_cond::mark_t union_out_acc(unsigned s) const
      {
        assert(s < cache_.size());
        return std::get<1>(cache_[s]);
      }

      // Intersection of all incoming acceptance sets
      acc_cond::mark_t common_inout_acc(unsigned s) const
      {
        assert(s < cache_.size());
        return std::get<2>(cache_[s]);
      }

      bool has_acc_selfloop(unsigned s) const
      {
        assert(s < cache_.size());
        return std::get<3>(cache_[s]);
      }

      bool is_true_state(unsigned s) const
      {
        assert(s < cache_.size());
        return std::get<4>(cache_[s]);
      }

      unsigned last_true_state() const
      {
        return last_true_state_;
      }
    };

    // Order of accepting sets (for one SCC)
    class acc_order final
    {
      std::vector<unsigned> order_;
      acc_cond::mark_t found_;

    public:
      unsigned
      next_level(int slevel, acc_cond::mark_t set, bool skip_levels)
      {
        // Update the order with any new set we discover
        if (auto newsets = set - found_)
          {
            newsets.fill(std::back_inserter(order_));
            found_ |= newsets;
          }

        unsigned next = slevel;
        while (next < order_.size() && set.has(order_[next]))
          {
            ++next;
            if (!skip_levels)
              break;
          }
        return next;
      }

      void
      print(int scc)
      {
        std::cout << "Order_" << scc << ":\t";
        for (auto i: order_)
          std::cout << i << ", ";
        std::cout << '\n';
      }
    };

    // Accepting order for each SCC
    class scc_orders final
    {
      std::map<int, acc_order> orders_;
      bool skip_levels_;

    public:
      scc_orders(bool skip_levels):
        skip_levels_(skip_levels)
      {
      }

      unsigned
      next_level(int scc, int slevel, acc_cond::mark_t set)
      {
        return orders_[scc].next_level(slevel, set, skip_levels_);
      }

      void
      print()
      {
        std::map<int, acc_order>::iterator i;
        for (i = orders_.begin(); i != orders_.end(); i++)
          i->second.print(i->first);
      }
    };

    template<bool want_sba>
    twa_graph_ptr
    degeneralize_aux(const const_twa_graph_ptr& a, bool use_z_lvl,
                     bool use_cust_acc_orders, int use_lvl_cache,
                     bool skip_levels, bool ignaccsl,
                     bool remove_extra_scc)
    {
      if (!a->acc().is_generalized_buchi())
        throw std::runtime_error
          ("degeneralize() can only works with generalized Büchi acceptance");
      if (!a->is_existential())
        throw std::runtime_error
          ("degeneralize() does not support alternation");

      bool use_scc = (use_lvl_cache
                      || use_cust_acc_orders
                      || use_z_lvl
                      || remove_extra_scc);

      bdd_dict_ptr dict = a->get_dict();

      // The result automaton is an SBA.
      auto res = make_twa_graph(dict);
      res->copy_ap_of(a);
      res->set_buchi();
      if (want_sba)
        res->prop_state_acc(true);
      // Preserve determinism, weakness, and stutter-invariance
      res->prop_copy(a, { false, true, true, true, true, true });

      auto orig_states = new std::vector<unsigned>();
      auto levels = new std::vector<unsigned>();
      orig_states->reserve(a->num_states()); // likely more are needed.
      levels->reserve(a->num_states());
      res->set_named_prop("original-states", orig_states);
      res->set_named_prop("degen-levels", levels);

      // Create an order of acceptance conditions.  Each entry in this
      // vector correspond to an acceptance set.  Each index can
      // be used as a level in degen_state to indicate the next expected
      // acceptance set.  Level order.size() is a special level used to
      // denote accepting states.
      std::vector<unsigned> order;
      {
        // The order is arbitrary, but it turns out that using emplace_back
        // instead of push_front often gives better results because
        // acceptance sets at the beginning if the cycle are more often
        // used in the automaton.  (This surprising fact is probably
        // related to the order in which we declare the BDD variables
        // during the translation.)
        unsigned n = a->num_sets();
        for (unsigned i = n; i > 0; --i)
          order.emplace_back(i - 1);
      }

      // Initialize scc_orders
      scc_orders orders(skip_levels);

      // and vice-versa.
      ds2num_map ds2num;

      // This map is used to find edges that go to the same
      // destination with the same acceptance.  The integer key is
      // (dest*2+acc) where dest is the destination state number, and
      // acc is 1 iff the edge is accepting.  The source
      // is always that of the current iteration.
      typedef std::map<int, unsigned> tr_cache_t;
      tr_cache_t tr_cache;

      // State->level cache
      std::vector<std::pair<unsigned, bool>> lvl_cache(a->num_states());

      // Compute SCCs in order to use any optimization.
      std::unique_ptr<scc_info> m = use_scc
        ? std::make_unique<scc_info>(a, scc_info_options::NONE)
        : nullptr;

      // Cache for common outgoing/incoming acceptances.
      inout_acc inout(a, m.get());

      queue_t todo;

      degen_state s(a->get_init_state_number(), 0);

      // As a heuristic for building SBA, if the initial state has at
      // least one accepting self-loop, start the degeneralization on
      // the accepting level.
      if (want_sba && !ignaccsl && inout.has_acc_selfloop(s.first))
        s.second = order.size();
      // Otherwise, check for acceptance conditions common to all
      // outgoing edges, plus those common to all incoming edges, and
      // assume we have already seen these and start on the associated
      // level.
      if (s.second == 0)
        {
          auto set = inout.common_inout_acc(s.first);
          if (SPOT_UNLIKELY(use_cust_acc_orders))
            s.second = orders.next_level(m->initial(), s.second, set);
          else
            while (s.second < order.size() && set.has(order[s.second]))
              {
                ++s.second;
                if (!skip_levels)
                  break;
              }
          // There is no accepting level for TBA, let reuse level 0.
          if (!want_sba && s.second == order.size())
            s.second = 0;
        }

      auto new_state = [&](degen_state ds)
        {
          // Merge all true states into a single one.
          bool ts = inout.is_true_state(ds.first);
          if (ts)
            ds = {inout.last_true_state(), 0U};

          auto di = ds2num.find(ds);
          if (di != ds2num.end())
              return di->second;

          unsigned ns = res->new_state();
          ds2num[ds] = ns;
          if (ts)
            {
              res->new_acc_edge(ns, ns, bddtrue, true);
              // As we do not process all outgoing transition of
              // ds.first, it is possible that a non-deterministic
              // automaton becomes deterministic.
              if (res->prop_universal().is_false())
                res->prop_universal(trival::maybe());
            }
          else
            todo.emplace_back(ds);

          assert(ns == orig_states->size());
          orig_states->emplace_back(ds.first);
          levels->emplace_back(ds.second);

          // Level cache stores one encountered level for each state
          // (the value of use_lvl_cache determinates which level
          // should be remembered).  This cache is used when
          // re-entering the SCC.
          if (use_lvl_cache)
            {
              unsigned lvl = ds.second;
              if (lvl_cache[ds.first].second)
                {
                  if (use_lvl_cache == 3)
                    lvl = std::max(lvl_cache[ds.first].first, lvl);
                  else if (use_lvl_cache == 2)
                    lvl = std::min(lvl_cache[ds.first].first, lvl);
                  else
                    lvl = lvl_cache[ds.first].first; // Do not change
                }
              lvl_cache[ds.first] = std::make_pair(lvl, true);
            }
          return ns;
        };
      new_state(s);

      while (!todo.empty())
        {
          s = todo.front();
          todo.pop_front();
          int src = ds2num[s];
          unsigned slevel = s.second;

          // If we have a state on the last level, it should be accepting.
          bool is_acc = slevel == order.size();
          // On the accepting level, start again from level 0.
          if (want_sba && is_acc)
            slevel = 0;

          // Check SCC for state s
          int s_scc = -1;
          if (use_scc)
            s_scc = m->scc_of(s.first);

          for (auto& i: a->out(s.first))
            {
              degen_state d(i.dst, 0);

              // Check whether the target SCC is accepting
              bool is_scc_acc;
              int scc;
              if (use_scc)
                {
                  scc = m->scc_of(d.first);
                  is_scc_acc = m->is_accepting_scc(scc);
                }
              else
                {
                  // If we have no SCC information, treat all SCCs as
                  // accepting.
                  scc = -1;
                  is_scc_acc = true;
                }

              // The old level is slevel.  What should be the new one?
              auto acc = i.acc;
              auto otheracc = inout.common_inout_acc(d.first);

              if (want_sba && is_acc)
                {
                  // Ignore the last expected acceptance set (the value of
                  // prev below) if it is common to all other outgoing
                  // edges (of the current state) AND if it is not
                  // used by any outgoing edge of the destination
                  // state.
                  //
                  // 1) It's correct to do that, because this acceptance
                  //    set is common to other outgoing edges.
                  //    Therefore if we make a cycle to this state we
                  //    will eventually see that acceptance set thanks
                  //    to the "pulling" of the common acceptance sets
                  //    of the destination state (d.first).
                  //
                  // 2) It's also desirable because it makes the
                  //    degeneralization idempotent (up to a renaming
                  //    of states).  Consider the following automaton
                  //    where 1 is initial and => marks accepting
                  //    edges: 1=>1, 1=>2, 2->2, 2->1. This is
                  //    already an SBA, with 1 as accepting state.
                  //    However if you try degeralize it without
                  //    ignoring *prev, you'll get two copies of state
                  //    2, depending on whether we reach it using 1=>2
                  //    or from 2->2.  If this example was not clear,
                  //    play with the "degenid.test" test case.
                  //
                  // 3) Ignoring all common acceptance sets would also
                  //    be correct, but it would make the
                  //    degeneralization produce larger automata in some
                  //    cases.  The current condition to ignore only one
                  //    acceptance set if is this not used by the next
                  //    state is a heuristic that is compatible with
                  //    point 2) above while not causing more states to
                  //    be generated in our benchmark of 188 formulae
                  //    from the literature.
                  if (!order.empty())
                    {
                      unsigned prev = order.size() - 1;
                      auto common = inout.common_out_acc(s.first);
                      if (common.has(order[prev]))
                        {
                          auto u = inout.union_out_acc(d.first);
                          if (!u.has(order[prev]))
                            acc -= a->acc().mark(order[prev]);
                        }
                    }
                }
              // A edge in the SLEVEL acceptance set should
              // be directed to the next acceptance set.  If the
              // current edge is also in the next acceptance
              // set, then go to the one after, etc.
              //
              // See Denis Oddoux's PhD thesis for a nice
              // explanation (in French).
              // @PhDThesis{    oddoux.03.phd,
              //   author     = {Denis Oddoux},
              //   title      = {Utilisation des automates alternants pour un
              //                model-checking efficace des logiques
              //                temporelles lin{\'e}aires.},
              //   school     = {Universit{\'e}e Paris 7},
              //   year       = {2003},
              //   address= {Paris, France},
              //   month      = {December}
              // }
              if (is_scc_acc)
                {
                  // If lvl_cache is used and switching SCCs, use level
                  // from cache
                  if (use_lvl_cache && s_scc != scc
                      && lvl_cache[d.first].second)
                    {
                      d.second = lvl_cache[d.first].first;
                    }
                  else
                    {
                      // Complete (or replace) the acceptance sets of
                      // this link with the acceptance sets common to
                      // all edges of the destination SCC entering or
                      // leaving the destination state.
                      if (s_scc == scc)
                        acc |= otheracc;
                      else
                        acc = otheracc;

                      // If use_z_lvl is on, start with level zero 0 when
                      // switching SCCs
                      unsigned next = (!use_z_lvl || s_scc == scc) ? slevel : 0;

                      // If using custom acc orders, get next level
                      // for this scc
                      if (use_cust_acc_orders)
                        {
                          d.second = orders.next_level(scc, next, acc);
                        }
                      // Else compute level according the global acc order
                      else
                        {
                          // As a heuristic, if we enter the SCC on a
                          // state that has at least one accepting
                          // self-loop, start the degeneralization on
                          // the accepting level.
                          if (s_scc != scc
                              && !ignaccsl
                              && inout.has_acc_selfloop(d.first))
                            {
                              d.second = order.size();
                            }
                          else
                            {
                              // Consider both the current acceptance
                              // sets, and the acceptance sets common
                              // to the outgoing edges of the
                              // destination state.  But don't do that
                              // if the state is accepting and we are
                              // not skipping levels.
                              if (skip_levels || !is_acc)
                                while (next < order.size()
                                       && acc.has(order[next]))
                                  {
                                    ++next;
                                    if (!skip_levels)
                                      break;
                                  }
                              d.second = next;
                            }
                        }
                    }
                }

              // In case we are building a TBA is_acc has to be
              // set differently for each edge, and
              // we do not need to stay use final level.
              if (!want_sba)
                {
                  is_acc = d.second == order.size();
                  if (is_acc)        // The edge is accepting
                    {
                      d.second = 0; // Make it go to the first level.
                      // Skip as many levels as possible.
                      if (!a->acc().accepting(acc) && !skip_levels)
                        {
                          if (use_cust_acc_orders)
                            {
                              d.second = orders.next_level(scc, d.second, acc);
                            }
                          else
                            {
                              while (d.second < order.size() &&
                                     acc.has(order[d.second]))
                                ++d.second;
                            }
                        }
                    }
                }

              // Have we already seen this destination?
              int dest = new_state(d);

              unsigned& t = tr_cache[dest * 2 + is_acc];

              if (t == 0)        // Create edge.
                t = res->new_acc_edge(src, dest, i.cond, is_acc);
              else                // Update existing edge.
                res->edge_data(t).cond |= i.cond;
            }
          tr_cache.clear();
        }

#ifdef DEGEN_DEBUG
      std::cout << "Orig. order:  \t";
      for (auto i: order)
        std::cout << i << ", ";
      std::cout << '\n';
      orders.print();
#endif
      res->merge_edges();

      unsigned res_ns = res->num_states();
      if (!remove_extra_scc || res_ns <= a->num_states())
        return res;

      scc_info si_res(res, scc_info_options::TRACK_STATES);
      unsigned res_scc_count = si_res.scc_count();
      if (res_scc_count <= m->scc_count())
        return res;

      // If we reach this place, we have more SCCs in the output than
      // in the input.  This means that we have created some redundant
      // SCCs.  Often, these are trivial SCCs created in front of
      // their larger sisters, because we did not pick the correct
      // level when entering the SCC for the first time, and the level
      // we picked has not been seen again when exploring the SCC.
      // But it could also be the case that by entering the SCC in two
      // different ways, we create two clones of the SCC (I haven't
      // encountered any such case, but I do not want to rule it out
      // in the code below).
      //
      // Now we will iterate over the SCCs in topological order to
      // remember the "bottomost" SCCs that contain each original
      // state.  If an original state is duplicated in a higher SCC,
      // it can be shunted away.  Amen.
      std::vector<unsigned> bottomost_occurence(a->num_states());
      {
        unsigned n = res_scc_count;
        do
          for (unsigned s: si_res.states_of(--n))
            bottomost_occurence[(*orig_states)[s]] = s;
        while (n);
      }
      std::vector<unsigned> retarget(res_ns);
      for (unsigned n = 0; n < res_ns; ++n)
        {
          unsigned other = bottomost_occurence[(*orig_states)[n]];
          retarget[n] = (si_res.scc_of(n) != si_res.scc_of(other)) ? other : n;
        }
      for (auto& e: res->edges())
        e.dst = retarget[e.dst];
      res->purge_unreachable_states();
      return res;
    }
  }

  twa_graph_ptr
  degeneralize(const const_twa_graph_ptr& a,
               bool use_z_lvl, bool use_cust_acc_orders,
               int use_lvl_cache, bool skip_levels, bool ignaccsl,
               bool remove_extra_scc)
  {
    // If this already a degeneralized digraph, there is nothing we
    // can improve.
    if (a->is_sba())
      return std::const_pointer_cast<twa_graph>(a);

    return degeneralize_aux<true>(a, use_z_lvl, use_cust_acc_orders,
                                  use_lvl_cache, skip_levels, ignaccsl,
                                  remove_extra_scc);
  }

  twa_graph_ptr
  degeneralize_tba(const const_twa_graph_ptr& a,
                   bool use_z_lvl, bool use_cust_acc_orders,
                   int use_lvl_cache, bool skip_levels, bool ignaccsl,
                   bool remove_extra_scc)
  {
    // If this already a degeneralized digraph, there is nothing we
    // can improve.
    if (a->acc().is_buchi())
      return std::const_pointer_cast<twa_graph>(a);

    return degeneralize_aux<false>(a, use_z_lvl, use_cust_acc_orders,
                                   use_lvl_cache, skip_levels, ignaccsl,
                                   remove_extra_scc);
  }
}
