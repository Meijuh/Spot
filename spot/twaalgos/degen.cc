// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014, 2015, 2016 Laboratoire de Recherche
// et Développement de l'Epita.
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
      operator()(const degen_state& s) const
      {
        return wang32_hash(s.first ^ wang32_hash(s.second));
      }
    };

    // Associate the degeneralized state to its number.
    typedef std::unordered_map<degen_state, int, degen_state_hash> ds2num_map;

    // Queue of state to be processed.
    typedef std::deque<degen_state> queue_t;

    // Acceptance set common to all outgoing edges (of the same
    // SCC -- we do not care about the other) of some state.
    class outgoing_acc final
    {
      const_twa_graph_ptr a_;
      typedef std::tuple<acc_cond::mark_t,
                         acc_cond::mark_t,
                         bool> cache_entry;
      std::vector<cache_entry> cache_;
      const scc_info* sm_;

      void fill_cache(unsigned s)
      {
        unsigned s1 = sm_ ? sm_->scc_of(s) : 0;
        acc_cond::mark_t common = a_->acc().all_sets();
        acc_cond::mark_t union_ = 0U;
        bool has_acc_self_loop = false;
        bool seen = false;
        for (auto& t: a_->out(s))
          {
            // Ignore edges that leave the SCC of s.
            unsigned d = t.dst;
            unsigned s2 = sm_ ? sm_->scc_of(d) : 0;
            if (s2 != s1)
              continue;

            common &= t.acc;
            union_ |= t.acc;

            // an accepting self-loop?
            has_acc_self_loop |= (t.dst == s) && a_->acc().accepting(t.acc);
            seen = true;
          }
        if (!seen)
          common = 0U;
        cache_[s] = std::make_tuple(common, union_, has_acc_self_loop);
      }

    public:
      outgoing_acc(const const_twa_graph_ptr& a, const scc_info* sm):
        a_(a), cache_(a->num_states()), sm_(sm)
      {
        unsigned n = a->num_states();
        for (unsigned s = 0; s < n; ++s)
          fill_cache(s);
      }

      // Intersection of all outgoing acceptance sets
      acc_cond::mark_t common_acc(unsigned s)
      {
        assert(s < cache_.size());
        return std::get<0>(cache_[s]);
      }

      // Union of all outgoing acceptance sets
      acc_cond::mark_t union_acc(unsigned s)
      {
        assert(s < cache_.size());
        return std::get<1>(cache_[s]);
      }

      // Has an accepting self-loop
      bool has_acc_selfloop(unsigned s)
      {
        assert(s < cache_.size());
        return std::get<2>(cache_[s]);
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
                     bool skip_levels, bool ignaccsl)
    {
      if (!a->acc().is_generalized_buchi())
        throw std::runtime_error
          ("degeneralize() can only works with generalized Büchi acceptance");

      bool use_scc = use_lvl_cache || use_cust_acc_orders || use_z_lvl;

      bdd_dict_ptr dict = a->get_dict();

      // The result automaton is an SBA.
      auto res = make_twa_graph(dict);
      res->copy_ap_of(a);
      res->set_buchi();
      if (want_sba)
        res->prop_state_acc(true);
      // Preserve determinism, weakness, and stutter-invariance
      res->prop_copy(a, { false, true, true, true });

      // Create an order of acceptance conditions.  Each entry in this
      // vector correspond to an acceptance set.  Each index can
      // be used as a level in degen_state to indicate the next expected
      // acceptance set.  Level order.size() is a special level used to
      // denote accepting states.
      std::vector<unsigned> order;
      {
        // FIXME: revisit this comment once everything compiles again.
        //
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

      // Read this early, because it might create a state if the
      // automaton is empty.
      degen_state s(a->get_init_state_number(), 0);

      // State->level cache
      std::vector<std::pair<unsigned, bool>> lvl_cache(a->num_states());

      // Compute SCCs in order to use any optimization.
      scc_info* m = nullptr;
      if (use_scc)
        m = new scc_info(a);

      // Cache for common outgoing acceptances.
      outgoing_acc outgoing(a, m);

      queue_t todo;

      // As a heuristic for building SBA, if the initial state has at
      // least one accepting self-loop, start the degeneralization on
      // the accepting level.
      if (want_sba && !ignaccsl && outgoing.has_acc_selfloop(s.first))
        s.second = order.size();
      // Otherwise, check for acceptance conditions common to all
      // outgoing edges, and assume we have already seen these and
      // start on the associated level.
      if (s.second == 0)
        {
          auto set = outgoing.common_acc(s.first);
          if (use_cust_acc_orders)
            s.second = orders.next_level(m->initial(), s.second, set);
          else
            while (s.second < order.size()
                   && set.has(order[s.second]))
              {
                ++s.second;
                if (!skip_levels)
                  break;
              }
          // There is not accepting level for TBA, let reuse level 0.
          if (!want_sba && s.second == order.size())
            s.second = 0;
        }

      ds2num[s] = res->new_state();
      todo.emplace_back(s);

      // If use_lvl_cache is on insert initial state to level cache
      // Level cache stores first encountered level for each state.
      // When entering an SCC first the lvl_cache is checked.
      // If such state exists level from chache is used.
      // If not, a new level (starting with 0) is computed.
      if (use_lvl_cache)
        lvl_cache[s.first] = std::make_pair(s.second, true);

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
              auto otheracc = outgoing.common_acc(d.first);

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
                      auto common = outgoing.common_acc(s.first);
                      if (common.has(order[prev]))
                        {
                          auto u = outgoing.union_acc(d.first);
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
                      // all edges leaving the destination state.
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
                              && outgoing.has_acc_selfloop(d.first))
                            {
                              d.second = order.size();
                            }
                          else
                            {
                              // Consider both the current acceptance
                              // sets, and the acceptance sets common to
                              // the outgoing edges of the
                              // destination state.  But don't do
                              // that if the state is accepting and we
                              // are not skipping levels.
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
                      // Skip levels as much as possible.
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
              int dest;
              ds2num_map::const_iterator di = ds2num.find(d);
              if (di != ds2num.end())
                {
                  dest = di->second;
                }
              else
                {
                  dest = res->new_state();
                  ds2num[d] = dest;
                  todo.emplace_back(d);
                  // Insert new state to cache

                  if (use_lvl_cache)
                    {
                      auto lvl = d.second;
                      if (lvl_cache[d.first].second)
                        {
                          if (use_lvl_cache == 3)
                            lvl = std::max(lvl_cache[d.first].first, lvl);
                          else if (use_lvl_cache == 2)
                            lvl = std::min(lvl_cache[d.first].first, lvl);
                          else
                            lvl = lvl_cache[d.first].first; // Do not change
                        }
                      lvl_cache[d.first] = std::make_pair(lvl, true);
                    }
                }

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
        {
          std::cout << i << ", ";
        }
      std::cout << '\n';
      orders.print();
#endif

      delete m;

      res->merge_edges();
      return res;
    }
  }

  twa_graph_ptr
  degeneralize(const const_twa_graph_ptr& a,
               bool use_z_lvl, bool use_cust_acc_orders,
               int use_lvl_cache, bool skip_levels, bool ignaccsl)
  {
    // If this already a degeneralized digraph, there is nothing we
    // can improve.
    if (a->is_sba())
      return std::const_pointer_cast<twa_graph>(a);

    return degeneralize_aux<true>(a, use_z_lvl, use_cust_acc_orders,
                                  use_lvl_cache, skip_levels, ignaccsl);
  }

  twa_graph_ptr
  degeneralize_tba(const const_twa_graph_ptr& a,
                   bool use_z_lvl, bool use_cust_acc_orders,
                   int use_lvl_cache, bool skip_levels, bool ignaccsl)
  {
    // If this already a degeneralized digraph, there is nothing we
    // can improve.
    if (a->acc().is_buchi())
      return std::const_pointer_cast<twa_graph>(a);

    return degeneralize_aux<false>(a, use_z_lvl, use_cust_acc_orders,
                                   use_lvl_cache, skip_levels, ignaccsl);
  }
}
