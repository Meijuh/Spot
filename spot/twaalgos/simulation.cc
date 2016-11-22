// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014, 2015, 2016 Laboratoire de Recherche
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

#include <queue>
#include <map>
#include <utility>
#include <cmath>
#include <limits>
#include <spot/twaalgos/simulation.hh>
#include <spot/misc/minato.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/reachiter.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/sepsets.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/misc/bddlt.hh>

//  Simulation-based reduction, implemented using bdd-based signatures.
//
//  The signature of a state is a Boolean function (implemented as a
//  BDD) representing the set of outgoing transitions of that state.
//  Two states with the same signature are equivalent and can be
//  merged.
//
// We define signatures in a way that implications between signatures
//  entail language inclusion.  These inclusions are used to remove
//  redundant transitions, but this occurs implicitly while
//  transforming the signature into irredundant-sum-of-product before
//  building the automaton: redundant terms that are left over
//  correspond to ignored transitions.
//
//  See our Spin'13 paper for background on this procedure.

namespace spot
{
  namespace
  {
    // Used to get the signature of the state.
    typedef std::vector<bdd> vector_state_bdd;

    // Get the list of state for each class.
    typedef std::map<bdd, std::list<unsigned>,
                     bdd_less_than> map_bdd_lstate;

    // This class helps to compare two automata in term of
    // size.
    struct automaton_size final
    {
      automaton_size()
        : edges(0),
          states(0)
      {
      }

      automaton_size(const twa_graph_ptr& a)
        : edges(a->num_edges()),
          states(a->num_states())
      {
      }

      void set_size(const twa_graph_ptr& a)
      {
        states = a->num_states();
        edges = a->num_edges();
      }

      inline bool operator!=(const automaton_size& r)
      {
        return edges != r.edges || states != r.states;
      }

      inline bool operator<(const automaton_size& r)
      {
        if (states < r.states)
          return true;
        if (states > r.states)
          return false;

        if (edges < r.edges)
          return true;
        if (edges > r.edges)
          return false;

        return false;
      }

      inline bool operator>(const automaton_size& r)
      {
        if (states < r.states)
          return false;
        if (states > r.states)
          return true;

        if (edges < r.edges)
          return false;
        if (edges > r.edges)
          return true;

        return false;
      }

      int edges;
      int states;
    };

    // The direct_simulation. If Cosimulation is true, we are doing a
    // cosimulation.
    template <bool Cosimulation, bool Sba>
    class direct_simulation final
    {
    protected:
      typedef std::map<bdd, bdd, bdd_less_than> map_bdd_bdd;
      int acc_vars;
      acc_cond::mark_t all_inf_;
    public:

      bdd mark_to_bdd(acc_cond::mark_t m)
      {
        // FIXME: Use a cache.
        bdd res = bddtrue;
        for (auto n: m.sets())
          res &= bdd_ithvar(acc_vars + n);
        return res;
      }

      acc_cond::mark_t bdd_to_mark(bdd b)
      {
        // FIXME: Use a cache.
        std::vector<unsigned> res;
        while (b != bddtrue)
          {
            res.emplace_back(bdd_var(b) - acc_vars);
            b = bdd_high(b);
          }
        return acc_cond::mark_t(res.begin(), res.end());
      }

      direct_simulation(const const_twa_graph_ptr& in)
        : po_size_(0),
          all_class_var_(bddtrue),
          original_(in)
      {
        if (!has_separate_sets(in))
          throw std::runtime_error
            ("direct_simulation() requires separate Inf and Fin sets");

        // Call get_init_state_number() before anything else as it
        // might add a state.
        unsigned init_state_number = in->get_init_state_number();
        scc_info_.reset(new scc_info(in));

        unsigned ns = in->num_states();
        assert(ns > 0);
        size_a_ = ns;

        auto all_inf = in->get_acceptance().used_inf_fin_sets().first;
        all_inf_ = all_inf;

        // Replace all the acceptance conditions by their complements.
        // (In the case of Cosimulation, we also flip the edges.)
        if (Cosimulation)
          {
            a_ = make_twa_graph(in->get_dict());
            a_->copy_ap_of(in);
            a_->copy_acceptance_of(in);
            a_->new_states(ns);

            for (unsigned s = 0; s < ns; ++s)
              {
                for (auto& t: in->out(s))
                  {
                    acc_cond::mark_t acc;
                    if (Sba)
                      {
                        // If the acceptance is interpreted as
                        // state-based, to apply the reverse simulation
                        // on a SBA, we should pull the acceptance of
                        // the destination state on its incoming arcs
                        // (which now become outgoing arcs after
                        // transposition).
                        acc = 0U;
                        for (auto& td: in->out(t.dst))
                          {
                            acc = td.acc ^ all_inf;
                            break;
                          }
                      }
                    else
                      {
                        acc = t.acc ^ all_inf;
                      }
                    a_->new_edge(t.dst, s, t.cond, acc);
                  }
                a_->set_init_state(init_state_number);
              }
          }
        else
          {
            a_ = make_twa_graph(in, twa::prop_set::all());
            for (auto& t: a_->edges())
              t.acc ^= all_inf;
          }
        assert(a_->num_states() == size_a_);

        want_implications_ = !is_deterministic(a_);

        // Now, we have to get the bdd which will represent the
        // class. We register one bdd by state, because in the worst
        // case, |Class| == |State|.
        unsigned set_num = a_->get_dict()
          ->register_anonymous_variables(size_a_ + 1, this);

        unsigned n_acc = a_->num_sets();
        acc_vars = a_->get_dict()
          ->register_anonymous_variables(n_acc, this);

        all_proms_ = bddtrue;
        for (unsigned v = acc_vars; v < acc_vars + n_acc; ++v)
          all_proms_ &= bdd_ithvar(v);

        bdd_initial = bdd_ithvar(set_num++);
        bdd init = bdd_ithvar(set_num++);

        used_var_.emplace_back(init);

        // Initialize all classes to init.
        previous_class_.resize(size_a_);
        for (unsigned s = 0; s < size_a_; ++s)
          previous_class_[s] = init;

        // Put all the anonymous variable in a queue, and record all
        // of these in a variable all_class_var_ which will be used
        // to understand the destination part in the signature when
        // building the resulting automaton.
        all_class_var_ = init;
        for (unsigned i = set_num; i < set_num + size_a_ - 1; ++i)
          {
            free_var_.push(i);
            all_class_var_ &= bdd_ithvar(i);
          }

        relation_[init] = init;
      }


      // Reverse all the acceptance condition at the destruction of
      // this object, because it occurs after the return of the
      // function simulation.
      virtual ~direct_simulation()
      {
        a_->get_dict()->unregister_all_my_variables(this);
      }

      // Update the name of the classes.
      void update_previous_class()
      {
        std::list<bdd>::iterator it_bdd = used_var_.begin();

        // We run through the map bdd/list<state>, and we update
        // the previous_class_ with the new data.
        for (auto& p: bdd_lstate_)
          {
            // If the signature of a state is bddfalse (no
            // edges) the class of this state is bddfalse
            // instead of an anonymous variable. It allows
            // simplifications in the signature by removing a
            // edge which has as a destination a state with
            // no outgoing edge.
            if (p.first == bddfalse)
              for (auto s: p.second)
                previous_class_[s] = bddfalse;
            else
              for (auto s: p.second)
                previous_class_[s] = *it_bdd;
            ++it_bdd;
          }
      }

      void main_loop()
      {
        unsigned int nb_partition_before = 0;
        unsigned int nb_po_before = po_size_ - 1;
        while (nb_partition_before != bdd_lstate_.size()
               || nb_po_before != po_size_)
          {
            update_previous_class();
            nb_partition_before = bdd_lstate_.size();
            bdd_lstate_.clear();
            nb_po_before = po_size_;
            po_size_ = 0;
            update_sig();
            go_to_next_it();
          }

        update_previous_class();
      }

      // The core loop of the algorithm.
      twa_graph_ptr run(std::vector<bdd>* implications = nullptr)
      {
        main_loop();
        return build_result(implications);
      }

      // Take a state and compute its signature.
      bdd compute_sig(unsigned src)
      {
        bdd res = bddfalse;

        for (auto& t: a_->out(src))
          {
            bdd acc = mark_to_bdd(t.acc);

            // to_add is a conjunction of the acceptance condition,
            // the label of the edge and the class of the
            // destination and all the class it implies.
            bdd to_add = acc & t.cond & relation_[previous_class_[t.dst]];

            res |= to_add;
          }

        // When we Cosimulate, we add a special flag to differentiate
        // the initial state from the other.
        if (Cosimulation && src == a_->get_init_state_number())
          res |= bdd_initial;

        return res;
      }


      void update_sig()
      {
        for (unsigned s = 0; s < size_a_; ++s)
          bdd_lstate_[compute_sig(s)].emplace_back(s);
      }


      // This method renames the color set, updates the partial order.
      void go_to_next_it()
      {
        int nb_new_color = bdd_lstate_.size() - used_var_.size();


        // If we have created more partitions, we need to use more
        // variables.
        for (int i = 0; i < nb_new_color; ++i)
          {
            assert(!free_var_.empty());
            used_var_.emplace_back(bdd_ithvar(free_var_.front()));
            free_var_.pop();
          }


        // If we have reduced the number of partition, we 'free' them
        // in the free_var_ list.
        for (int i = 0; i > nb_new_color; --i)
          {
            assert(!used_var_.empty());
            free_var_.push(bdd_var(used_var_.front()));
            used_var_.pop_front();
          }


        assert((bdd_lstate_.size() == used_var_.size())
               || (bdd_lstate_.find(bddfalse) != bdd_lstate_.end()
                   && bdd_lstate_.size() == used_var_.size() + 1));

        // This vector links the tuple "C^(i-1), N^(i-1)" to the
        // new class coloring for the next iteration.
        std::vector<std::pair<bdd, bdd>> now_to_next;
        unsigned sz = bdd_lstate_.size();
        now_to_next.reserve(sz);

        std::list<bdd>::iterator it_bdd = used_var_.begin();

        for (auto& p: bdd_lstate_)
          {
            // If the signature of a state is bddfalse (no edges) the
            // class of this state is bddfalse instead of an anonymous
            // variable. It allows simplifications in the signature by
            // removing an edge which has as a destination a state
            // with no outgoing edge.
            bdd acc = bddfalse;
            if (p.first != bddfalse)
              acc = *it_bdd;
            now_to_next.emplace_back(p.first, acc);
            ++it_bdd;
          }

        // Update the partial order.

        // This loop follows the pattern given by the paper.
        // foreach class do
        // |  foreach class do
        // |  | update po if needed
        // |  od
        // od

        for (unsigned n = 0; n < sz; ++n)
          {
            bdd n_sig = now_to_next[n].first;
            bdd n_class = now_to_next[n].second;
            if (want_implications_)
              for (unsigned m = 0; m < sz; ++m)
                {
                  if (n == m)
                    continue;
                  if (bdd_implies(n_sig, now_to_next[m].first))
                    {
                      n_class &= now_to_next[m].second;
                      ++po_size_;
                    }
                }
            relation_[now_to_next[n].second] = n_class;
          }
      }

      // Build the minimal resulting automaton.
      twa_graph_ptr build_result(std::vector<bdd>* implications = nullptr)
      {
        twa_graph_ptr res = make_twa_graph(a_->get_dict());
        res->copy_ap_of(a_);
        res->copy_acceptance_of(a_);

        // Non atomic propositions variables (= acc and class)
        bdd nonapvars = all_proms_ & bdd_support(all_class_var_);

        auto* gb = res->create_namer<int>();

        if (implications)
          implications->resize(bdd_lstate_.size());
        // Create one state per partition.
        for (auto& p: bdd_lstate_)
          {
            bdd cl = previous_class_[p.second.front()];
            // A state may be referred to either by
            // its class, or by all the implied classes.
            auto s = gb->new_state(cl.id());
            gb->alias_state(s, relation_[cl].id());
            if (implications)
              (*implications)[s] = relation_[cl];
          }

        // Acceptance of states.  Only used if Sba && Cosimulation.
        std::vector<acc_cond::mark_t> accst;
        if (Sba && Cosimulation)
          accst.resize(res->num_states(), 0U);

        stat.states = bdd_lstate_.size();
        stat.edges = 0;

        unsigned nb_satoneset = 0;
        unsigned nb_minato = 0;

        auto all_inf = all_inf_;
        // For each class, we will create
        // all the edges between the states.
        for (auto& p: bdd_lstate_)
          {
            // All states in p.second have the same class, so just
            // pick the class of the first one first one.
            bdd src = previous_class_[p.second.front()];

            // Get the signature to derive successors.
            bdd sig = compute_sig(p.second.front());

            if (Cosimulation)
              sig = bdd_compose(sig, bddfalse, bdd_var(bdd_initial));

            // Get all the variable in the signature.
            bdd sup_sig = bdd_support(sig);

            // Get the variable in the signature which represents the
            // conditions.
            bdd sup_all_atomic_prop = bdd_exist(sup_sig, nonapvars);

            // Get the part of the signature composed only with the atomic
            // proposition.
            bdd all_atomic_prop = bdd_exist(sig, nonapvars);

            // First loop over all possible valuations atomic properties.
            while (all_atomic_prop != bddfalse)
              {
                bdd one = bdd_satoneset(all_atomic_prop,
                                        sup_all_atomic_prop,
                                        bddtrue);
                all_atomic_prop -= one;

                // For each possible valuation, iterate over all possible
                // destination classes.   We use minato_isop here, because
                // if the same valuation of atomic properties can go
                // to two different classes C1 and C2, iterating on
                // C1 + C2 with the above bdd_satoneset loop will see
                // C1 then (!C1)C2, instead of C1 then C2.
                // With minatop_isop, we ensure that the no negative
                // class variable will be seen (likewise for promises).
                minato_isop isop(sig & one);

                ++nb_satoneset;

                bdd cond_acc_dest;
                while ((cond_acc_dest = isop.next()) != bddfalse)
                  {
                    ++stat.edges;

                    ++nb_minato;

                    // Take the edge, and keep only the variable which
                    // are used to represent the class.
                    bdd dst = bdd_existcomp(cond_acc_dest,
                                             all_class_var_);

                    // Keep only ones who are acceptance condition.
                    auto acc = bdd_to_mark(bdd_existcomp(cond_acc_dest,
                                                         all_proms_));

                    // Keep the other!
                    bdd cond = bdd_existcomp(cond_acc_dest,
                                             sup_all_atomic_prop);

                    // Because we have complemented all the Inf
                    // acceptance conditions on the input automaton,
                    // we must revert them to create a new edge.
                    acc ^= all_inf;

                    if (Cosimulation)
                      {
                        if (Sba)
                          {
                            // acc should be attached to src, or rather,
                            // in our edge-based representation)
                            // to all edges leaving src.  As we
                            // can't do this here, store this in a table
                            // so we can fix it later.
                            accst[gb->get_state(src.id())] = acc;
                            acc = 0U;
                          }
                        gb->new_edge(dst.id(), src.id(), cond, acc);
                      }
                    else
                      {
                        gb->new_edge(src.id(), dst.id(), cond, acc);
                      }
                  }
              }
          }

        res->set_init_state(gb->get_state(previous_class_
                                          [a_->get_init_state_number()].id()));

        res->merge_edges(); // FIXME: is this really needed?

        // Mark all accepting state in a second pass, when
        // dealing with SBA in cosimulation.
        if (Sba && Cosimulation)
          {
            unsigned ns = res->num_states();
            for (unsigned s = 0; s < ns; ++s)
              {
                acc_cond::mark_t acc = accst[s];
                if (acc == 0U)
                  continue;
                for (auto& t: res->out(s))
                  t.acc = acc;
              }
          }

        // If we recorded implications for the determinization
        // procedure, we should not remove unreachable states, as that
        // will invalidate the contents of the IMPLICATIONS vector.
        // It's OK not to purge the result, as the determinization
        // will only explore the reachable part anyway.
        if (!implications)
          res->purge_unreachable_states();

        delete gb;
        res->prop_copy(original_,
                       { false, // state-based acc forced below
                         true,  // weakness preserved,
                         true, // determinism checked and overridden below
                               // and "unambiguous" property preserved
                         true, // stutter inv.
                       });
        if (!Cosimulation)
          res->prop_deterministic(nb_minato == nb_satoneset);
        if (Sba)
          res->prop_state_acc(true);
        return res;
      }


      // Debug:
      // In a first time, print the signature, and the print a list
      // of each state in this partition.
      // In a second time, print foreach state, who is where,
      // where is the new class name.
      void print_partition()
      {
        for (auto& p: bdd_lstate_)
          {
            std::cerr << "partition: "
                      << bdd_format_isop(a_->get_dict(), p.first)
                      << std::endl;
            for (auto s: p.second)
              std::cerr << "  - "
                        << a_->format_state(a_->state_from_number(s))
                        << '\n';
          }

        std::cerr << "\nPrevious iteration\n" << std::endl;

        unsigned ps = previous_class_.size();
        for (unsigned p = 0; p < ps; ++p)
          {
            std::cerr << a_->format_state(a_->state_from_number(p))
                      << " was in "
                      << bdd_format_set(a_->get_dict(), previous_class_[p])
                      << '\n';
          }
      }

    protected:
      // The automaton which is simulated.
      twa_graph_ptr a_;

      // Implications between classes.
      map_bdd_bdd relation_;

      // Represent the class of each state at the previous iteration.
      vector_state_bdd previous_class_;

      // The list of state for each class at the current_iteration.
      // Computed in `update_sig'.
      map_bdd_lstate bdd_lstate_;

      // The queue of free bdd. They will be used as the identifier
      // for the class.
      std::queue<int> free_var_;

      // The list of used bdd. They are in used as identifier for class.
      std::list<bdd> used_var_;

      // Size of the automaton.
      unsigned int size_a_;

      // Used to know when there is no evolution in the partial order.
      unsigned int po_size_;

      // Whether to compute implications between classes.  This is costly
      // and useless for deterministic automata.
      bool want_implications_;

      // All the class variable:
      bdd all_class_var_;

      // The flag to say if the outgoing state is initial or not
      bdd bdd_initial;

      bdd all_proms_;

      automaton_size stat;

      std::unique_ptr<scc_info> scc_info_;

      const const_twa_graph_ptr original_;
    };

  } // End namespace anonymous.


  twa_graph_ptr
  simulation(const const_twa_graph_ptr& t)
  {
    direct_simulation<false, false> simul(t);
    return simul.run();
  }

  twa_graph_ptr
  simulation(const const_twa_graph_ptr& t,
             std::vector<bdd>* implications)
  {
    direct_simulation<false, false> simul(t);
    return simul.run(implications);
  }

  twa_graph_ptr
  simulation_sba(const const_twa_graph_ptr& t)
  {
    direct_simulation<false, true> simul(t);
    return simul.run();
  }

  twa_graph_ptr
  cosimulation(const const_twa_graph_ptr& t)
  {
    direct_simulation<true, false> simul(t);
    return simul.run();
  }

  twa_graph_ptr
  cosimulation_sba(const const_twa_graph_ptr& t)
  {
    direct_simulation<true, true> simul(t);
    return simul.run();
  }


  template<bool Sba>
  twa_graph_ptr
  iterated_simulations_(const const_twa_graph_ptr& t)
  {
    twa_graph_ptr res = nullptr;
    automaton_size prev;
    automaton_size next;

    do
      {
        prev = next;
        direct_simulation<false, Sba> simul(res ? res : t);
        res = simul.run();
        if (res->prop_deterministic())
          break;

        direct_simulation<true, Sba> cosimul(res);
        res = cosimul.run();

        if (Sba)
          res = scc_filter_states(res, false);
        else
          res = scc_filter(res, false);

        next.set_size(res);
      }
    while (prev != next);
    return res;
  }

  twa_graph_ptr
  iterated_simulations(const const_twa_graph_ptr& t)
  {
    return iterated_simulations_<false>(t);
  }

  twa_graph_ptr
  iterated_simulations_sba(const const_twa_graph_ptr& t)
  {
    return iterated_simulations_<true>(t);
  }

} // End namespace spot.
