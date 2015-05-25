// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et
// Développement de l'Epita.
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

#include <deque>
#include <utility>
#include <unordered_map>

#include "safra.hh"
#include "twaalgos/degen.hh"

namespace spot
{
  auto
  safra_state::compute_succs(const const_twa_graph_ptr& aut,
                             const std::vector<unsigned>& bddnums,
                             std::unordered_map<bdd,
                                             std::pair<unsigned, unsigned>,
                                             bdd_hash>& deltas) const -> succs_t
  {
    succs_t res;
    // Given a bdd returns index of associated safra_state in res
    std::map<unsigned, unsigned> bdd2num;
    for (auto& node: nodes_)
      {
        for (auto& t: aut->out(node.first))
          {
            auto p = deltas[t.cond];
            for (unsigned j = p.first; j < p.second; ++j)
              {
                auto i = bdd2num.insert(std::make_pair(bddnums[j], res.size()));
                unsigned idx;
                if (!i.second)
                  idx = i.first->second;
                else
                  {
                    // Each new node starts out with same number of nodes as src
                    idx = res.size();
                    res.emplace_back(safra_state(nb_braces_.size()),
                                     bddnums[j]);
                  }
                safra_state& ss = res[idx].first;
                ss.update_succ(node.second, t.dst, t.acc);
                assert(ss.nb_braces_.size() == ss.is_green_.size());
              }
          }
      }
    for (auto& s: res)
      {
        safra_state& tmp = s.first;
        s.first.color_ = tmp.finalize_construction();
      }
    return res;
  }

  unsigned safra_state::finalize_construction()
  {
    unsigned red = -1U;
    unsigned green = -1U;
    std::vector<unsigned> rem_succ_of;
    assert(is_green_.size() == nb_braces_.size());
    for (unsigned i = 0; i < is_green_.size(); ++i)
      {
        if (nb_braces_[i] == 0)
          {
            red = std::min(red, 2 * i + 1);
            // Step A3: Brackets that do not contain any nodes emit red
            is_green_[i] = false;
          }
        else if (is_green_[i])
          {
            green = std::min(green, 2 * i);
            // Step A4 Emit green
            rem_succ_of.emplace_back(i);
          }
      }
    for (auto& n: nodes_)
      {
        // Step A4 Remove all brackets inside each green pair
        node_helper::truncate_braces(n.second, rem_succ_of, nb_braces_);
      }

    // Step A5 define the rem variable
    std::vector<unsigned> decr_by(nb_braces_.size());
    unsigned decr = 0;
    for (unsigned i = 0; i < nb_braces_.size(); ++i)
      {
        // Step A5 renumber braces
        nb_braces_[i - decr] = nb_braces_[i];
        if (nb_braces_[i] == 0)
          {
            ++decr;
          }
        // Step A5, renumber braces
        decr_by[i] = decr;
      }
    nb_braces_.resize(nb_braces_.size() - decr);
    for (auto& n: nodes_)
      {
        node_helper::renumber(n.second, decr_by);
      }
    return std::min(red, green);
  }

  void node_helper::renumber(std::vector<brace_t>& braces,
                             const std::vector<unsigned>& decr_by)
  {
    for (unsigned idx = 0; idx < braces.size(); ++idx)
      {
        braces[idx] -= decr_by[braces[idx]];
      }
  }

  void
  node_helper::truncate_braces(std::vector<brace_t>& braces,
                                const std::vector<unsigned>& rem_succ_of,
                                std::vector<size_t>& nb_braces)
  {
    for (unsigned idx = 0; idx < braces.size(); ++idx)
      {
        bool found = false;
        // find first brace that matches rem_succ_of
        for (auto s: rem_succ_of)
          {
            found |= braces[idx] == s;
          }
        if (found)
          {
            assert(idx < braces.size() - 1);
            // For each deleted brace, decrement elements of nb_braces
            // This corresponds to A4 step
            for (unsigned i = idx + 1; i < braces.size(); ++i)
              {
                --nb_braces[braces[i]];
              }
            braces.resize(idx + 1);
            break;
          }
      }
  }

  void safra_state::update_succ(const std::vector<node_helper::brace_t>& braces,
                                unsigned dst, const acc_cond::mark_t acc)
  {
    std::vector<node_helper::brace_t> copy = braces;
    // TODO handle multiple accepting sets
    if (acc.count())
      {
        assert(acc.has(0) && acc.count() == 1 &&
               "Only one TBA are accepted at the moment");
        // Accepting transition generate new braces: step A1
        copy.emplace_back(nb_braces_.size());
        // nb_braces_ gets updated later so put 0 for now
        nb_braces_.emplace_back(0);
        // Newly created braces cannot emit green as they won't have
        // any braces inside them (by construction)
        is_green_.push_back(false);
      }
    auto i = nodes_.emplace(dst, copy);
    if (!i.second)
      {
        // Step A2: Remove all occurrences whos nesting pattern (i-e  braces_)
        // is smaller
        if (copy > i.first->second)
          {
            // Remove brace count of replaced node
            for (auto b: i.first->second)
              --nb_braces_[b];
            i.first->second = std::move(copy);
          }
        else
          // Node already exists and has bigger nesting pattern value
          return;
      }
    // After inserting new node, update the brace count per node
    for (auto b: i.first->second)
      ++nb_braces_[b];
    // Step A4: For a brace to emit green it must surround other braces.
    // Hence, the last brace cannot emit green as it is the most inside brace.
    is_green_[i.first->second.back()] = false;
  }

  // Called only to initialize first state
  safra_state::safra_state(unsigned val, bool init_state)
  {
    if (init_state)
      {
        unsigned state_num = val;
        // One brace set
        is_green_.push_back(true);
        // First brace has init_state hence one state inside the first braces.
        nb_braces_.push_back(1);
        std::vector<node_helper::brace_t> braces = { 0 };
        nodes_.emplace(state_num, std::move(braces));
      }
    else
      {
        unsigned nb_braces = val;
        // One brace set
        is_green_.assign(nb_braces, true);
        // First brace has init_state hence one state inside the first braces.
        nb_braces_.assign(nb_braces, 0);
      }
  }

  bool
  safra_state::operator<(const safra_state& other) const
  {
    return nodes_ < other.nodes_;
  }

  void safra_state::print_debug(unsigned state_id)
  {
    std::cerr << "State: " << state_id << "{ ";
    for (auto& n: nodes_)
      {
        std::cerr << n.first << " [";
        for (auto& b: n.second)
          {
            std::cerr << b << ' ';
          }
        std::cerr << "], ";
      }
    std::cerr << "}\n";
  }

  twa_graph_ptr
  tgba_determinisation(const const_twa_graph_ptr& a)
  {
    // Degeneralize
    const_twa_graph_ptr aut;
    if (a->acc().is_generalized_buchi())
      aut = spot::degeneralize_tba(a);
    else
      aut = a;


    bdd allap = bddtrue;
    {
      typedef std::set<bdd, bdd_less_than> sup_map;
      sup_map sup;
      // Record occurrences of all guards
      for (auto& t: aut->transitions())
        sup.emplace(t.cond);
      for (auto& i: sup)
        allap &= bdd_support(i);
    }

    // Preprocessing
    // Used to convert atomic bdd to id
    std::unordered_map<bdd, unsigned, bdd_hash> bdd2num;
    std::vector<bdd> num2bdd;
    // Nedded for compute succs
    // Used to convert large bdd to indexes
    std::unordered_map<bdd, std::pair<unsigned, unsigned>, bdd_hash> deltas;
    std::vector<unsigned> bddnums;
    for (auto& t: aut->transitions())
      {
        auto it = deltas.find(t.cond);
        if (it == deltas.end())
          {
            bdd all = t.cond;
            unsigned prev = bddnums.size();
            while (all != bddfalse)
              {
                bdd one = bdd_satoneset(all, allap, bddfalse);
                all -= one;
                auto p = bdd2num.emplace(one, num2bdd.size());
                if (p.second)
                  num2bdd.push_back(one);
                bddnums.emplace_back(p.first->second);
              }
            deltas[t.cond] = std::make_pair(prev, bddnums.size());
          }
      }
    unsigned nc = bdd2num.size();

    auto res = make_twa_graph(aut->get_dict());
    res->copy_ap_of(aut);
    res->prop_copy(aut,
                   { true, // state based
                   true, // inherently_weak
                   true, // deterministic
                   false // stutter inv
                   });

    // Given a safra_state get its associated state in output automata.
    // Required to create new transitions from 2 safra-state
    typedef std::map<safra_state, int> power_set;
    power_set seen;
    safra_state init(aut->get_init_state_number(), true);
    unsigned num = res->new_state();
    res->set_init_state(num);
    seen.insert(std::make_pair(init, num));
    std::deque<safra_state> todo;
    todo.push_back(init);
    while (!todo.empty())
      {
        using succs_t = safra_state::succs_t;
        safra_state curr = todo.front();
        unsigned src_num = seen.find(curr)->second;
        todo.pop_front();
        succs_t succs = curr.compute_succs(aut, bddnums, deltas);
        for (auto s: succs)
          {
            auto i = seen.find(s.first);
	    unsigned dst_num;
	    if (i != seen.end())
	      {
		dst_num = i->second;
	      }
	    else
	      {
                dst_num = res->new_state();
                // s.first.print_debug(dst_num);
                todo.push_back(s.first);
                seen.insert(std::make_pair(s.first, dst_num));
              }
            if (s.first.color_ != -1U)
              res->new_transition(src_num, dst_num, num2bdd[s.second],
                                  {s.first.color_});
            else
              res->new_transition(src_num, dst_num, num2bdd[s.second]);
          }
      }
    return res;
  }
}
