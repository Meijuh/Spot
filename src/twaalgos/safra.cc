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

#include "safra.hh"

namespace spot
{
  auto
  safra_state::compute_succs(const const_twa_graph_ptr& aut) const -> succs_t
  {
    succs_t res;
    // Given a bdd returns index of associated safra_state in res
    std::map<bdd, unsigned, bdd_less_than> bdd2num;
    for (auto& node: nodes_)
      {
        for (auto& t: aut->out(node.id_))
          {
            auto i = bdd2num.insert(std::make_pair(t.cond, res.size()));
            unsigned idx;
	    if (!i.second)
              idx = i.first->second;
	    else
	      {
                // Each new node starts out with same number of nodes as src
                safra_state empty_state = safra_state(nb_braces_.size());
                idx = res.size();
                res.push_back(std::make_pair(empty_state, t.cond));
              }
            safra_state& ss = res[idx].first;
            assert(ss.nb_braces_.size() == ss.is_green_.size());
            ss.update_succ(node, t.dst, t.acc);
            assert(ss.nb_braces_.size() == ss.is_green_.size());
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
            // TODO We also emit Red = min(red, i)
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
        node& nn = const_cast<node&>(n);
        // Step A4 Remove all brackets inside each green pair
        nn.truncate_braces(rem_succ_of, nb_braces_);
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
        node& nn = const_cast<node&>(n);
        nn.renumber(decr_by);

        // TODO this is a dirty hack to have two comparision functions depending
        // on  wether or not we are still construction the safra_stata
        // Ideally I'd like to have this done statically but not sure how to do
        // it
        nn.disable_construction();
      }
    return std::min(red, green);
  }

  void safra_state::node::renumber(const std::vector<unsigned>& decr_by)
  {
    for (unsigned idx = 0; idx < braces_.size(); ++idx)
      {
        braces_[idx] -= decr_by[braces_[idx]];
      }
  }

  // TODO FINISH TRUNCATE
  void
  safra_state::node::truncate_braces(const std::vector<unsigned>& rem_succ_of,
                                     std::vector<size_t>& nb_braces)
  {
    assert(in_construction_ && "Only allowed to do this during construction");
    for (unsigned idx = 0; idx < braces_.size(); ++idx)
      {
        bool found = false;
        // find first brace that matches rem_succ_of
        for (auto s: rem_succ_of)
          {
            found |= braces_[idx] == s;
          }
        if (found)
          {
            assert(idx < braces_.size() - 1);
            // For each deleted brace, decrement elements of nb_braces
            // This corresponds to A4 step
            for (unsigned i = idx + 1; i < braces_.size(); ++i)
              {
                --nb_braces[braces_[i]];
              }
            braces_.resize(idx + 1);
            break;
          }
      }
  }

  void safra_state::update_succ(const node& src, unsigned dst,
                                const acc_cond::mark_t acc)
  {
    unsigned last_brace = src.braces_.back();
    // Check if there already is a node named dst in current macro_state
    auto i = nodes_.find(node(dst));
    if (i != nodes_.end())
      {
        // Step A2: Remove all occurrences whos nesting pattern (i-e  braces_)
        // is smaller
        if (src.braces_ > i->braces_ ||
           (acc.count() && src.braces_ == i->braces_))
          {
            auto copy = src.braces_;
            // TODO handle multiple accepting transition
            if (acc.count())
              {
                // Accepting transition generate new braces: step A1
                last_brace = nb_braces_.size();
                copy.emplace_back(nb_braces_.size());
                nb_braces_.emplace_back(1);
                // Newly created braces cannot emit green as they won't have
                // any braces inside them (by construction)
                is_green_.emplace_back(false);
              }
            {
              // Remove brace count of removed node
              node& dst = const_cast<node&>(*i);
              for (auto b: dst.braces_)
                --nb_braces_[b];
            }
            {
              // Affect new value of braces
              node& dst = const_cast<node&>(*i);
              for (auto b: copy)
                ++nb_braces_[b];
              dst.braces_ = std::move(copy);
            }
          }
        else
          // Node already exists and has bigger nesting pattern value
          return;
      }
    else
      {
        // TODO need to handle multiple acc sets
        auto copy = src.braces_;
        if (acc.count())
          {
            last_brace = nb_braces_.size();
            copy.emplace_back(nb_braces_.size());
            // Step A4 Newly created braces cannot emit green as they won't have
            // any braces inside them (by construction)
            is_green_.emplace_back(false);
            nb_braces_.emplace_back(0);
          }
        for (auto b: copy)
          ++nb_braces_[b];
        nodes_.emplace(dst, std::move(copy));
      }
    // Step A4: For a brace to emit green it must surround other braces.
    // Therefore, the last brace cannot emit green as it is the most inside
    // brace.
    is_green_[last_brace] = false;
  }

  // Comparison is needed when for a set of safra_state
  bool
  safra_state::operator<(const safra_state& other) const
  {
    return nodes_ < other.nodes_;
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
        nodes_.emplace(state_num, 0);
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
  safra_state::node::operator<(const node& other) const
  {
    if (id_ == other.id_)
      return in_construction_ ? false : braces_ < other.braces_;
    else
      return id_ < other.id_;
  }

  bool
  safra_state::node::operator==(const node& other) const
  {
    if (id_ == other.id_)
      return in_construction_ ? true : braces_ == other.braces_;
    else
      return false;
  }

  void safra_state::print_debug(unsigned state_id)
  {
    std::cerr << "State: " << state_id << "{ ";
    for (auto& n: nodes_)
      {
        std::cerr << n.id_ << " [";
        for (auto& b: n.braces_)
          {
            std::cerr << b << ' ';
          }
        std::cerr << "], ";
      }
    std::cerr << "}\n";
  }

  twa_graph_ptr
  tgba_determinisation(const const_twa_graph_ptr& aut)
  {
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
        succs_t succs = curr.compute_succs(aut);
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
              res->new_transition(src_num, dst_num, s.second, {s.first.color_});
            else
              res->new_transition(src_num, dst_num, s.second);
          }
      }
    return res;
  }
}
