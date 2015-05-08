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
                std::cerr << "Created inner node: " << idx << std::endl;
              }
            safra_state& ss = res[idx].first;
            ss.update_succ(node, t.dst, t.acc);
          }
      }
    for (auto& s: res)
      {
        safra_state& tmp = s.first;
        tmp.finalize_construction();
      }
    return res;
  }

  void safra_state::finalize_construction()
  {
    // TODO this is a dirty hack to have two comparision functions depending on
    // wether or not we are still construction the safra_stata
    // Ideally I'd like to have this done statically but not sure how to do it
    for (unsigned i = 0; i < nb_braces_.size(); ++i)
      {
        if (nb_braces_[i] == 0)
          {
            // TODO We also emit Red = min(red, i)
            is_green_[i] = false;
          }
      }
    for (auto& n: nodes_)
      {
        node& nn = const_cast<node&>(n);
        nn.disable_construction();
      }
  }

  void safra_state::update_succ(const node& src, unsigned dst,
                                const acc_cond::mark_t acc)
  {
    (void) acc; // TODO
    auto i = nodes_.find(node(dst));
    if (i != nodes_.end())
      {
        // Todo need to handle acc and create new braces
        if (src.braces_ > i->braces_)
          {
            std::cerr << "Replacing braces of: " << dst << std::endl;
            node& dst = const_cast<node&>(*i);
            for (auto b: dst.braces_)
              nb_braces_[b]--;
            dst.braces_ = src.braces_;
          }
        // Node already exists and has bigger values
        else
          return;
      }
    else
      {
        // Todo need to handle acc and create new braces
        nodes_.emplace(dst, src.braces_);
      }
    for (auto b: src.braces_)
      nb_braces_[b]++;
    // If brace has no right-hand-side brace than it cannot emit any green color
    is_green_[src.braces_[src.braces_.size() - 1]] = false;
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
        is_green_.assign(true, nb_braces);
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
                std::cerr << "New state " << dst_num << std::endl;
                todo.push_back(s.first);
                seen.insert(std::make_pair(s.first, dst_num));
              }
            std::cerr << "Tr: " << src_num << " -> " << dst_num << "["
                      << s.second << "]" << std::endl;
	    res->new_transition(src_num, dst_num, s.second);
          }
      }
    return res;
  }
}
