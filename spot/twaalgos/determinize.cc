// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016 Laboratoire de Recherche et Développement
// de l'Epita.
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

#include <algorithm>
#include <deque>
#include <stack>
#include <utility>
#include <unordered_map>
#include <set>
#include <map>


#include <spot/misc/bddlt.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/simulation.hh>


namespace spot
{
  namespace node_helper
  {
    using brace_t = unsigned;
    void renumber(std::vector<brace_t>& braces,
                  const std::vector<unsigned>& decr_by);
    void truncate_braces(std::vector<brace_t>& braces,
                         const std::vector<unsigned>& rem_succ_of,
                         std::vector<size_t>& nb_braces);
  };

  class safra_state final
  {
  public:
    using state_t = unsigned;
    using color_t = unsigned;
    using bdd_id_t = unsigned;
    using nodes_t = std::map<state_t, std::vector<node_helper::brace_t>>;
    using succs_t = std::vector<std::pair<safra_state, bdd_id_t>>;
    using safra_node_t = std::pair<state_t, std::vector<node_helper::brace_t>>;

    bool operator<(const safra_state& other) const;
    // Printh the number of states in each brace
    safra_state(state_t state_number, bool init_state = false,
                bool acceptance_scc = false);
    // Given a certain transition_label, compute all the successors of that
    // label, and return that new node.
    void
    compute_succs(const const_twa_graph_ptr& aut,
                  succs_t& res,
                  const scc_info& scc,
                  const std::vector<bdd>& implications,
                  const std::vector<bool>& is_connected,
                  std::unordered_map<bdd, unsigned, bdd_hash>& bdd2num,
                  std::vector<bdd>& all_bdds,
                  bool use_scc,
                  bool use_simulation,
                  bool use_stutter) const;
    // Compute successor for transition ap
    safra_state
    compute_succ(const const_twa_graph_ptr& aut,
                 const bdd& ap,
                 const scc_info& scc,
                 const std::vector<bdd>& implications,
                 const std::vector<bool>& is_connected,
                 bool use_scc,
                 bool use_simulation) const;
    // The outermost brace of each node cannot be green
    void ungreenify_last_brace();
    // When a nodes a implies a node b, remove the node a.
    void merge_redundant_states(const std::vector<bdd>& implications,
                                const scc_info& scc,
                                const std::vector<bool>& is_connected);
    // Used when creating the list of successors
    // A new intermediate node is created with  src's braces and with dst as id
    // A merge is done if dst already existed in *this
    void update_succ(const std::vector<node_helper::brace_t>& braces,
                     state_t dst, const acc_cond::mark_t acc);
    // Return the emitted color, red or green
    color_t finalize_construction();
    // A list of nodes similar to the ones of a
    // safra tree.  These are constructed in the same way as the powerset
    // algorithm.
    nodes_t nodes_;
    // A counter that indicates the nomber of states within a brace.
    // This enables us to compute the red value
    std::vector<size_t> nb_braces_;
    // A bitfield to know if a brace can emit green.
    std::vector<bool> is_green_;
    color_t color_;
  };

  namespace
  {
    using power_set = std::map<safra_state, int>;
    const char* const sub[10] =
      {
        "\u2080",
        "\u2081",
        "\u2082",
        "\u2083",
        "\u2084",
        "\u2085",
        "\u2086",
        "\u2087",
        "\u2088",
        "\u2089",
      };

    std::string subscript(unsigned start)
    {
      std::string res;
      do
        {
          res = sub[start % 10] + res;
          start /= 10;
        }
      while (start);
      return res;
    }

    // Returns true if lhs has a smaller nesting pattern than rhs
    // If lhs and rhs are the same, return false.
    bool nesting_cmp(const std::vector<node_helper::brace_t>& lhs,
                     const std::vector<node_helper::brace_t>& rhs)
    {
      size_t m = std::min(lhs.size(), rhs.size());
      size_t i = 0;
      for (; i < m; ++i)
        {
          if (lhs[i] != rhs[i])
            return lhs[i] < rhs[i];
        }
      return lhs.size() > rhs.size();
    }

    // Used to remove all acceptance whos value is above and equal max_acc
    void remove_dead_acc(twa_graph_ptr& aut, unsigned max_acc)
    {
      assert(max_acc < 32);
      unsigned mask = (1 << max_acc) - 1;
      for (auto& t: aut->edges())
        {
          t.acc &= mask;
        }
    }

    struct compare
    {
      bool
      operator() (const safra_state::safra_node_t& lhs,
                  const safra_state::safra_node_t& rhs)
      {
        return lhs.second < rhs.second;
      }
    };

    // Return the sorteds nodes in ascending order
    std::vector<safra_state::safra_node_t>
    sorted_nodes(const safra_state::nodes_t& nodes)
    {
      std::vector<safra_state::safra_node_t> res;
      for (auto& n: nodes)
        res.emplace_back(n.first, n.second);
      std::sort(res.begin(), res.end(), compare());
      return res;
    }

    std::string
    nodes_to_string(const safra_state::nodes_t& states)
    {
      auto copy = sorted_nodes(states);
      std::ostringstream os;
      std::stack<unsigned> s;
      bool first = true;
      for (auto& n: copy)
        {
          auto it = n.second.begin();
          // Find brace on top of stack in vector
          // If brace is not present, then we close it as no other ones of that
          // type will be found since we ordered our vector
          while (!s.empty())
            {
              it = std::lower_bound(n.second.begin(), n.second.end(),
                                    s.top());
              if (it == n.second.end() || *it != s.top())
                {
                  os << subscript(s.top()) << '}';
                  s.pop();
                }
              else
                {
                  if (*it == s.top())
                    ++it;
                  break;
                }
            }
          // Add new braces
          while (it != n.second.end())
            {
              os << '{' << subscript(*it);
              s.push(*it);
              ++it;
              first = true;
            }
          if (!first)
            os << ' ';
          os << n.first;
          first = false;
        }
      // Finish unwinding stack to print last braces
      while (!s.empty())
        {
          os << subscript(s.top()) << '}';
          s.pop();
        }
      return os.str();
    }

    std::vector<std::string>*
    print_debug(std::map<safra_state, int>& states)
    {
      auto res = new std::vector<std::string>(states.size());
      for (auto& p: states)
        (*res)[p.second] = nodes_to_string(p.first.nodes_);
      return res;
    }

  }


  std::vector<bool> find_scc_paths(const scc_info& scc);

  safra_state
  safra_state::compute_succ(const const_twa_graph_ptr& aut,
                            const bdd& ap,
                            const scc_info& scc,
                            const std::vector<bdd>& implications,
                            const std::vector<bool>& is_connected,
                            bool use_scc,
                            bool use_simulation) const
  {
    safra_state ss = safra_state(nb_braces_.size());
    for (auto& node: nodes_)
      {
        for (auto& t: aut->out(node.first))
          {
            if (!bdd_implies(ap, t.cond))
              continue;
            // Check if we are leaving the SCC, if so we delete all the
            // braces as no cycles can be found with that node
            if (use_scc && scc.scc_of(node.first) != scc.scc_of(t.dst))
              if (scc.is_accepting_scc(scc.scc_of(t.dst)))
                // Entering accepting SCC so add brace
                ss.update_succ({ /* no braces */ }, t.dst, { 0 });
              else
                // When entering non accepting SCC don't create any braces
                ss.update_succ({ /* no braces */ }, t.dst, { /* empty */ });
            else
              ss.update_succ(node.second, t.dst, t.acc);
            assert(ss.nb_braces_.size() == ss.is_green_.size());
          }
      }
    if (use_simulation)
      ss.merge_redundant_states(implications, scc, is_connected);
    ss.ungreenify_last_brace();
    ss.color_ = ss.finalize_construction();
    return ss;
  }

  void
  safra_state::compute_succs(const const_twa_graph_ptr& aut,
                             succs_t& res,
                             const scc_info& scc,
                             const std::vector<bdd>& implications,
                             const std::vector<bool>& is_connected,
                             std::unordered_map<bdd, unsigned, bdd_hash>&
                             bdd2num,
                             std::vector<bdd>& all_bdds,
                             bool use_scc,
                             bool use_simulation,
                             bool use_stutter) const
  {
    for (auto& ap: all_bdds)
      {
        safra_state ss = *this;

        if (use_stutter && aut->prop_stutter_invariant())
          {
            std::vector<color_t> colors;
            unsigned int counter = 0;
            std::map<safra_state, unsigned int> safra2id;
            bool stop = false;
            while (!stop)
              {
                auto pair = safra2id.insert({ss, counter++});
                // insert should never fail
                assert(pair.second);
                ss = ss.compute_succ(aut, ap, scc, implications, is_connected,
                                     use_scc, use_simulation);
                colors.emplace_back(ss.color_);
                stop = safra2id.find(ss) != safra2id.end();
              }
            // Add color of final transition that loops back
            colors.emplace_back(ss.color_);
            unsigned int loop_start = safra2id[ss];
            for (auto& min: safra2id)
              {
                if (min.second >= loop_start && ss < min.first)
                  ss = min.first;
              }
            ss.color_ = *std::min_element(colors.begin(), colors.end());
          }
        else
          ss = compute_succ(aut, ap, scc, implications, is_connected,
                            use_scc, use_simulation);
        unsigned bdd_idx = bdd2num[ap];
        res.emplace_back(ss, bdd_idx);
      }
  }

  void
  safra_state::merge_redundant_states(const std::vector<bdd>& implications,
                                      const scc_info& scc,
                                      const std::vector<bool>& is_connected)
  {
    std::vector<int> to_remove;
    for (auto& n1: nodes_)
      for (auto& n2: nodes_)
        {
          if (n1 == n2)
            continue;
          // index to see if there is a path from scc2 -> scc1
          unsigned idx = scc.scc_count() * scc.scc_of(n2.first) +
            scc.scc_of(n1.first);
          if (!is_connected[idx] && bdd_implies(implications.at(n1.first),
                                                implications.at(n2.first)))
            to_remove.emplace_back(n1.first);
        }
    for (auto& n: to_remove)
      {
        for (auto& brace: nodes_[n])
          --nb_braces_[brace];
        nodes_.erase(n);
      }
  }

  void safra_state::ungreenify_last_brace()
  {
    // Step A4: For a brace to emit green it must surround other braces.
    // Hence, the last brace cannot emit green as it is the most inside brace.
    for (auto& n: nodes_)
      {
        if (!n.second.empty())
          is_green_[n.second.back()] = false;
      }
  }

  safra_state::color_t safra_state::finalize_construction()
  {
    unsigned red = -1U;
    unsigned green = -1U;
    std::vector<unsigned> rem_succ_of;
    assert(is_green_.size() == nb_braces_.size());
    for (unsigned i = 0; i < is_green_.size(); ++i)
      {
        if (nb_braces_[i] == 0)
          {
            // Step A3: Brackets that do not contain any nodes emit red
            is_green_[i] = false;

            // First brace can now be zero with new optim making it possible to
            // emit red 0
            red = std::min(red, 2 * i);
          }
        else if (is_green_[i])
          {
            green = std::min(green, 2 * i + 1);
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
                                state_t dst, const acc_cond::mark_t acc)
  {
    std::vector<node_helper::brace_t> copy = braces;
    if (acc.count())
      {
        assert(acc.has(0) && acc.count() == 1 && "Only TBA are accepted");
        // Accepting edge generate new braces: step A1
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
        // Step A2: Only keep the smallest nesting pattern (i-e  braces_) for
        // identical nodes.  Nesting_cmp returnes true if copy is smaller
        if (nesting_cmp(copy, i.first->second))
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
  }

  // Called only to initialize first state
  safra_state::safra_state(state_t val, bool init_state, bool accepting_scc)
  {
    if (init_state)
      {
        unsigned state_num = val;
        if (!accepting_scc)
          {
            std::vector<node_helper::brace_t> braces = { /* no braces */ };
            nodes_.emplace(state_num, std::move(braces));
          }
        else
          {
            std::vector<node_helper::brace_t> braces = { 0 };
            nodes_.emplace(state_num, std::move(braces));
            // First brace has init_state hence one state inside the first
            // braces.
            nb_braces_.emplace_back(1);
            // One brace set
            is_green_.push_back(true);
          }
      }
    else
      {
        unsigned nb_braces = val;
        // One brace set
        is_green_.assign(nb_braces, true);
        // Newly created states are the empty mocrstate
        nb_braces_.assign(nb_braces, 0);
      }
  }

  bool
  safra_state::operator<(const safra_state& other) const
  {
    if (nodes_ == other.nodes_)
      {
        for (auto& n: nodes_)
          {
            auto it = other.nodes_.find(n.first);
            assert(it != other.nodes_.end());
            if (nesting_cmp(n.second, it->second))
              return true;
          }
        return false;
      }

    return nodes_ < other.nodes_;
  }

  std::vector<bool>
  find_scc_paths(const scc_info& scc)
  {
    unsigned scccount = scc.scc_count();
    std::vector<bool> res(scccount * scccount, 0);
    for (unsigned i = 0; i < scccount; ++i)
      res[i + scccount * i] = 1;
    for (unsigned i = 0; i < scccount; ++i)
      {
        std::stack<unsigned> s;
        s.push(i);
        while (!s.empty())
          {
            unsigned src = s.top();
            s.pop();
            for (auto& d: scc.succ(src))
              {
                s.push(d);
                unsigned idx = scccount * i + d;
                res[idx] = 1;
              }
          }
      }
    return res;
  }

  twa_graph_ptr
  tgba_determinize(const const_twa_graph_ptr& a,
                   bool pretty_print, bool use_scc,
                   bool use_simulation, bool use_stutter)
  {
    if (a->prop_deterministic())
      return std::const_pointer_cast<twa_graph>(a);

    // Degeneralize
    twa_graph_ptr aut = spot::degeneralize_tba(a);
    std::vector<bdd> implications;
    if (use_simulation)
      {
        aut = spot::scc_filter(aut);
        aut = simulation(aut, &implications);
      }
    scc_info scc = scc_info(aut);
    std::vector<bool> is_connected = find_scc_paths(scc);

    bdd allap = bddtrue;
    {
      typedef std::set<bdd, bdd_less_than> sup_map;
      sup_map sup;
      // Record occurrences of all guards
      for (auto& t: aut->edges())
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
    std::vector<safra_state::bdd_id_t> bddnums;
    for (auto& t: aut->edges())
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
                  num2bdd.emplace_back(one);
                bddnums.emplace_back(p.first->second);
              }
            deltas[t.cond] = std::make_pair(prev, bddnums.size());
          }
      }

    auto res = make_twa_graph(aut->get_dict());
    res->copy_ap_of(aut);
    res->prop_copy(aut,
                   { false, // state based
                       false, // inherently_weak
                       false, // deterministic
                       true // stutter inv
                       });

    // Given a safra_state get its associated state in output automata.
    // Required to create new edges from 2 safra-state
    power_set seen;
    auto init_state = aut->get_init_state_number();
    bool start_accepting =
      !use_scc || scc.is_accepting_scc(scc.scc_of(init_state));
    safra_state init(init_state, true, start_accepting);
    unsigned num = res->new_state();
    res->set_init_state(num);
    seen.insert(std::make_pair(init, num));
    std::deque<safra_state> todo;
    todo.emplace_back(init);
    unsigned sets = 0;
    using succs_t = safra_state::succs_t;
    succs_t succs;
    while (!todo.empty())
      {
        safra_state curr = todo.front();
        unsigned src_num = seen.find(curr)->second;
        todo.pop_front();
        curr.compute_succs(aut, succs, scc, implications, is_connected,
                           bdd2num, num2bdd, use_scc, use_simulation,
                           use_stutter);
        for (auto s: succs)
          {
            // Don't construct sink state as complete does a better job at this
            if (s.first.nodes_.empty())
              continue;
            auto i = seen.find(s.first);
            unsigned dst_num;
            if (i != seen.end())
              {
                dst_num = i->second;
              }
            else
              {
                dst_num = res->new_state();
                todo.emplace_back(s.first);
                seen.insert(std::make_pair(s.first, dst_num));
              }
            if (s.first.color_ != -1U)
              {
                res->new_edge(src_num, dst_num, num2bdd[s.second],
                              {s.first.color_});
                // We only care about green acc which are odd
                if (s.first.color_ % 2 == 1)
                  sets = std::max(s.first.color_ + 1, sets);
              }
            else
              res->new_edge(src_num, dst_num, num2bdd[s.second]);
          }
        succs.clear();
      }
    remove_dead_acc(res, sets);
    // Acceptance is now min(odd) since we con emit Red on paths 0 with new opti
    res->set_acceptance(sets, acc_cond::acc_code::parity(false, true, sets));
    res->prop_deterministic(true);
    res->prop_state_acc(false);

    if (pretty_print)
      res->set_named_prop("state-names", print_debug(seen));
    return res;
  }
}
