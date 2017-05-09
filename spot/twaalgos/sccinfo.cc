// -*- coding: utf-8 -*-
// Copyright (C) 2014-2017 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include <spot/twaalgos/sccinfo.hh>
#include <stack>
#include <algorithm>
#include <queue>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/mask.hh>
#include <spot/misc/escape.hh>


namespace spot
{

  namespace
  {
    struct scc
    {
    public:
      scc(int index, acc_cond::mark_t in_acc):
        in_acc(in_acc), index(index)
      {
      }

      acc_cond::mark_t in_acc;  // Acceptance sets on the incoming transition
      acc_cond::mark_t acc = 0U; // union of all acceptance sets in the SCC
      int index;                // Index of the SCC
      bool trivial = true;        // Whether the SCC has no cycle
      bool accepting = false;        // Necessarily accepting
    };
  }

  scc_info::scc_info(const_twa_graph_ptr aut)
    : aut_(aut)
  {
    unsigned n = aut->num_states();
    sccof_.resize(n, -1U);

    std::deque<unsigned> live;
    std::deque<scc> root_;        // Stack of SCC roots.
    std::vector<int> h_(n, 0);
    // Map of visited states.  Values > 0 designate maximal SCC.
    // Values < 0 number states that are part of incomplete SCCs being
    // completed.  0 denotes non-visited states.

    int num_ = 0;               // Number of visited nodes, negated.

    struct stack_item {
      unsigned src;
      unsigned out_edge;
      unsigned univ_pos;
    };
    // DFS stack.  Holds (STATE, TRANS, UNIV_POS) pairs where TRANS is
    // the current outgoing transition of STATE, and UNIV_POS is used
    // when the transition is universal to iterate over all possible
    // destinations.
    std::stack<stack_item> todo_;
    auto& gr = aut->get_graph();

    // Setup depth-first search from the initial state.  But we may
    // have a conjunction of initial state in alternating automata.
    for (unsigned init: aut->univ_dests(aut->get_init_state_number()))
      {
        int spi = h_[init];
        if (spi > 0)
          continue;
        assert(spi == 0);
        h_[init] = --num_;
        root_.emplace_back(num_, 0U);
        todo_.emplace(stack_item{init, gr.state_storage(init).succ, 0});
        live.emplace_back(init);

        while (!todo_.empty())
          {
            // We are looking at the next successor in SUCC.
            unsigned tr_succ = todo_.top().out_edge;

            // If there is no more successor, backtrack.
            if (!tr_succ)
              {
                // We have explored all successors of state CURR.
                unsigned curr = todo_.top().src;

                // Backtrack TODO_.
                todo_.pop();

                // When backtracking the root of an SCC, we must also
                // remove that SCC from the ARC/ROOT stacks.  We must
                // discard from H all reachable states from this SCC.
                assert(!root_.empty());
                if (root_.back().index == h_[curr])
                  {
                    unsigned num = node_.size();
                    auto acc = root_.back().acc;
                    bool triv = root_.back().trivial;
                    node_.emplace_back(acc, triv);

                    // Move all elements of this SCC from the live stack
                    // to the the node.
                    auto i = std::find(live.rbegin(), live.rend(), curr);
                    assert(i != live.rend());
                    ++i;                // Because base() does -1
                    auto& nbs = node_.back().states_;
                    nbs.insert(nbs.end(), i.base(), live.end());
                    live.erase(i.base(), live.end());

                    std::set<unsigned> dests;
                    unsigned np1 = num + 1;
                    for (unsigned s: nbs)
                      {
                        sccof_[s] = num;
                        h_[s] = np1;
                      }
                    // Gather all successor SCCs
                    for (unsigned s: nbs)
                      for (auto& t: aut->out(s))
                        for (unsigned d: aut->univ_dests(t))
                          {
                            unsigned n = sccof_[d];
                            assert(n != -1U);
                            if (n == num)
                              continue;
                            dests.insert(n);
                          }
                    auto& succ = node_.back().succ_;
                    succ.insert(succ.end(), dests.begin(), dests.end());
                    bool accept = !triv && root_.back().accepting;
                    node_.back().accepting_ = accept;
                    bool reject = triv || !aut->acc().inf_satisfiable(acc);
                    // If the SCC acceptance is indeterminate, but has
                    // only self-loops with the same mark, it is
                    // necessarily rejecting, otherwise we would have
                    // found it to be accepting.
                    if (!accept && !reject && nbs.size() == 1)
                      {
                        acc_cond::mark_t selfacc = 0;
                        bool first = true;
                        reject = true;
                        for (const auto& e: aut->out(nbs.front()))
                          for (unsigned d: aut->univ_dests(e))
                            if (e.src == d)
                              {
                                if (first)
                                  {
                                    selfacc = e.acc;
                                    first = false;
                                  }
                                else if (selfacc != e.acc)
                                  {
                                    reject = false;
                                    goto break2;
                                  }
                              }
                      }
                  break2:
                    node_.back().rejecting_ = reject;
                    root_.pop_back();
                  }
                continue;
              }

            // We have a successor to look at.
            // Fetch the values we are interested in...
            auto& e = gr.edge_storage(tr_succ);
            unsigned dest = e.dst;
            if ((int) dest < 0)
              {
                // Iterate over all destinations of a universal edge.
                if (todo_.top().univ_pos == 0)
                  todo_.top().univ_pos = ~dest + 1;
                const auto& v = gr.dests_vector();
                dest = v[todo_.top().univ_pos];
                // Last universal destination?
                if (~e.dst + v[~e.dst] == todo_.top().univ_pos)
                  {
                    todo_.top().out_edge = e.next_succ;
                    todo_.top().univ_pos = 0;
                  }
                else
                  {
                    ++todo_.top().univ_pos;
                  }
              }
            else
              {
                todo_.top().out_edge = e.next_succ;
              }

            auto acc = e.acc;

            // Are we going to a new state?
            int spi = h_[dest];
            if (spi == 0)
              {
                // Yes.  Number it, stack it, and register its successors
                // for later processing.
                h_[dest] = --num_;
                root_.emplace_back(num_, acc);
                todo_.emplace(stack_item{dest, gr.state_storage(dest).succ, 0});
                live.emplace_back(dest);
                continue;
              }

            // We already know the state.

            // Have we reached a maximal SCC?
            if (spi > 0)
              continue;

            // Now this is the most interesting case.  We have reached a
            // state S1 which is already part of a non-dead SCC.  Any such
            // non-dead SCC has necessarily been crossed by our path to
            // this state: there is a state S2 in our path which belongs
            // to this SCC too.  We are going to merge all states between
            // this S1 and S2 into this SCC..
            //
            // This merge is easy to do because the order of the SCC in
            // ROOT is descending: we just have to merge all SCCs from the
            // top of ROOT that have an index lesser than the one of
            // the SCC of S2 (called the "threshold").
            int threshold = spi;
            bool is_accepting = false;
            // If this is a self-loop, check its acceptance alone.
            if (dest == e.src)
              is_accepting = aut->acc().accepting(acc);

            assert(!root_.empty());
            while (threshold > root_.back().index)
              {
                acc |= root_.back().acc;
                acc |= root_.back().in_acc;
                is_accepting |= root_.back().accepting;
                root_.pop_back();
                assert(!root_.empty());
              }

            // Note that we do not always have
            //  threshold == root_.back().index
            // after this loop, the SCC whose index is threshold might have
            // been merged with a higher SCC.

            // Accumulate all acceptance conditions, states, SCC
            // successors, and conditions into the merged SCC.
            root_.back().acc |= acc;
            root_.back().accepting |= is_accepting
              || aut->acc().accepting(root_.back().acc);
            // This SCC is no longer trivial.
            root_.back().trivial = false;
          }
      }
    determine_usefulness();
  }

  void scc_info::determine_usefulness()
  {
    // An SCC is useful if it is not rejecting or it has a successor
    // SCC that is useful.
    unsigned scccount = scc_count();
    for (unsigned i = 0; i < scccount; ++i)
      {
        if (!node_[i].is_rejecting())
          {
            node_[i].useful_ = true;
            continue;
          }
        node_[i].useful_ = false;
        for (unsigned j: node_[i].succ())
          if (node_[j].is_useful())
            {
              node_[i].useful_ = true;
              break;
            }
      }
  }


  std::set<acc_cond::mark_t> scc_info::used_acc_of(unsigned scc) const
  {
    std::set<acc_cond::mark_t> res;
    for (auto& t: inner_edges_of(scc))
      res.insert(t.acc);
    return res;
  }

  acc_cond::mark_t scc_info::acc_sets_of(unsigned scc) const
  {
    acc_cond::mark_t res = 0U;
    for (auto& t: inner_edges_of(scc))
      res |= t.acc;
    return res;
  }

  std::vector<std::set<acc_cond::mark_t>> scc_info::used_acc() const
  {
    unsigned n = aut_->num_states();
    std::vector<std::set<acc_cond::mark_t>> result(scc_count());

    for (unsigned src = 0; src < n; ++src)
      {
        unsigned src_scc = scc_of(src);
        if (src_scc == -1U || is_rejecting_scc(src_scc))
          continue;
        auto& s = result[src_scc];
        for (auto& t: aut_->out(src))
          {
            if (scc_of(t.dst) != src_scc)
              continue;
            s.insert(t.acc);
          }
      }
    return result;
  }

  std::vector<bool> scc_info::weak_sccs() const
  {
    unsigned n = scc_count();
    std::vector<bool> result(scc_count());
    auto acc = used_acc();
    for (unsigned s = 0; s < n; ++s)
      result[s] = is_rejecting_scc(s) || acc[s].size() == 1;
    return result;
  }

  bdd scc_info::scc_ap_support(unsigned scc) const
  {
    bdd support = bddtrue;
    for (auto& t: edges_of(scc))
      support &= bdd_support(t.cond);
    return support;
  }

  void scc_info::determine_unknown_acceptance()
  {
    if (!aut_->is_existential())
      throw std::runtime_error("scc_info::determine_unknown_acceptance() "
                               "does not support alternating automata");
    std::vector<bool> k;
    unsigned n = scc_count();
    bool changed = false;
    for (unsigned s = 0; s < n; ++s)
      if (!is_rejecting_scc(s) && !is_accepting_scc(s))
        {
          auto& node = node_[s];
          if (k.empty())
            k.resize(aut_->num_states());
          for (auto i: node.states_)
            k[i] = true;
          if (mask_keep_accessible_states(aut_, k, node.states_.front())
              ->is_empty())
            node.rejecting_ = true;
          else
            node.accepting_ = true;
          changed = true;
        }
    if (changed)
      determine_usefulness();
  }

  std::ostream&
  dump_scc_info_dot(std::ostream& out,
                    const_twa_graph_ptr aut, scc_info* sccinfo)
  {
    scc_info* m = sccinfo ? sccinfo : new scc_info(aut);

    out << "digraph G {\n  i [label=\"\", style=invis, height=0]\n";
    int start = m->scc_of(aut->get_init_state_number());
    out << "  i -> " << start << std::endl;

    std::vector<bool> seen(m->scc_count());
    seen[start] = true;

    std::queue<int> q;
    q.push(start);
    while (!q.empty())
      {
        int state = q.front();
        q.pop();

        out << "  " << state << " [shape=box,"
            << (aut->acc().accepting(m->acc(state)) ? "style=bold," : "")
            << "label=\"" << state;
        {
          size_t n = m->states_of(state).size();
          out << " (" << n << " state";
          if (n > 1)
            out << 's';
          out << ')';
        }
        out << "\"]\n";

        for (unsigned dest: m->succ(state))
          {
            out << "  " << state << " -> " << dest << '\n';
            if (seen[dest])
              continue;
            seen[dest] = true;
            q.push(dest);
          }
      }

    out << "}\n";
    if (!sccinfo)
      delete m;
    return out;
  }

}
