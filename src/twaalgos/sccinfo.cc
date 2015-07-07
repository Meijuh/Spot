// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et Développement
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

#include "sccinfo.hh"
#include <stack>
#include <algorithm>
#include <queue>
#include "twa/bddprint.hh"
#include "twaalgos/mask.hh"
#include "misc/escape.hh"

namespace spot
{

  namespace
  {
    struct scc
    {
    public:
      scc(int index, bdd in_cond, acc_cond::mark_t in_acc):
	index(index), in_cond(in_cond), in_acc(in_acc)
      {
      }

      int index;	 // Index of the SCC
      bdd in_cond;	 // Condition on incoming transition
      acc_cond::mark_t in_acc; // Acceptance sets on the incoming transition
      scc_info::scc_node node;
    };
  }

  scc_info::scc_info(const_twa_graph_ptr aut)
    : aut_(aut)
  {
    unsigned n = aut->num_states();
    sccof_.resize(n, -1U);

    typedef std::list<scc> stack_type;
    stack_type root_;		// Stack of SCC roots.
    std::vector<int> h_(n, 0);
    // Map of visited states.  Values > 0 designate maximal SCC.
    // Values < 0 number states that are part of incomplete SCCs being
    // completed.  0 denotes non-visited states.

    int num_;			// Number of visited nodes, negated.

    typedef twa_graph::graph_t::const_iterator iterator;
    typedef std::pair<unsigned, iterator> pair_state_iter;
    std::stack<pair_state_iter> todo_; // DFS stack.  Holds (STATE,
				       // ITERATOR) pairs where
				       // ITERATOR is an iterator over
				       // the successors of STATE.
				       // ITERATOR should always be
				       // freed when TODO is popped,
				       // but STATE should not because
				       // it is used as a key in H.


    // Setup depth-first search from the initial state.
    if (n > 0)
      {
	unsigned init = aut->get_init_state_number();
	num_ = -1;
	h_[init] = num_;
	root_.emplace_front(num_, bddfalse, 0U);
	todo_.emplace(init, aut->out(init).begin());
      }

    while (!todo_.empty())
      {
	// We are looking at the next successor in SUCC.
	iterator succ = todo_.top().second;

	// If there is no more successor, backtrack.
	if (!succ)
	  {
	    // We have explored all successors of state CURR.
	    unsigned curr = todo_.top().first;

	    // Backtrack TODO_.
	    todo_.pop();

	    // Fill STATES with any state removed, so that
	    // remove_component() does not have to traverse the SCC
	    // again.
	    root_.front().node.states_.push_front(curr);

	    // When backtracking the root of an SCC, we must also
	    // remove that SCC from the ARC/ROOT stacks.  We must
	    // discard from H all reachable states from this SCC.
	    assert(!root_.empty());
	    if (root_.front().index == h_[curr])
	      {
		int num = node_.size();
		for (auto s: root_.front().node.states_)
		  {
		    sccof_[s] = num;
		    h_[s] = num + 1;
		  }
		bdd cond = root_.front().in_cond;
		auto acc = root_.front().node.acc_marks();
		bool triv = root_.front().node.is_trivial();
		node_.emplace_back(acc, triv);
		std::swap(node_.back().succ_, root_.front().node.succ_);
		std::swap(node_.back().states_, root_.front().node.states_);
		node_.back().accepting_ =
		  !triv && root_.front().node.accepting_;
		node_.back().rejecting_ =
		  triv || !aut->acc().inf_satisfiable(acc);
		root_.pop_front();
		// Record the transition between the SCC being popped
		// and the previous SCC.
		if (!root_.empty())
		  root_.front().node.succ_.emplace_back(num);
	      }
	    continue;
	  }

	// We have a successor to look at.
	// Fetch the values we are interested in...
	unsigned dest = succ->dst;
	auto acc = succ->acc;
	bdd cond = succ->cond;
	++todo_.top().second;

	// We do not need SUCC from now on.

	// Are we going to a new state?
	int spi = h_[dest];
	if (spi == 0)
	  {
	    // Yes.  Number it, stack it, and register its successors
	    // for later processing.
	    h_[dest] = --num_;
	    root_.emplace_front(num_, cond, acc);
	    todo_.emplace(dest, aut->out(dest).begin());
	    continue;
	  }

	// We already know the state.

	// Have we reached a maximal SCC?
	if (spi > 0)
	  {
	    --spi;
	    // Record that there is a transition from this SCC to the
	    // dest SCC labelled with cond.
	    auto& succ = root_.front().node.succ_;
	    scc_succs::iterator i =
	      std::find(succ.begin(), succ.end(), (unsigned) spi);
	    if (i == succ.end())
	      succ.emplace_back(spi);
	    continue;
	  }

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
	std::list<unsigned> states;
	scc_succs succs;
	bool is_accepting = false;
	// If this is a self-loop, check its acceptance alone.
	if (dest == succ->src)
	  is_accepting = aut->acc().accepting(acc);

	assert(!root_.empty());
	while (threshold > root_.front().index)
	  {
	    acc |= root_.front().node.acc_;
	    acc |= root_.front().in_acc;
	    is_accepting |= root_.front().node.accepting_;
	    states.splice(states.end(), root_.front().node.states_);

	    succs.insert(succs.end(),
			 root_.front().node.succ_.begin(),
			 root_.front().node.succ_.end());
	    root_.pop_front();
	    assert(!root_.empty());
	  }

	// Note that we do not always have
	//  threshold == root_.front().index
	// after this loop, the SCC whose index is threshold might have
	// been merged with a higher SCC.

	// Accumulate all acceptance conditions, states, SCC
	// successors, and conditions into the merged SCC.
	root_.front().node.acc_ |= acc;
	root_.front().node.accepting_ |= is_accepting
	  || aut->acc().accepting(root_.front().node.acc_);
	root_.front().node.states_.splice(root_.front().node.states_.end(),
					  states);
	root_.front().node.succ_.insert(root_.front().node.succ_.end(),
					succs.begin(), succs.end());
	// This SCC is no longer trivial.
	root_.front().node.trivial_ = false;
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
    for (auto src: states_of(scc))
      for (auto& t: aut_->out(src))
	if (scc_of(t.dst) == scc)
	  res.insert(t.acc);
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
    for (auto s: states_of(scc))
      for (auto& t: aut_->out(s))
	support &= bdd_support(t.cond);
    return support;
  }

  void scc_info::determine_unknown_acceptance()
  {
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
	  if (mask_keep_states(aut_, k, node.states_.front())->is_empty())
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
