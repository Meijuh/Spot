// -*- coding: utf-8 -*-
// Copyright (C) 2008, 2009, 2010, 2012, 2013, 2014 Laboratoire de
// Recherche et Développement de l'Epita (LRDE).
// Copyright (C) 2004, 2005, 2007 Laboratoire d'Informatique de
// Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
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

#include "randomgraph.hh"
#include "tgba/tgbagraph.hh"
#include "misc/random.hh"
#include "ltlast/atomic_prop.hh"
#include <sstream>
#include <list>
#include <set>
#include <iterator>
#include <vector>

namespace spot
{

  namespace
  {
    std::string
    acc(int n)
    {
      std::stringstream s;
      s << n;
      return "a" + s.str();
    }

    void
    random_labels(tgba_digraph* aut,
		  unsigned src,
		  unsigned dest,
		  int* props, int props_n, float t,
		  const std::list<bdd>& accs, float a)
    {
      int val = 0;
      int size = 0;
      bdd p = bddtrue;
      while (props_n)
	{
	  if (size == 8 * sizeof(int))
	    {
	      p &= bdd_ibuildcube(val, size, props);
	      props += size;
	      val = 0;
	      size = 0;
	    }
	  val <<= 1;
	  val |= (drand() < t);
	  ++size;
	  --props_n;
	}
      if (size > 0)
	p &= bdd_ibuildcube(val, size, props);

      bdd ac = bddfalse;
      for (std::list<bdd>::const_iterator i = accs.begin();
	   i != accs.end(); ++i)
	if (drand() < a)
	  ac |= *i;

      aut->new_transition(src, dest, p, ac);
    }
  }

  tgba*
  random_graph(int n, float d,
	       const ltl::atomic_prop_set* ap, bdd_dict* dict,
	       int n_acc, float a, float t,
	       ltl::environment* env)
  {
    assert(n > 0);
    auto res = new tgba_digraph(dict);

    int props_n = ap->size();
    int* props = new int[props_n];

    int pi = 0;
    for (auto i: *ap)
      props[pi++] = dict->register_proposition(i, res);

    std::list<bdd> accs;
    bdd allneg = bddtrue;
    for (int i = 0; i < n_acc; ++i)
      {
	const ltl::formula* f = env->require(acc(i));
	int v = dict->register_acceptance_variable(f, res);
	f->destroy();
	bdd b = bdd_nithvar(v);
	allneg &= b;
	accs.push_back(b);
      }
    res->set_acceptance_conditions(allneg);
    for (auto& i: accs)
      i = bdd_compose(allneg, i, bdd_var(i));

    // Using std::unordered_set instead of std::set for these sets is 3
    // times slower (tested on a 50000 nodes example).
    typedef std::set<int> node_set;
    node_set nodes_to_process;
    node_set unreachable_nodes;

    res->new_states(n);

    std::vector<unsigned> state_randomizer(n);
    state_randomizer[0] = 0;
    nodes_to_process.insert(0);

    for (int i = 1; i < n; ++i)
      {
	state_randomizer[i] = i;
	unreachable_nodes.insert(i);
      }

    // We want to connect each node to a number of successors between
    // 1 and n.  If the probability to connect to each successor is d,
    // the number of connected successors follows a binomial distribution.
    barand bin(n - 1, d);

    while (!nodes_to_process.empty())
      {
	auto src = *nodes_to_process.begin();
	nodes_to_process.erase(nodes_to_process.begin());

	// Choose a random number of successors (at least one), using
	// a binomial distribution.
	int nsucc = 1 + bin.rand();

	// Connect to NSUCC randomly chosen successors.  We want at
	// least one unreachable successors among these if there are
	// some.
	bool saw_unreachable = false;
	int possibilities = n;
	while (nsucc--)
	  {
	    // No connection to unreachable successors so far.  This
	    // is our last chance, so force it now.
	    if (nsucc == 0
		&& !saw_unreachable
		&& !unreachable_nodes.empty())
	      {
		// Pick a random unreachable node.
		int index = mrand(unreachable_nodes.size());
		node_set::const_iterator i = unreachable_nodes.begin();
		std::advance(i, index);

		// Link it from src.
		random_labels(res, src, *i, props, props_n, t, accs, a);
		nodes_to_process.insert(*i);
		unreachable_nodes.erase(i);
		break;
	      }
	    else
	      {
		// Pick the index of a random node.
		int index = mrand(possibilities--);

		// Permute it with state_randomizer[possibilities], so
		// we cannot pick it again.
		auto x = state_randomizer[index];
		state_randomizer[index] = state_randomizer[possibilities];
		state_randomizer[possibilities] = x;

		random_labels(res, src, x, props, props_n, t, accs, a);

		auto j = unreachable_nodes.find(x);
		if (j != unreachable_nodes.end())
		  {
		    nodes_to_process.insert(x);
		    unreachable_nodes.erase(j);
		    saw_unreachable = true;
		  }
	      }
	  }

	// The node must have at least one successor.
	assert(res->get_graph().state_storage(src).succ);
      }
    // All nodes must be reachable.
    assert(unreachable_nodes.empty());
    delete[] props;
    return res;
  }

}
