// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2013, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2004  Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include "misc/hash.hh"
#include "replayrun.hh"
#include "tgba/tgba.hh"
#include "emptiness.hh"
#include "tgba/bddprint.hh"
#include <sstream>

namespace spot
{
  namespace
  {
    void
    print_annotation(std::ostream& os,
		     const const_tgba_ptr& a,
		     const tgba_succ_iterator* i)
    {
      std::string s = a->transition_annotation(i);
      if (s == "")
	return;
      os << ' ' << s;
    }
  }

  bool
  replay_tgba_run(std::ostream& os, const const_tgba_ptr& a,
		  const const_tgba_run_ptr& run, bool debug)
  {
    const state* s = a->get_init_state();
    int serial = 1;
    const tgba_run::steps* l;
    std::string in;
    acc_cond::mark_t all_acc = 0U;
    bool all_acc_seen = false;
    typedef std::unordered_map<const state*, std::set<int>,
			       state_ptr_hash, state_ptr_equal> state_map;
    state_map seen;

    if (run->prefix.empty())
      {
	l = &run->cycle;
	in = "cycle";
	if (!debug)
	  os << "No prefix.\nCycle:\n";
      }
    else
      {
	l = &run->prefix;
	in = "prefix";
	if (!debug)
	  os << "Prefix:\n";
      }

    tgba_run::steps::const_iterator i = l->begin();

    if (s->compare(i->s))
      {
	if (debug)
	  os << "ERROR: First state of run (in " << in << "): "
	     << a->format_state(i->s)
	     << "\ndoes not match initial state of automata: "
	     << a->format_state(s) << '\n';
	s->destroy();
	return false;
      }

    for (; i != l->end(); ++serial)
      {
	if (debug)
	  {
	    // Keep track of the serial associated to each state so we
	    // can note duplicate states and make the replay easier to read.
	    state_map::iterator o = seen.find(s);
	    std::ostringstream msg;
	    if (o != seen.end())
	      {
		for (auto d: o->second)
		  msg << " == " << d;
		o->second.insert(serial);
		s->destroy();
		s = o->first;
	      }
	    else
	      {
		seen[s].insert(serial);
	      }
	    os << "state " << serial << " in " << in << msg.str() << ": ";
	  }
	else
	  {
	    os << "  ";
	  }
	os << a->format_state(s) << '\n';

	// expected outgoing transition
	bdd label = i->label;
	acc_cond::mark_t acc = i->acc;

	// compute the next expected state
	const state* next;
	++i;
	if (i != l->end())
	  {
	    next = i->s;
	  }
	else
	  {
	    if (l == &run->prefix)
	      {
		l = &run->cycle;
		in = "cycle";
		i = l->begin();
		if (!debug)
		  os << "Cycle:\n";
	      }
	    next = l->begin()->s;
	  }

	// browse the actual outgoing transitions
	tgba_succ_iterator* j = a->succ_iter(s);
	// When not debugging, S is not used as key in SEEN, so we can
	// destroy it right now.
	if (!debug)
	  s->destroy();
	if (j->first())
	  do
	    {
	      if (j->current_condition() != label
		  || j->current_acceptance_conditions() != acc)
		continue;

	      const state* s2 = j->current_state();
	      if (s2->compare(next))
		{
		  s2->destroy();
		  continue;
		}
	      else
		{
		  s = s2;
		  break;
		}
	    }
	  while (j->next());
	if (j->done())
	  {
	    if (debug)
	      {
		os << "ERROR: no transition with label="
		   << bdd_format_formula(a->get_dict(), label)
		   << " and acc=" << a->acc().format(acc)
		   << " leaving state " << serial
		   << " for state " << a->format_state(next) << '\n'
		   << "The following transitions leave state " << serial
		   << ":\n";
		if (j->first())
		  do
		    {
		      const state* s2 = j->current_state();
		      os << "  *";
		      print_annotation(os, a, j);
		      os << " label="
			 << bdd_format_formula(a->get_dict(),
					       j->current_condition())
			 << " and acc="
			 << a->acc().format(j->current_acceptance_conditions())
			 << " going to " << a->format_state(s2) << '\n';
		      s2->destroy();
		    }
		  while (j->next());
	      }
	    a->release_iter(j);
	    s->destroy();
	    return false;
	  }
	if (debug)
	  {
	    os << "transition";
	    print_annotation(os, a, j);
	    os << " with label="
	       << bdd_format_formula(a->get_dict(), label)
	       << " and acc=" << a->acc().format(acc)
	       << std::endl;
	  }
	else
	  {
	    os << "  |  ";
	    print_annotation(os, a, j);
	    bdd_print_formula(os, a->get_dict(), label);
	    os << '\t';
	    a->acc().format(acc);
	    os << std::endl;
	  }
	a->release_iter(j);

	// Sum acceptance conditions.
	//
	// (Beware l and i designate the next step to consider.
	// Therefore if i is at the beginning of the cycle, `acc'
	// contains the acceptance conditions of the last transition
	// in the prefix; we should not account it.)
	if (l == &run->cycle && i != l->begin())
	  {
	    all_acc |= acc;
	    if (!all_acc_seen && a->acc().accepting(all_acc))
	      {
		all_acc_seen = true;
		if (debug)
		  os << "all acceptance conditions ("
		     << a->acc().format(all_acc)
		     << ") have been seen\n";
	      }
	  }
      }
    s->destroy();
    if (!a->acc().accepting(all_acc))
      {
	if (debug)
	  os << "ERROR: The cycle's acceptance conditions ("
	     << a->acc().format(all_acc)
	     << ") do not\nmatch those of the automaton ("
	     << a->acc().format(a->acc().all_sets())
	     << ")\n";
	return false;
      }

    state_map::const_iterator o = seen.begin();
    while (o != seen.end())
      {
	// Advance the iterator before deleting the "key" pointer.
	const state* ptr = o->first;
	++o;
	ptr->destroy();
      }

    return true;
  }
}
