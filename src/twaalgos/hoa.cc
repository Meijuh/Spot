// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2012, 2014, 2015 Laboratoire de Recherche et
// Developpement de l'Epita (LRDE).
// Copyright (C) 2003, 2004  Laboratoire d'Informatique de Paris 6 (LIP6),
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

#include <ostream>
#include <sstream>
#include <cstring>
#include <map>
#include "twa/twa.hh"
#include "twa/twagraph.hh"
#include "hoa.hh"
#include "reachiter.hh"
#include "misc/escape.hh"
#include "misc/bddlt.hh"
#include "misc/minato.hh"
#include "twa/formula2bdd.hh"
#include "ltlast/atomic_prop.hh"

namespace spot
{
  namespace
  {
    struct metadata final
    {
      // Assign a number to each atomic proposition.
      typedef std::map<int, unsigned> ap_map;
      ap_map ap;
      typedef std::vector<int> vap_t;
      vap_t vap;

      std::vector<bool> common_acc;
      bool has_state_acc;
      bool is_complete;
      bool is_deterministic;
      bool use_implicit_labels;
      bdd all_ap;

      // Label support: the set of all conditions occurring in the
      // automaton.
      typedef std::map<bdd, std::string, bdd_less_than> sup_map;
      sup_map sup;

      metadata(const const_twa_graph_ptr& aut, bool implicit)
      {
	check_det_and_comp(aut);
	use_implicit_labels = implicit && is_deterministic && is_complete;
	number_all_ap();
      }

      std::ostream&
      emit_acc(std::ostream& os,
	       const const_twa_graph_ptr& aut,
	       acc_cond::mark_t b)
      {
	// FIXME: We could use a cache for this.
	if (b == 0U)
	  return os;
	os << " {";
	bool notfirst = false;
	for (auto v: aut->acc().sets(b))
	  {
	    if (notfirst)
	      os << ' ';
	    else
	      notfirst = true;
	    os << v;
	  }
	os << '}';
	return os;
      }

      void check_det_and_comp(const const_twa_graph_ptr& aut)
      {
	std::string empty;

	unsigned ns = aut->num_states();
	bool deterministic = true;
	bool complete = true;
	bool state_acc = true;
	for (unsigned src = 0; src < ns; ++src)
	  {
	    bdd sum = bddfalse;
	    bdd available = bddtrue;
	    bool st_acc = true;
	    bool notfirst = false;
	    acc_cond::mark_t prev = 0U;
	    for (auto& t: aut->out(src))
	      {
		if (complete)
		  sum |= t.cond;
		if (deterministic)
		  {
		    if (!bdd_implies(t.cond, available))
		      deterministic = false;
		    else
		      available -= t.cond;
		  }
		sup.insert(std::make_pair(t.cond, empty));
		if (st_acc)
		  {
		    if (notfirst && prev != t.acc)
		      {
			st_acc = false;
		      }
		    else
		      {
			notfirst = true;
			prev = t.acc;
		      }
		  }
	      }
	    if (complete)
	      complete &= sum == bddtrue;
	    common_acc.push_back(st_acc);
	    state_acc &= st_acc;
	  }
	is_deterministic = deterministic;
	is_complete = complete;
	has_state_acc = state_acc;

	// If the automaton declares that it is deterministic or
	// state-based, make sure that it really is.
	assert(!aut->is_deterministic() || deterministic);
	assert(!aut->has_state_based_acc() || state_acc);
      }

      void number_all_ap()
      {
	bdd all = bddtrue;
	for (auto& i: sup)
	  all &= bdd_support(i.first);
	all_ap = all;

	while (all != bddtrue)
	  {
	    int v = bdd_var(all);
	    all = bdd_high(all);
	    ap.insert(std::make_pair(v, vap.size()));
	    vap.push_back(v);
	  }

	if (use_implicit_labels)
	  return;

	for (auto& i: sup)
	  {
	    bdd cond = i.first;
	    if (cond == bddtrue)
	      {
		i.second = "t";
		continue;
	      }
	    if (cond == bddfalse)
	      {
		i.second = "f";
		continue;
	      }
	    std::ostringstream s;
	    bool notfirstor = false;

	    minato_isop isop(cond);
	    bdd cube;
	    while ((cube = isop.next()) != bddfalse)
	      {
		if (notfirstor)
		  s << " | ";
		bool notfirstand = false;
		while (cube != bddtrue)
		  {
		    if (notfirstand)
		      s << '&';
		    else
		      notfirstand = true;
		    bdd h = bdd_high(cube);
		    if (h == bddfalse)
		      {
			s << '!' << ap[bdd_var(cube)];
			cube = bdd_low(cube);
		      }
		    else
		      {
			s << ap[bdd_var(cube)];
			cube = h;
		      }
		  }
		notfirstor = true;
	      }
	    i.second = s.str();
	  }
      }
    };

  }

  enum hoa_acceptance
    {
      Hoa_Acceptance_States,	/// state-based acceptance if
				/// (globally) possible
				/// transition-based acceptance
				/// otherwise.
      Hoa_Acceptance_Transitions, /// transition-based acceptance globally
      Hoa_Acceptance_Mixed    /// mix state-based and transition-based
    };

  static std::ostream&
  hoa_reachable(std::ostream& os,
		const const_twa_graph_ptr& aut,
		const char* opt)
  {
    bool newline = true;
    hoa_acceptance acceptance = Hoa_Acceptance_States;
    bool implicit_labels = false;

    if (opt)
      while (*opt)
	{
	  switch (*opt++)
	    {
	    case 'i':
	      implicit_labels = true;
	      break;
	    case 'l':
	      newline = false;
	      break;
	    case 'm':
	      acceptance = Hoa_Acceptance_Mixed;
	      break;
	    case 's':
	      acceptance = Hoa_Acceptance_States;
	      break;
	    case 't':
	      acceptance = Hoa_Acceptance_Transitions;
	      break;
	    }
	}

    // Calling get_init_state_number() may add a state to empty
    // automata, so it has to be done first.
    unsigned init = aut->get_init_state_number();

    metadata md(aut, implicit_labels);

    if (acceptance == Hoa_Acceptance_States && !md.has_state_acc)
      acceptance = Hoa_Acceptance_Transitions;

    unsigned num_states = aut->num_states();

    const char nl = newline ? '\n' : ' ';
    os << "HOA: v1" << nl;
    auto n = aut->get_named_prop<std::string>("automaton-name");
    if (n)
      escape_str(os << "name: \"", *n) << '"' << nl;
    unsigned nap = md.vap.size();
    os << "States: " << num_states << nl
       << "Start: " << init << nl
       << "AP: " << nap;
    auto d = aut->get_dict();
    for (auto& i: md.vap)
      {
	auto f = ltl::is_atomic_prop(d->bdd_map[i].f);
	assert(f);
	escape_str(os << " \"", f->name()) << '"';
      }
    os << nl;

    unsigned num_acc = aut->acc().num_sets();
    if (aut->acc().is_generalized_buchi())
      {
	if (aut->acc().is_true())
	  os << "acc-name: all";
	else if (aut->acc().is_buchi())
	  os << "acc-name: Buchi";
	else
	  os << "acc-name: generalized-Buchi " << num_acc;
	os << nl;
      }
    os << "Acceptance: " << num_acc << ' ';
    os << aut->acc().get_acceptance();
    os << nl;
    os << "properties:";

    // Make sure the property line is not too large,
    // otherwise our test cases do not fit in 80 columns...
    unsigned prop_len = 60;
    auto prop = [&](const char* str)
      {
	if (newline)
	  {
	    auto l = strlen(str);
	    if (prop_len < l)
	      {
		prop_len = 60;
		os << "\nproperties:";
	      }
	    prop_len -= l;
	  }
	os << str;
      };
    implicit_labels = md.use_implicit_labels;
    if (implicit_labels)
      prop(" implicit-labels");
    else
      prop(" trans-labels explicit-labels");
    if (acceptance == Hoa_Acceptance_States)
      prop(" state-acc");
    else if (acceptance == Hoa_Acceptance_Transitions)
      prop(" trans-acc");
    if (md.is_complete)
      prop(" complete");
    if (md.is_deterministic)
      prop(" deterministic");
    if (aut->is_stutter_invariant())
      prop(" stutter-invariant");
    if (aut->is_inherently_weak())
      prop(" inherently-weak");
    os << nl;

    // If we want to output implicit labels, we have to
    // fill a vector with all destinations in order.
    std::vector<unsigned> out;
    std::vector<acc_cond::mark_t> outm;
    if (implicit_labels)
      {
	out.resize(1UL << nap);
	if (acceptance != Hoa_Acceptance_States)
	  outm.resize(1UL << nap);
      }

    os << "--BODY--" << nl;
    auto sn = aut->get_named_prop<std::vector<std::string>>("state-names");
    for (unsigned i = 0; i < num_states; ++i)
      {
	hoa_acceptance this_acc = acceptance;
	if (this_acc == Hoa_Acceptance_Mixed)
	  this_acc = (md.common_acc[i] ?
		      Hoa_Acceptance_States : Hoa_Acceptance_Transitions);

	os << "State: " << i;
	if (sn && i < sn->size() && !(*sn)[i].empty())
	  os << " \"" << (*sn)[i] << '"';
	if (this_acc == Hoa_Acceptance_States)
	  {
	    acc_cond::mark_t acc = 0U;
	    for (auto& t: aut->out(i))
	      {
		acc = t.acc;
		break;
	      }
	    md.emit_acc(os, aut, acc);
	  }
	os << nl;

	if (!implicit_labels)
	  {
	    for (auto& t: aut->out(i))
	      {
		os << '[' << md.sup[t.cond] << "] " << t.dst;
		if (this_acc == Hoa_Acceptance_Transitions)
		  md.emit_acc(os, aut, t.acc);
		os << nl;
	      }
	  }
	else
	  {
	    for (auto& t: aut->out(i))
	      {
		bdd cond = t.cond;
		while (cond != bddfalse)
		  {
		    bdd one = bdd_satoneset(cond, md.all_ap, bddfalse);
		    cond -= one;
		    unsigned level = 1;
		    unsigned pos = 0U;
		    while (one != bddtrue)
		      {
			bdd h = bdd_high(one);
			if (h == bddfalse)
			  {
			    one = bdd_low(one);
			  }
			else
			  {
			    pos |= level;
			    one = h;
			  }
			level <<= 1;
		      }
		    out[pos] = t.dst;
		    if (this_acc != Hoa_Acceptance_States)
		      outm[pos] = t.acc;
		  }
	      }
	    unsigned n = out.size();
	    for (unsigned i = 0; i < n;)
	      {
		os << out[i];
		if (this_acc != Hoa_Acceptance_States)
		  {
		    md.emit_acc(os, aut, outm[i]) << nl;
		    ++i;
		  }
		else
		  {
		    ++i;
		    os << (((i & 15) && i < n) ? ' ' : nl);
		  }
	      }
	  }
      }
    os << "--END--";		// No newline.  Let the caller decide.
    return os;
  }

  std::ostream&
  hoa_reachable(std::ostream& os,
		const const_twa_ptr& aut,
		const char* opt)
  {

    auto a = std::dynamic_pointer_cast<const twa_graph>(aut);
    if (!a)
      a = make_twa_graph(aut, twa::prop_set::all());

    return hoa_reachable(os, a, opt);
  }

}
