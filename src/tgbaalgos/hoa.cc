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
#include <map>
#include "tgba/tgba.hh"
#include "tgba/tgbagraph.hh"
#include "hoa.hh"
#include "reachiter.hh"
#include "misc/escape.hh"
#include "misc/bddlt.hh"
#include "misc/minato.hh"
#include "tgba/formula2bdd.hh"
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

      // Label support: the set of all conditions occurring in the
      // automaton.
      typedef std::map<bdd, std::string, bdd_less_than> sup_map;
      sup_map sup;

      metadata(const const_tgba_digraph_ptr& aut)
      {
	check_det_and_comp(aut);
	number_all_ap();
      }

      std::ostream&
      emit_acc(std::ostream& os,
	       const const_tgba_digraph_ptr& aut,
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

      void check_det_and_comp(const const_tgba_digraph_ptr& aut)
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
      }

      void number_all_ap()
      {
	sup_map::iterator i;
	bdd all = bddtrue;
	for (auto& i: sup)
	  all &= bdd_support(i.first);

	while (all != bddtrue)
	  {
	    int v = bdd_var(all);
	    all = bdd_high(all);
	    ap.insert(std::make_pair(v, vap.size()));
	    vap.push_back(v);
	  }

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

  enum hoa_alias { Hoa_Alias_None, Hoa_Alias_Ap, Hoa_Alias_Cond };
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
		const const_tgba_digraph_ptr& aut,
		hoa_acceptance acceptance,
		hoa_alias alias,
		bool newline)
  {
    (void) alias;

    // Calling get_init_state_number() may add a state to empty
    // automata, so it has to be done first.
    unsigned init = aut->get_init_state_number();

    metadata md(aut);

    if (acceptance == Hoa_Acceptance_States && !md.has_state_acc)
      acceptance = Hoa_Acceptance_Transitions;

    unsigned num_states = aut->num_states();

    const char nl = newline ? '\n' : ' ';
    os << "HOA: v1" << nl;
    auto n = aut->get_named_prop<std::string>("automaton-name");
    if (n)
      escape_str(os << "name: \"", *n) << '"' << nl;
    os << "States: " << num_states << nl
       << "Start: " << init << nl
       << "AP: " << md.vap.size();
    auto d = aut->get_dict();
    for (auto& i: md.vap)
      {
	auto f = ltl::is_atomic_prop(d->bdd_map[i].f);
	assert(f);
	escape_str(os << " \"", f->name()) << '"';
      }
    os << nl;
    unsigned num_acc = aut->acc().num_sets();
    if (num_acc == 0)
      os << "acc-name: all";
    else if (num_acc == 1)
      os << "acc-name: Buchi";
    else
      os << "acc-name: generalized-Buchi " << num_acc;
    os << nl;
    os << "Acceptance: " << num_acc;
    if (num_acc > 0)
      {
	os << " Inf(0";
	for (unsigned i = 1; i < num_acc; ++i)
	  os << ")&Inf(" << i;
	os << ')';
      }
    else
      {
	os  << " t";
      }
    os << nl;
    os << "properties: trans-labels explicit-labels";
    if (acceptance == Hoa_Acceptance_States)
      os << " state-acc";
    else if (acceptance == Hoa_Acceptance_Transitions)
      os << " trans-acc";
    if (md.is_complete)
      os << " complete";
    if (md.is_deterministic)
      os << " deterministic";
    os << nl;
    os << "--BODY--" << nl;
    for (unsigned i = 0; i < num_states; ++i)
      {
	hoa_acceptance this_acc = acceptance;
	if (this_acc == Hoa_Acceptance_Mixed)
	  this_acc = (md.common_acc[i] ?
		      Hoa_Acceptance_States : Hoa_Acceptance_Transitions);

	os << "State: " << i;
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

	for (auto& t: aut->out(i))
	  {
	    os << '[' << md.sup[t.cond] << "] " << t.dst;
	    if (this_acc == Hoa_Acceptance_Transitions)
	      md.emit_acc(os, aut, t.acc);
	    os << nl;
	  }
      }
    os << "--END--";		// No newline.  Let the caller decide.
    return os;
  }

  std::ostream&
  hoa_reachable(std::ostream& os,
		const const_tgba_ptr& aut,
		const char* opt)
  {
    bool newline = true;
    hoa_acceptance acceptance = Hoa_Acceptance_States;
    hoa_alias alias = Hoa_Alias_None;

    if (opt)
      while (*opt)
	{
	  switch (*opt++)
	    {
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

    auto a = std::dynamic_pointer_cast<const tgba_digraph>(aut);
    if (!a)
      a = make_tgba_digraph(aut, tgba::prop_set::all());

    return hoa_reachable(os, a, acceptance, alias, newline);
  }

}
