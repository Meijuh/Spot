// -*- coding: utf-8 -*-
// Copyright (C) 2013 Laboratoire de Recherche et Développement
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

#include <iostream>
#include <fstream>
#include <sstream>
#include "dtbasat.hh"
#include "reachiter.hh"
#include <map>
#include <utility>
#include "scc.hh"
#include "tgba/bddprint.hh"
#include "ltlast/constant.hh"
#include "stats.hh"
#include "misc/tmpfile.hh"
#include "misc/satsolver.hh"

// If the following DEBUG macro is set to 1, the temporary files used
// to communicate with the SAT-solver will be left in the current
// directory.  (The files dtba-sat.cnf and dtba-sat.out contain the
// input and output for the last successful minimization attempted, or
// for the only failed attempt if the minimization failed.)
//
// Additionally, the CNF file will be output with a comment before
// each clause, and an additional output file (dtba-sat.dbg) will be
// created with a list of all positive variables in the result and
// their meaning.
//
// Note that the code use unique temporary filenames, so it is safe to
// run several such minimizations in parallel.  It only when DEBUG=1
// that some of these files will be renamed to the above hard-coded
// names, possibly causing confusion if multiple minimizations are
// debugged in parallel and in the same directory.

#define DEBUG 0
#if DEBUG
#define dout out << "c "
#define trace std::cerr
#else
#define dout while (0) std::cout
#define trace dout
#endif

namespace spot
{
  namespace
  {
    static bdd_dict* debug_dict = 0;

    struct transition
    {
      int src;
      bdd cond;
      int dst;

      transition(int src, bdd cond, int dst)
	: src(src), cond(cond), dst(dst)
      {
      }

      bool operator<(const transition& other) const
      {
	if (this->src < other.src)
	  return true;
	if (this->src > other.src)
	  return false;
	if (this->dst < other.dst)
	  return true;
	if (this->dst > other.dst)
	  return false;
	return this->cond.id() < other.cond.id();
      }

      bool operator==(const transition& other) const
      {
	return (this->src == other.src
		&& this->dst == other.dst
		&& this->cond.id() == other.cond.id());
      }
    };

    struct src_cond
    {
      int src;
      bdd cond;

      src_cond(int src, bdd cond)
	: src(src), cond(cond)
      {
      }

      bool operator<(const src_cond& other) const
      {
	if (this->src < other.src)
	  return true;
	if (this->src > other.src)
	  return false;
	return this->cond.id() < other.cond.id();
      }

      bool operator==(const src_cond& other) const
      {
	return (this->src == other.src
		&& this->cond.id() == other.cond.id());
      }
    };

    struct state_pair
    {
      int a;
      int b;

      state_pair(int a, int b)
	: a(a), b(b)
      {
      }

      bool operator<(const state_pair& other) const
      {
	if (this->a < other.a)
	  return true;
	if (this->a > other.a)
	  return false;
	if (this->b < other.b)
	  return true;
	if (this->b > other.b)
	  return false;
	return false;
      }
    };

    struct path
    {
      int src_cand;
      int src_ref;
      int dst_cand;
      int dst_ref;

      path(int src_cand, int src_ref,
	   int dst_cand, int dst_ref)
	: src_cand(src_cand), src_ref(src_ref),
	  dst_cand(dst_cand), dst_ref(dst_ref)
      {
      }

      bool operator<(const path& other) const
      {
	if (this->src_cand < other.src_cand)
	  return true;
	if (this->src_cand > other.src_cand)
	  return false;
	if (this->src_ref < other.src_ref)
	  return true;
	if (this->src_ref > other.src_ref)
	  return false;
	if (this->dst_cand < other.dst_cand)
	  return true;
	if (this->dst_cand > other.dst_cand)
	  return false;
	if (this->dst_ref < other.dst_ref)
	  return true;
	if (this->dst_ref > other.dst_ref)
	  return false;
	return false;
      }

    };

    std::ostream& operator<<(std::ostream& os, const state_pair& p)
    {
      os << "<" << p.a << "," << p.b << ">";
      return os;
    }

    std::ostream& operator<<(std::ostream& os, const transition& t)
    {
      os << "<" << t.src << ","
	 << bdd_format_formula(debug_dict, t.cond)
	 << "," << t.dst << ">";
      return os;
    }

    std::ostream& operator<<(std::ostream& os, const path& p)
    {
      os << "<"
	 << p.src_cand << ","
	 << p.src_ref << ","
	 << p.dst_cand << ","
	 << p.dst_ref << ">";
      return os;
    }

    struct dict
    {
      typedef std::map<transition, int> trans_map;
      trans_map transid;
      trans_map transacc;
      typedef std::map<int, transition> rev_map;
      rev_map revtransid;
      rev_map revtransacc;

      std::map<state_pair, int> prodid;
      std::map<path, int> pathid_ref;
      std::map<path, int> pathid_cand;
      int nvars;
      typedef Sgi::hash_map<const state*, int,
			    state_ptr_hash, state_ptr_equal> state_map;
      typedef Sgi::hash_map<int, const state*> int_map;
      state_map state_to_int;
      int_map int_to_state;
      int cand_size;

      ~dict()
      {
	state_map::const_iterator s = state_to_int.begin();
	while (s != state_to_int.end())
	  // Always advance the iterator before deleting the key.
	  s++->first->destroy();
      }
    };


    class filler_dfs: public tgba_reachable_iterator_depth_first
    {
    protected:
      dict& d;
      int size_;
      bdd ap_;
      bool state_based_;
      scc_map& sm_;
    public:
      filler_dfs(const tgba* aut, dict& d, bdd ap, bool state_based,
		 scc_map& sm)
	: tgba_reachable_iterator_depth_first(aut), d(d), ap_(ap),
	  state_based_(state_based), sm_(sm)
      {
	d.nvars = 0;
      }

      int size()
      {
	return size_;
      }

      void end()
      {
	size_ = seen.size();

	if (d.cand_size == -1)
	  d.cand_size = size_ - 1;

	for (dict::state_map::const_iterator i2 = seen.begin();
	     i2 != seen.end(); ++i2)
	  {
	    int i = i2->second;
	    d.int_to_state[i] = i2->first;
	    unsigned i_scc = sm_.scc_of_state(i2->first);

	    for (int j = 1; j <= d.cand_size; ++j)
	      {
		d.prodid[state_pair(j, i)] = ++d.nvars;

		if (sm_.trivial(i_scc))
		  continue;

		for (dict::state_map::const_iterator k2 = seen.begin();
		     k2 != seen.end(); ++k2)
		  {
		    int k = k2->second;
		    if (sm_.scc_of_state(k2->first) != i_scc)
		      continue;
		    for (int l = 1; l <= d.cand_size; ++l)
		    {
		      if (i == k && j == l)
			continue;
		      path p(j, i, l, k);
		      d.pathid_ref[p] = ++d.nvars;
		      d.pathid_cand[p] = ++d.nvars;
		    }
		  }
	      }
	  }

	std::swap(d.state_to_int, seen);

	for (int i = 1; i <= d.cand_size; ++i)
	  {
	    int transacc = -1;
	    if (state_based_)
	      // All outgoing transitions use the same acceptance variable.
	      transacc = ++d.nvars;

	    for (int j = 1; j <= d.cand_size; ++j)
	      {
		bdd all = bddtrue;
		while (all != bddfalse)
		  {
		    bdd one = bdd_satoneset(all, ap_, bddfalse);
		    all -= one;

		    transition t(i, one, j);
		    d.transid[t] = ++d.nvars;
		    d.revtransid.insert(dict::rev_map::value_type(d.nvars, t));
		    int ta = d.transacc[t] =
		      state_based_ ? transacc : ++d.nvars;
		    d.revtransacc.insert(dict::rev_map::value_type(ta, t));
		  }
	      }
	  }
      }
    };

    static
    void dtba_to_sat(std::ostream& out, const tgba* ref, dict& d,
		     bool state_based)
    {
      clause_counter nclauses;
      int ref_size = 0;

      scc_map sm(ref);
      sm.build_map();
      bdd ap = sm.aprec_set_of(sm.initial());

      // Count the number of atomic propositions
      int nap = 0;
      {
	bdd cur = ap;
	while (cur != bddtrue)
	  {
	    ++nap;
	    cur = bdd_high(cur);
	  }
	nap = 1 << nap;
      }

      // Number all the SAT variable we may need.
      {
	filler_dfs f(ref, d, ap, state_based, sm);
	f.run();
	ref_size = f.size();
      }

      // empty automaton is impossible
      if (d.cand_size == 0)
	{
	  out << "p cnf 1 2\n-1 0\n1 0\n";
	  return;
	}

      // An empty line for the header
      out << "                                                 \n";

#if DEBUG
      debug_dict = ref->get_dict();
      dout << "ref_size: " << ref_size << "\n";
      dout << "cand_size: " << d.cand_size << "\n";
#endif

      dout << "symmetry-breaking clauses\n";
      int j = 0;
      bdd all = bddtrue;
      while (all != bddfalse)
 	{
 	  bdd s = bdd_satoneset(all, ap, bddfalse);
 	  all -= s;
 	  for (int i = 1; i < d.cand_size; ++i)
 	    for (int k = (i - 1) * nap + j + 3; k <= d.cand_size; ++k)
	      {
		transition t(i, s, k);
		int ti = d.transid[t];
		dout << "¬" << t << "\n";
		out << -ti << " 0\n";
		++nclauses;
	      }
 	  ++j;
 	}
      if (!nclauses.nb_clauses())
 	dout << "(none)\n";

      dout << "(1) the candidate automaton is complete\n";
      for (int q1 = 1; q1 <= d.cand_size; ++q1)
	{
	  bdd all = bddtrue;
	  while (all != bddfalse)
	    {
	      bdd s = bdd_satoneset(all, ap, bddfalse);
	      all -= s;

#if DEBUG
	      dout;
	      for (int q2 = 1; q2 <= d.cand_size; q2++)
		{
		  transition t(q1, s, q2);
		  out << t << "δ";
		  if (q2 != d.cand_size)
		    out << " ∨ ";
		}
	      out << "\n";
#endif

	      for (int q2 = 1; q2 <= d.cand_size; q2++)
		{
		  transition t(q1, s, q2);
		  int ti = d.transid[t];

		  out << ti << " ";
		}
	      out << "0\n";

	      ++nclauses;
	    }
	}

      dout << "(2) the initial state is reachable\n";
      dout << state_pair(1, 1) << "\n";
      out << d.prodid[state_pair(1, 1)] << " 0\n";
      ++nclauses;

      for (std::map<state_pair, int>::const_iterator pit = d.prodid.begin();
	   pit != d.prodid.end(); ++pit)
	{
	  int q1 = pit->first.a;
	  int q1p = pit->first.b;

	  dout << "(3) augmenting paths based on Cand[" << q1
	       << "] and Ref[" << q1p << "]\n";
	  tgba_succ_iterator* it = ref->succ_iter(d.int_to_state[q1p]);
	  for (it->first(); !it->done(); it->next())
	    {
	      const state* dps = it->current_state();
	      int dp = d.state_to_int[dps];
	      dps->destroy();

	      bdd all = it->current_condition();
	      while (all != bddfalse)
		{
		  bdd s = bdd_satoneset(all, ap, bddfalse);
		  all -= s;

		  for (int q2 = 1; q2 <= d.cand_size; q2++)
		    {
		      transition t(q1, s, q2);
		      int ti = d.transid[t];

		      state_pair p2(q2, dp);
		      int succ = d.prodid[p2];

		      if (pit->second == succ)
			continue;

		      dout << pit->first << " ∧ " << t << "δ → " << p2 << "\n";
		      out << -pit->second << " " << -ti << " "
			  << succ << " 0\n";
		      ++nclauses;
		    }
		}
	    }
	  delete it;
	}

      bdd all_acc = ref->all_acceptance_conditions();

      // construction of contraints (4,5) : all loops in the product
      // where no accepting run is detected in the ref. automaton,
      // must also be marked as not accepting in the cand. automaton
      for (int q1p = 1; q1p <= ref_size; ++q1p)
	{
	  unsigned q1p_scc = sm.scc_of_state(d.int_to_state[q1p]);
	  if (sm.trivial(q1p_scc))
	    continue;
	  for (int q2p = 1; q2p <= ref_size; ++q2p)
	    {
	      // We are only interested in transition that can form a
	      // cycle, so they must belong to the same SCC.
	      if (sm.scc_of_state(d.int_to_state[q2p]) != q1p_scc)
		continue;
	      for (int q1 = 1; q1 <= d.cand_size; ++q1)
		for (int q2 = 1; q2 <= d.cand_size; ++q2)
		  {
		    path p1(q1, q1p, q2, q2p);

		    dout << "(4&5) matching paths from reference based on "
			 << p1 << "\n";

		    int pid1;
		    if (q1 == q2 && q1p == q2p)
		      pid1 = d.prodid[state_pair(q1, q1p)];
		    else
		      pid1 = d.pathid_ref[p1];

		    tgba_succ_iterator* it =
		      ref->succ_iter(d.int_to_state[q2p]);
		    for (it->first(); !it->done(); it->next())
		      {
			const state* dps = it->current_state();
			// Skip destinations not in the SCC.
			if (sm.scc_of_state(dps) != q1p_scc)
			  {
			    dps->destroy();
			    continue;
			  }
			int dp = d.state_to_int[dps];
			dps->destroy();

			if (it->current_acceptance_conditions() == all_acc)
			  continue;
			for (int q3 = 1; q3 <= d.cand_size; ++q3)
			  {
			    if (dp == q1p && q3 == q1) // (4) looping
			      {
				bdd all = it->current_condition();
				while (all != bddfalse)
				  {
				    bdd s = bdd_satoneset(all, ap, bddfalse);
				    all -= s;

				    transition t(q2, s, q1);
				    int ti = d.transid[t];
				    int ta = d.transacc[t];

				    dout << p1 << "R ∧ " << t << "δ → ¬" << t
					 << "F\n";
				    out << -pid1 << " " << -ti << " "
					<< -ta << " 0\n";
				    ++nclauses;
				  }


			      }
			    else // (5) not looping
			      {
				path p2 = path(q1, q1p, q3, dp);
				int pid2 = d.pathid_ref[p2];

				if (pid1 == pid2)
				  continue;

				bdd all = it->current_condition();
				while (all != bddfalse)
				  {
				    bdd s = bdd_satoneset(all, ap, bddfalse);
				    all -= s;

				    transition t(q2, s, q3);
				    int ti = d.transid[t];

				    dout << p1 << "R ∧ " << t << "δ → " << p2
					 << "R\n";
				    out << -pid1 << " " << -ti << " "
					<< pid2 << " 0\n";
				    ++nclauses;
				  }
			      }
			  }
		      }
		    delete it;
		  }
	    }
	}
      // construction of contraints (6,7): all loops in the product
      // where accepting run is detected in the ref. automaton, must
      // also be marked as accepting in the candidate.
      for (int q1p = 1; q1p <= ref_size; ++q1p)
	{
	  unsigned q1p_scc = sm.scc_of_state(d.int_to_state[q1p]);
	  if (sm.trivial(q1p_scc))
	    continue;
	  for (int q2p = 1; q2p <= ref_size; ++q2p)
	    {
	      // We are only interested in transition that can form a
	      // cycle, so they must belong to the same SCC.
	      if (sm.scc_of_state(d.int_to_state[q2p]) != q1p_scc)
		continue;
	      for (int q1 = 1; q1 <= d.cand_size; ++q1)
		for (int q2 = 1; q2 <= d.cand_size; ++q2)
		  {
		    path p1(q1, q1p, q2, q2p);
		    dout << "(6&7) matching paths from candidate based on "
			 << p1 << "\n";

		    int pid1;
		    if (q1 == q2 && q1p == q2p)
		      pid1 = d.prodid[state_pair(q1, q1p)];
		    else
		      pid1 = d.pathid_cand[p1];

		    tgba_succ_iterator* it =
		      ref->succ_iter(d.int_to_state[q2p]);
		    for (it->first(); !it->done(); it->next())
		      {
			const state* dps = it->current_state();
			// Skip destinations not in the SCC.
			if (sm.scc_of_state(dps) != q1p_scc)
			  {
			    dps->destroy();
			    continue;
			  }
			int dp = d.state_to_int[dps];
			dps->destroy();
			for (int q3 = 1; q3 <= d.cand_size; q3++)
			  {
			    if (dp == q1p && q3 == q1) // (6) looping
			      {
				// We only care about the looping case if
				// it is accepting in the reference.
				if (it->current_acceptance_conditions()
				    != all_acc)
				  continue;
				bdd all = it->current_condition();
				while (all != bddfalse)
				  {
				    bdd s = bdd_satoneset(all, ap, bddfalse);
				    all -= s;

				    transition t(q2, s, q1);
				    int ti = d.transid[t];
				    int ta = d.transacc[t];

				    dout << p1 << "C ∧ " << t << "δ → " << t
					 << "F\n";
				    out << -pid1 << " " << -ti << " " << ta
					<< " 0\n";
				    ++nclauses;
				  }
			      }
			    else // (7) no loop
			      {
				path p2 = path(q1, q1p, q3, dp);
				int pid2 = d.pathid_cand[p2];

				if (pid1 == pid2)
				  continue;

				bdd all = it->current_condition();
				while (all != bddfalse)
				  {
				    bdd s = bdd_satoneset(all, ap, bddfalse);
				    all -= s;

				    transition t(q2, s, q3);
				    int ti = d.transid[t];
				    int ta = d.transacc[t];

				    dout << p1 << "C ∧ " << t << "δ ∧ ¬"
					 << t << "F → " << p2 << "C\n";

				    out << -pid1 << " " << -ti << " "
					<< ta << " " << pid2 << " 0\n";
				    ++nclauses;
				  }
			      }
			  }
		      }
		    delete it;
		  }
	    }
	}
      out.seekp(0);
      out << "p cnf " << d.nvars << " " << nclauses.nb_clauses();
    }

    static tgba_explicit_number*
    sat_build(const sat_solution& solution, dict& satdict, const tgba* aut,
	      bool state_based)
    {
      bdd_dict* autdict = aut->get_dict();
      tgba_explicit_number* a = new tgba_explicit_number(autdict);
      autdict->register_all_variables_of(aut, a);

      const ltl::formula* t = ltl::constant::true_instance();
      bdd acc = bdd_ithvar(autdict->register_acceptance_variable(t, a));
      a->set_acceptance_conditions(acc);

      for (int s = 1; s < satdict.cand_size; ++s)
	a->add_state(s);

      state_explicit_number::transition* last_aut_trans = 0;
      const transition* last_sat_trans = 0;

#if DEBUG
      std::fstream out("dtba-sat.dbg",
		       std::ios_base::trunc | std::ios_base::out);
      out.exceptions(std::ifstream::failbit | std::ifstream::badbit);
      std::set<int> positive;
#endif

      dout << "--- transition variables ---\n";
      std::set<int> acc_states;
      std::set<src_cond> seen_trans;
      for (sat_solution::const_iterator i = solution.begin();
	   i != solution.end(); ++i)
	{
	  int v = *i;

	  if (v < 0)  // FIXME: maybe we can have (v < NNN)?
	    continue;

#if DEBUG
	  positive.insert(v);
#endif

	  dict::rev_map::const_iterator t = satdict.revtransid.find(v);

	  if (t != satdict.revtransid.end())
	    {
	      // Skip (s,l,d2) if we have already seen some (s,l,d1).
	      if (seen_trans.insert(src_cond(t->second.src,
					     t->second.cond)).second)
		{
		  last_aut_trans = a->create_transition(t->second.src,
							t->second.dst);
		  last_aut_trans->condition = t->second.cond;
		  last_sat_trans = &t->second;

		  dout << v << "\t" << t->second << "δ\n";

		  // Mark the transition as accepting if the source is.
		  if (state_based
		      && acc_states.find(t->second.src) != acc_states.end())
		    last_aut_trans->acceptance_conditions = acc;
		}
	    }
	  else
	    {
	      t = satdict.revtransacc.find(v);
	      if (t != satdict.revtransacc.end())
		{
		  dout << v << "\t" << t->second << "F\n";
		  if (last_sat_trans && t->second == *last_sat_trans)
		    {
		      assert(!state_based);
		      // This assumes that the SAT solvers output
		      // variables in increasing order.
		      last_aut_trans->acceptance_conditions = acc;
		    }
		  else if (state_based)
		    {
		      // Accepting translations actually correspond to
		      // states and are announced before listing
		      // outgoing transitions.  Again, this assumes
		      // that the SAT solvers output variables in
		      // increasing order.
		      acc_states.insert(t->second.src);
		    }
		}
	    }
	}
#if DEBUG
      dout << "--- state_pair variables ---\n";
      for (std::map<state_pair, int>::const_iterator pit =
	     satdict.prodid.begin(); pit != satdict.prodid.end(); ++pit)
	if (positive.find(pit->second) != positive.end())
	  dout << pit->second << "\t" << pit->first << "\n";

      dout << "--- pathid_cand variables ---\n";
      for (std::map<path, int>::const_iterator pit =
	     satdict.pathid_cand.begin();
	   pit != satdict.pathid_cand.end(); ++pit)
	if (positive.find(pit->second) != positive.end())
	  dout << pit->second << "\t" << pit->first << "C\n";

      dout << "--- pathid_ref variables ---\n";
      for (std::map<path, int>::const_iterator pit =
	     satdict.pathid_ref.begin();
	   pit != satdict.pathid_ref.end(); ++pit)
	if (positive.find(pit->second) != positive.end())
	  dout << pit->second << "\t" << pit->first << "R\n";
#endif

      a->merge_transitions();
      return a;
    }

    static bool
    xrename(const char* from, const char* to)
    {
      if (!rename(from, to))
	return false;
      std::ostringstream msg;
      msg << "cannot rename " << from << " to " << to;
      perror(msg.str().c_str());
      return true;
    }
  }

  tgba_explicit_number*
  dtba_sat_synthetize(const tgba* a, int target_state_number,
		      bool state_based)
  {
    trace << "dtba_sat_synthetize(..., states = " << target_state_number
	  << ", state_based = " << state_based << ")\n";
    dict* current = 0;
    temporary_file* cnf = 0;
    temporary_file* out = 0;

    current = new dict;
    current->cand_size = target_state_number;

    try
      {
	cnf = create_tmpfile("dtba-sat-", ".cnf");
	std::fstream cnfs(cnf->name(),
			  std::ios_base::trunc | std::ios_base::out);
	cnfs.exceptions(std::ifstream::failbit | std::ifstream::badbit);
	dtba_to_sat(cnfs, a, *current, state_based);
	cnfs.close();
      }
    catch (...)
      {
	if (DEBUG)
	  xrename(cnf->name(), "dtba-sat.cnf");
	delete current;
	delete cnf;
	throw;
      }

    out = create_tmpfile("dtba-sat-", ".out");
    satsolver(cnf, out);

    sat_solution solution = satsolver_get_solution(out->name());

    tgba_explicit_number* res = 0;
    if (!solution.empty())
      res = sat_build(solution, *current, a, state_based);

    delete current;

    if (DEBUG)
      {
	xrename(out->name(), "dtba-sat.out");
	xrename(cnf->name(), "dtba-sat.cnf");
      }

    delete out;
    delete cnf;
    trace << "dtba_sat_synthetize(...) = " << res << "\n";
    return res;
  }

  tgba_explicit_number*
  dtba_sat_minimize(const tgba* a, bool state_based)
  {
    int n_states = stats_reachable(a).states;

    tgba_explicit_number* prev = 0;
    for (;;)
      {
	tgba_explicit_number* next =
	  dtba_sat_synthetize(prev ? prev : a, --n_states, state_based);
	if (next == 0)
	  break;
	delete prev;
	prev = next;
      }
    return prev;
  }

  tgba_explicit_number*
  dtba_sat_minimize_dichotomy(const tgba* a, bool state_based)
  {
    int max_states = stats_reachable(a).states - 1;
    int min_states = 1;

    tgba_explicit_number* prev = 0;
    while (min_states <= max_states)
      {
	int target = (max_states + min_states) / 2;
	tgba_explicit_number* next =
	  dtba_sat_synthetize(prev ? prev : a, target, state_based);
	if (next == 0)
	  {
	    min_states = target + 1;
	  }
	else
	  {
	    delete prev;
	    prev = next;
	    max_states = target - 1;
	  }
      }
    return prev;
  }
}
