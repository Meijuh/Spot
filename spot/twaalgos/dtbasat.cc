// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et
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

#include <iostream>
#include <fstream>
#include <sstream>
#include <spot/twaalgos/dtbasat.hh>
#include <spot/twaalgos/reachiter.hh>
#include <map>
#include <utility>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/stats.hh>
#include <spot/misc/satsolver.hh>
#include <spot/misc/timer.hh>
#include <spot/twaalgos/dot.hh>

// If you set the SPOT_TMPKEEP environment variable the temporary
// file used to communicate with the sat solver will be left in
// the current directory.
//
// Additionally, if the following DEBUG macro is set to 1, the CNF
// file will be output with a comment before each clause, and an
// additional output file (dtba-sat.dbg) will be created with a list
// of all positive variables in the result and their meaning.

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
    static bdd_dict_ptr debug_dict;

    struct transition
    {
      unsigned src;
      bdd cond;
      unsigned dst;

      transition(unsigned src, bdd cond, unsigned dst)
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
      unsigned src;
      bdd cond;

      src_cond(unsigned src, bdd cond)
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
      unsigned a;
      unsigned b;

      state_pair(unsigned a, unsigned b)
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
      os << '<' << p.a << ',' << p.b << '>';
      return os;
    }

    std::ostream& operator<<(std::ostream& os, const transition& t)
    {
      os << '<' << t.src << ','
	 << bdd_format_formula(debug_dict, t.cond)
	 << ',' << t.dst << '>';
      return os;
    }

    std::ostream& operator<<(std::ostream& os, const path& p)
    {
      os << '<'
	 << p.src_cand << ','
	 << p.src_ref << ','
	 << p.dst_cand << ','
	 << p.dst_ref << '>';
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
      int nvars = 0;
      unsigned cand_size;
    };

    unsigned declare_vars(const const_twa_graph_ptr& aut,
			  dict& d,
			  bdd ap,
			  bool state_based,
			  scc_info& sm)
    {
      unsigned ref_size = aut->num_states();

      if (d.cand_size == -1U)
	for (unsigned i = 0; i < ref_size; ++i)
	  if (sm.reachable_state(i))
	    ++d.cand_size;	// Note that we start from -1U the
				// cand_size is one less than the
				// number of reachable states.

      for (unsigned i = 0; i < ref_size; ++i)
	{
	  if (!sm.reachable_state(i))
	    continue;

	  unsigned i_scc = sm.scc_of(i);
	  bool is_trivial = sm.is_trivial(i_scc);

	  for (unsigned j = 0; j < d.cand_size; ++j)
	    {
	      d.prodid[state_pair(j, i)] = ++d.nvars;

	      // skip trivial SCCs
	      if (is_trivial)
		continue;

	      for (unsigned k = 0; k < ref_size; ++k)
		{
		  if (!sm.reachable_state(k))
		    continue;
		  if (sm.scc_of(k) != i_scc)
		    continue;
		  for (unsigned l = 0; l < d.cand_size; ++l)
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

	for (unsigned i = 0; i < d.cand_size; ++i)
	  {
	    int transacc = -1;
	    if (state_based)
	      // All outgoing transitions use the same acceptance variable.
	      transacc = ++d.nvars;

	    for (unsigned j = 0; j < d.cand_size; ++j)
	      {
		bdd all = bddtrue;
		while (all != bddfalse)
		  {
		    bdd one = bdd_satoneset(all, ap, bddfalse);
		    all -= one;

		    transition t(i, one, j);
		    d.transid[t] = ++d.nvars;
		    d.revtransid.emplace(d.nvars, t);
		    int ta = d.transacc[t] =
		      state_based ? transacc : ++d.nvars;
		    d.revtransacc.emplace(ta, t);
		  }
	      }
	  }

	return ref_size;
    }

    typedef std::pair<int, int> sat_stats;

    static
    sat_stats dtba_to_sat(std::ostream& out,
			  const const_twa_graph_ptr& ref,
			  dict& d, bool state_based)
    {
      clause_counter nclauses;

      // Compute the AP used in the hard way.
      bdd ap = bddtrue;
      for (auto& t: ref->edges())
	ap &= bdd_support(t.cond);

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

      scc_info sm(ref);

      // Number all the SAT variables we may need.
      unsigned ref_size = declare_vars(ref, d, ap, state_based, sm);

      // empty automaton is impossible
      if (d.cand_size == 0)
	{
	  out << "p cnf 1 2\n-1 0\n1 0\n";
	  return std::make_pair(1, 2);
	}

      // An empty line for the header
      out << "                                                 \n";

#if DEBUG
      debug_dict = ref->get_dict();
      dout << "ref_size: " << ref_size << '\n';
      dout << "cand_size: " << d.cand_size << '\n';
#endif

      dout << "symmetry-breaking clauses\n";
      unsigned j = 0;
      bdd all = bddtrue;
      while (all != bddfalse)
 	{
 	  bdd s = bdd_satoneset(all, ap, bddfalse);
 	  all -= s;
	  for (unsigned i = 0; i < d.cand_size - 1; ++i)
	    for (unsigned k = i * nap + j + 2; k < d.cand_size; ++k)
	      {
		transition t(i, s, k);
		int ti = d.transid[t];
		dout << "¬" << t << '\n';
		out << -ti << " 0\n";
		++nclauses;
	      }
 	  ++j;
 	}
      if (!nclauses.nb_clauses())
 	dout << "(none)\n";

      dout << "(1) the candidate automaton is complete\n";
      for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
	{
	  bdd all = bddtrue;
	  while (all != bddfalse)
	    {
	      bdd s = bdd_satoneset(all, ap, bddfalse);
	      all -= s;

#if DEBUG
	      dout;
	      for (unsigned q2 = 0; q2 < d.cand_size; q2++)
		{
		  transition t(q1, s, q2);
		  out << t << "δ";
		  if (q2 != d.cand_size)
		    out << " ∨ ";
		}
	      out << '\n';
#endif

	      for (unsigned q2 = 0; q2 < d.cand_size; q2++)
		{
		  transition t(q1, s, q2);
		  int ti = d.transid[t];

		  out << ti << ' ';
		}
	      out << "0\n";

	      ++nclauses;
	    }
	}

      dout << "(2) the initial state is reachable\n";
      {
	unsigned init = ref->get_init_state_number();
	dout << state_pair(0, init) << '\n';
	out << d.prodid[state_pair(0, init)] << " 0\n";
	++nclauses;
      }

      for (std::map<state_pair, int>::const_iterator pit = d.prodid.begin();
	   pit != d.prodid.end(); ++pit)
	{
	  unsigned q1 = pit->first.a;
	  unsigned q1p = pit->first.b;

	  dout << "(3) augmenting paths based on Cand[" << q1
	       << "] and Ref[" << q1p << "]\n";
	  for (auto& tr: ref->out(q1p))
	    {
	      unsigned dp = tr.dst;
	      bdd all = tr.cond;
	      while (all != bddfalse)
		{
		  bdd s = bdd_satoneset(all, ap, bddfalse);
		  all -= s;

		  for (unsigned q2 = 0; q2 < d.cand_size; q2++)
		    {
		      transition t(q1, s, q2);
		      int ti = d.transid[t];

		      state_pair p2(q2, dp);
		      int succ = d.prodid[p2];

		      if (pit->second == succ)
			continue;

		      dout << pit->first << " ∧ " << t << "δ → " << p2 << '\n';
		      out << -pit->second << ' ' << -ti << ' '
			  << succ << " 0\n";
		      ++nclauses;
		    }
		}
	    }
	}

      const acc_cond& ra = ref->acc();

      // construction of contraints (4,5) : all loops in the product
      // where no accepting run is detected in the ref. automaton,
      // must also be marked as not accepting in the cand. automaton
      for (unsigned q1p = 0; q1p < ref_size; ++q1p)
	{
	  if (!sm.reachable_state(q1p))
	    continue;
	  unsigned q1p_scc = sm.scc_of(q1p);
	  if (sm.is_trivial(q1p_scc))
	    continue;
	  for (unsigned q2p = 0; q2p < ref_size; ++q2p)
	    {
	      if (!sm.reachable_state(q2p))
		continue;
	      // We are only interested in transition that can form a
	      // cycle, so they must belong to the same SCC.
	      if (sm.scc_of(q2p) != q1p_scc)
		continue;
	      for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
		for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
		  {
		    path p1(q1, q1p, q2, q2p);

		    dout << "(4&5) matching paths from reference based on "
			 << p1 << '\n';

		    int pid1;
		    if (q1 == q2 && q1p == q2p)
		      pid1 = d.prodid[state_pair(q1, q1p)];
		    else
		      pid1 = d.pathid_ref[p1];

		    for (auto& tr: ref->out(q2p))
		      {
			unsigned dp = tr.dst;
			// Skip destinations not in the SCC.
			if (sm.scc_of(dp) != q1p_scc)
			  continue;

			if (ra.accepting(tr.acc))
			  continue;
			for (unsigned q3 = 0; q3 < d.cand_size; ++q3)
			  {
			    if (dp == q1p && q3 == q1) // (4) looping
			      {
				bdd all = tr.cond;
				while (all != bddfalse)
				  {
				    bdd s = bdd_satoneset(all, ap, bddfalse);
				    all -= s;

				    transition t(q2, s, q1);
				    int ti = d.transid[t];
				    int ta = d.transacc[t];

				    dout << p1 << "R ∧ " << t << "δ → ¬" << t
					 << "F\n";
				    out << -pid1 << ' ' << -ti << ' '
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

				bdd all = tr.cond;
				while (all != bddfalse)
				  {
				    bdd s = bdd_satoneset(all, ap, bddfalse);
				    all -= s;

				    transition t(q2, s, q3);
				    int ti = d.transid[t];

				    dout << p1 << "R ∧ " << t << "δ → " << p2
					 << "R\n";
				    out << -pid1 << ' ' << -ti << ' '
					<< pid2 << " 0\n";
				    ++nclauses;
				  }
			      }
			  }
		      }
		  }
	    }
	}
      // construction of contraints (6,7): all loops in the product
      // where accepting run is detected in the ref. automaton, must
      // also be marked as accepting in the candidate.
      for (unsigned q1p = 0; q1p < ref_size; ++q1p)
	{
	  if (!sm.reachable_state(q1p))
	    continue;
	  unsigned q1p_scc = sm.scc_of(q1p);
	  if (sm.is_trivial(q1p_scc))
	    continue;
	  for (unsigned q2p = 0; q2p < ref_size; ++q2p)
	    {
	      if (!sm.reachable_state(q2p))
		continue;
	      // We are only interested in transition that can form a
	      // cycle, so they must belong to the same SCC.
	      if (sm.scc_of(q2p) != q1p_scc)
		continue;
	      for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
		for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
		  {
		    path p1(q1, q1p, q2, q2p);
		    dout << "(6&7) matching paths from candidate based on "
			 << p1 << '\n';

		    int pid1;
		    if (q1 == q2 && q1p == q2p)
		      pid1 = d.prodid[state_pair(q1, q1p)];
		    else
		      pid1 = d.pathid_cand[p1];

		    for (auto& tr: ref->out(q2p))
		      {
			unsigned dp = tr.dst;
			// Skip destinations not in the SCC.
			if (sm.scc_of(dp) != q1p_scc)
			  continue;
			for (unsigned q3 = 0; q3 < d.cand_size; q3++)
			  {
			    if (dp == q1p && q3 == q1) // (6) looping
			      {
				// We only care about the looping case if
				// it is accepting in the reference.
				if (!ra.accepting(tr.acc))
				  continue;
				bdd all = tr.cond;
				while (all != bddfalse)
				  {
				    bdd s = bdd_satoneset(all, ap, bddfalse);
				    all -= s;

				    transition t(q2, s, q1);
				    int ti = d.transid[t];
				    int ta = d.transacc[t];

				    dout << p1 << "C ∧ " << t << "δ → " << t
					 << "F\n";
				    out << -pid1 << ' ' << -ti << ' ' << ta
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

				bdd all = tr.cond;
				while (all != bddfalse)
				  {
				    bdd s = bdd_satoneset(all, ap, bddfalse);
				    all -= s;

				    transition t(q2, s, q3);
				    int ti = d.transid[t];
				    int ta = d.transacc[t];

				    dout << p1 << "C ∧ " << t << "δ ∧ ¬"
					 << t << "F → " << p2 << "C\n";

				    out << -pid1 << ' ' << -ti << ' '
					<< ta << ' ' << pid2 << " 0\n";
				    ++nclauses;
				  }
			      }
			  }
		      }
		  }
	    }
	}
      out.seekp(0);
      out << "p cnf " << d.nvars << ' ' << nclauses.nb_clauses();
      return std::make_pair(d.nvars, nclauses.nb_clauses());
    }

    static twa_graph_ptr
    sat_build(const satsolver::solution& solution, dict& satdict,
	      const_twa_graph_ptr aut, bool state_based)
    {
      auto autdict = aut->get_dict();
      auto a = make_twa_graph(autdict);
      a->copy_ap_of(aut);
      acc_cond::mark_t acc = a->set_buchi();
      if (state_based)
	a->prop_state_acc(true);
      a->prop_deterministic(true);
      a->new_states(satdict.cand_size);

      unsigned last_aut_trans = -1U;
      const transition* last_sat_trans = nullptr;

#if DEBUG
      std::fstream out("dtba-sat.dbg",
		       std::ios_base::trunc | std::ios_base::out);
      out.exceptions(std::ifstream::failbit | std::ifstream::badbit);
      std::set<int> positive;
#endif

      dout << "--- transition variables ---\n";
      std::set<int> acc_states;
      std::set<src_cond> seen_trans;
      for (int v: solution)
	{
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
		  // Mark the transition as accepting if the source is.
		  bool accept = state_based
		    && acc_states.find(t->second.src) != acc_states.end();

		  last_aut_trans =
		    a->new_acc_edge(t->second.src, t->second.dst,
				    t->second.cond, accept);
		  last_sat_trans = &t->second;

		  dout << v << '\t' << t->second << "δ\n";
		}
	    }
	  else
	    {
	      t = satdict.revtransacc.find(v);
	      if (t != satdict.revtransacc.end())
		{
		  dout << v << '\t' << t->second << "F\n";
		  if (last_sat_trans && t->second == *last_sat_trans)
		    {
		      assert(!state_based);
		      // This assumes that the SAT solvers output
		      // variables in increasing order.
		      a->edge_data(last_aut_trans).acc = acc;
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
      for (auto pit: satdict.prodid)
	if (positive.find(pit.second) != positive.end())
	  dout << pit.second << '\t' << pit.first << "C\n";
	else
	  dout << -pit.second << "\t¬" << pit.first << "C\n";

      dout << "--- pathid_cand variables ---\n";
      for (auto pit: satdict.pathid_cand)
	if (positive.find(pit.second) != positive.end())
	  dout << pit.second << '\t' << pit.first << "C\n";
	else
	  dout << -pit.second << "\t¬" << pit.first << "C\n";

      dout << "--- pathid_ref variables ---\n";
      for (auto pit: satdict.pathid_ref)
	if (positive.find(pit.second) != positive.end())
	  dout << pit.second << '\t' << pit.first << "R\n";
	else
	  dout << -pit.second << "\t¬" << pit.first << "C\n";
#endif
      a->merge_edges();
      return a;
    }
  }

  twa_graph_ptr
  dtba_sat_synthetize(const const_twa_graph_ptr& a,
		      int target_state_number, bool state_based)
  {
    if (!a->acc().is_buchi())
      throw std::runtime_error
	("dtba_sat() can only work with Büchi acceptance");
    if (target_state_number == 0)
      return nullptr;
    trace << "dtba_sat_synthetize(..., states = " << target_state_number
	  << ", state_based = " << state_based << ")\n";
    dict d;
    d.cand_size = target_state_number;

    satsolver solver;
    satsolver::solution_pair solution;

    timer_map t;
    t.start("encode");
    sat_stats s = dtba_to_sat(solver(), a, d, state_based);
    t.stop("encode");
    t.start("solve");
    solution = solver.get_solution();
    t.stop("solve");

    twa_graph_ptr res = nullptr;
    if (!solution.second.empty())
      res = sat_build(solution.second, d, a, state_based);

    // Always copy the environment variable into a static string,
    // so that we (1) look it up once, but (2) won't crash if the
    // environment is changed.
    static std::string log = []()
      {
	auto s = getenv("SPOT_SATLOG");
	return s ? s : "";
      }();
    if (!log.empty())
      {
	std::fstream out(log,
			 std::ios_base::app | std::ios_base::out);
	out.exceptions(std::ifstream::failbit | std::ifstream::badbit);
	const timer& te = t.timer("encode");
	const timer& ts = t.timer("solve");
	out << target_state_number << ',';
	if (res)
	  {
	    twa_sub_statistics st = sub_stats_reachable(res);
	    out << st.states << ',' << st.edges << ',' << st.transitions;
	  }
	else
	  {
	    out << ",,";
	  }
	out << ','
	    << s.first << ',' << s.second << ','
	    << te.utime() << ',' << te.stime() << ','
	    << ts.utime() << ',' << ts.stime() << '\n';
      }
    static bool show = getenv("SPOT_SATSHOW");
    if (show && res)
      print_dot(std::cout, res);

    trace << "dtba_sat_synthetize(...) = " << res << '\n';
    return res;
  }

  twa_graph_ptr
  dtba_sat_minimize(const const_twa_graph_ptr& a,
		    bool state_based, int max_states)
  {
    int n_states = (max_states < 0) ?
      stats_reachable(a).states : max_states + 1;

    twa_graph_ptr prev = nullptr;
    for (;;)
      {
	auto next =
	  dtba_sat_synthetize(prev ? prev : a, --n_states, state_based);
	if (!next)
	  return prev;
	else
	  n_states = stats_reachable(next).states;
	prev = next;
      }
    SPOT_UNREACHABLE();
  }

  twa_graph_ptr
  dtba_sat_minimize_dichotomy(const const_twa_graph_ptr& a,
			      bool state_based, int max_states)
  {
    if (max_states < 0)
      max_states = stats_reachable(a).states - 1;
    int min_states = 1;

    twa_graph_ptr prev = nullptr;
    while (min_states <= max_states)
      {
	int target = (max_states + min_states) / 2;
	auto next = dtba_sat_synthetize(prev ? prev : a, target, state_based);
	if (!next)
	  {
	    min_states = target + 1;
	  }
	else
	  {
	    prev = next;
	    max_states = stats_reachable(next).states - 1;
	  }
      }
    return prev;
  }
}
