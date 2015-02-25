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
#include "dtgbasat.hh"
#include "reachiter.hh"
#include <map>
#include <utility>
#include "sccinfo.hh"
#include "tgba/bddprint.hh"
#include "ltlast/constant.hh"
#include "stats.hh"
#include "ltlenv/defaultenv.hh"
#include "misc/satsolver.hh"
#include "misc/timer.hh"
#include "isweakscc.hh"
#include "dotty.hh"

// If you set the SPOT_TMPKEEP environment variable the temporary
// file used to communicate with the sat solver will be left in
// the current directory.
//
// Additionally, if the following DEBUG macro is set to 1, the CNF
// file will be output with a comment before each clause, and an
// additional output file (dtgba-sat.dbg) will be created with a list
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
    static bdd_dict_ptr debug_dict = 0;
    static const acc_cond* debug_ref_acc = 0;
    static const acc_cond* debug_cand_acc = 0;

    struct transition
    {
      unsigned src;
      bdd cond;
      unsigned dst;

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
      unsigned src;
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

    struct transition_acc
    {
      unsigned src;
      bdd cond;
      acc_cond::mark_t acc;
      unsigned dst;

      transition_acc(int src, bdd cond, acc_cond::mark_t acc, int dst)
	: src(src), cond(cond), acc(acc), dst(dst)
      {
      }

      bool operator<(const transition_acc& other) const
      {
	if (this->src < other.src)
	  return true;
	if (this->src > other.src)
	  return false;
	if (this->dst < other.dst)
	  return true;
	if (this->dst > other.dst)
	  return false;
	if (this->cond.id() < other.cond.id())
	  return true;
	if (this->cond.id() > other.cond.id())
	  return false;
	return this->acc < other.acc;
      }

      bool operator==(const transition_acc& other) const
      {
	return (this->src == other.src
		&& this->dst == other.dst
		&& this->cond.id() == other.cond.id()
		&& this->acc == other.acc);
      }
    };

    struct path
    {
      unsigned src_cand;
      unsigned src_ref;
      unsigned dst_cand;
      unsigned dst_ref;
      acc_cond::mark_t acc_cand;
      acc_cond::mark_t acc_ref;

      path(unsigned src_cand, unsigned src_ref)
	: src_cand(src_cand), src_ref(src_ref),
	  dst_cand(src_cand), dst_ref(src_ref),
	  acc_cand(0U), acc_ref(0U)
      {
      }

      path(unsigned src_cand, unsigned src_ref,
	   unsigned dst_cand, unsigned dst_ref,
	   acc_cond::mark_t acc_cand, acc_cond::mark_t acc_ref)
	: src_cand(src_cand), src_ref(src_ref),
	  dst_cand(dst_cand), dst_ref(dst_ref),
	  acc_cand(acc_cand), acc_ref(acc_ref)
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
	if (this->acc_ref < other.acc_ref)
	  return true;
	if (this->acc_ref > other.acc_ref)
	  return false;
	if (this->acc_cand < other.acc_cand)
	  return true;
	if (this->acc_cand > other.acc_cand)
	  return false;

	return false;
      }

    };

    std::ostream& operator<<(std::ostream& os, const transition& t)
    {
      os << '<' << t.src << ','
	 << bdd_format_formula(debug_dict, t.cond)
	 << ',' << t.dst << '>';
      return os;
    }


    std::ostream& operator<<(std::ostream& os, const transition_acc& t)
    {
      os << '<' << t.src << ','
	 << bdd_format_formula(debug_dict, t.cond) << ','
	 << debug_cand_acc->format(t.acc)
	 << ',' << t.dst << '>';
      return os;
    }

    std::ostream& operator<<(std::ostream& os, const path& p)
    {
      os << '<'
	 << p.src_cand << ','
	 << p.src_ref << ','
	 << p.dst_cand << ','
	 << p.dst_ref << ", "
	 << debug_cand_acc->format(p.acc_cand) << ", "
	 << debug_ref_acc->format(p.acc_ref) << '>';
      return os;
    }

    struct dict
    {
      dict(const const_tgba_ptr& a)
	: aut(a)
      {
      }

      const_tgba_ptr aut;
      typedef std::map<transition, int> trans_map;
      typedef std::map<transition_acc, int> trans_acc_map;
      trans_map transid;
      trans_acc_map transaccid;
      typedef std::map<int, transition> rev_map;
      typedef std::map<int, transition_acc> rev_acc_map;
      rev_map revtransid;
      rev_acc_map revtransaccid;

      std::map<path, int> pathid;
      int nvars = 0;
      //typedef std::unordered_map<const state*, int,
      //state_ptr_hash, state_ptr_equal> state_map;
      //typedef std::unordered_map<int, const state*> int_map;
      //state_map state_to_int;
      //      int_map int_to_state;
      unsigned cand_size;
      unsigned int cand_nacc;
      std::vector<acc_cond::mark_t> cand_acc; // size cand_nacc

      std::vector<acc_cond::mark_t> all_cand_acc;
      std::vector<acc_cond::mark_t> all_ref_acc;

      std::vector<bool> is_weak_scc;

      acc_cond cacc;

      ~dict()
      {
	aut->get_dict()->unregister_all_my_variables(this);
      }
    };


    unsigned declare_vars(const const_tgba_digraph_ptr& aut,
			  dict& d, bdd ap, bool state_based, scc_info& sm)
    {
      bdd_dict_ptr bd = aut->get_dict();
      d.cand_acc.resize(d.cand_nacc);
      d.cacc.add_sets(d.cand_nacc);
      d.all_cand_acc.push_back(0U);
      for (unsigned n = 0; n < d.cand_nacc; ++n)
	{
	  auto c = d.cacc.mark(n);
	  d.cand_acc[n] = c;
	  size_t s = d.all_cand_acc.size();
	  for (size_t i = 0; i < s; ++i)
	    d.all_cand_acc.push_back(d.all_cand_acc[i] | c);
	}


      d.all_ref_acc.push_back(0U);
      unsigned ref_nacc = aut->acc().num_sets();
      for (unsigned n = 0; n < ref_nacc; ++n)
	{
	  auto c = aut->acc().mark(n);
	  size_t s = d.all_ref_acc.size();
	  for (size_t i = 0; i < s; ++i)
	    d.all_ref_acc.push_back(d.all_ref_acc[i] | c);
	}

      unsigned ref_size = aut->num_states();

      if (d.cand_size == -1U)
	for (unsigned i = 0; i < ref_size; ++i)
	  if (sm.reachable_state(i))
	    ++d.cand_size;      // Note that we start from -1U the
				// cand_size is one less than the
				// number of reachable states.

      for (unsigned i = 0; i < ref_size; ++i)
	{
	  if (!sm.reachable_state(i))
	    continue;
	  unsigned i_scc = sm.scc_of(i);
	  bool is_weak = d.is_weak_scc[i_scc];

	  for (unsigned j = 0; j < d.cand_size; ++j)
	    {
	      for (unsigned k = 0; k < ref_size; ++k)
		{
		  if (!sm.reachable_state(k))
		    continue;
		  if (sm.scc_of(k) != i_scc)
		    continue;
		  for (unsigned l = 0; l < d.cand_size; ++l)
		    {
		      size_t sfp = is_weak ? 1 : d.all_ref_acc.size();
		      for (size_t fp = 0; fp < sfp; ++fp)
			{
			  size_t sf = d.all_cand_acc.size();
			  for (size_t f = 0; f < sf; ++f)
			    {
			      path p(j, i, l, k,
				     d.all_cand_acc[f],
				     d.all_ref_acc[fp]);
			      d.pathid[p] = ++d.nvars;
			    }

			}
		    }
		}
	    }
	}

      if (!state_based)
	{
	  for (unsigned i = 0; i < d.cand_size; ++i)
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

		    // Create the variable for the accepting transition
		    // immediately afterwards.  It helps parsing the
		    // result.
		    for (unsigned n = 0; n < d.cand_nacc; ++n)
		      {
			transition_acc ta(i, one, d.cand_acc[n], j);
			d.transaccid[ta] = ++d.nvars;
			d.revtransaccid.emplace(d.nvars, ta);
		      }
		  }
	      }
	}
      else // state based
	{
	  for (unsigned i = 0; i < d.cand_size; ++i)
	    for (unsigned n = 0; n < d.cand_nacc; ++n)
	      {
		++d.nvars;
		for (unsigned j = 1; j < d.cand_size; ++j)
		  {
		    bdd all = bddtrue;
		    while (all != bddfalse)
		      {
			bdd one = bdd_satoneset(all, ap, bddfalse);
			all -= one;

			transition_acc ta(i, one, d.cand_acc[n], j);
			d.transaccid[ta] = d.nvars;
			d.revtransaccid.emplace(d.nvars, ta);
		      }
		  }
	      }
	  for (unsigned i = 0; i < d.cand_size; ++i)
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
		  }
	      }
	}
      return ref_size;
    }

    typedef std::pair<int, int> sat_stats;

    static
    sat_stats dtgba_to_sat(std::ostream& out, const_tgba_digraph_ptr ref,
			   dict& d, bool state_based)
    {
      clause_counter nclauses;

      // Compute the AP used in the hard way.
      bdd ap = bddtrue;
      for (auto& t: ref->transitions())
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
      d.is_weak_scc = sm.weak_sccs();

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
      debug_ref_acc = &ref->acc();
      debug_cand_acc = &d.cacc;
      dout << "ref_size: " << ref_size << '\n';
      dout << "cand_size: " << d.cand_size << '\n';
#endif
      auto& racc = ref->acc();

      dout << "symmetry-breaking clauses\n";
      int j = 0;
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

      dout << "(8) the candidate automaton is complete\n";
      for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
	{
	  bdd all = bddtrue;
	  while (all != bddfalse)
	    {
	      bdd s = bdd_satoneset(all, ap, bddfalse);
	      all -= s;

#if DEBUG
	      dout;
	      for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
		{
		  transition t(q1, s, q2);
		  out << t << "δ";
		  if (q2 != d.cand_size)
		    out << " ∨ ";
		}
	      out << '\n';
#endif

	      for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
		{
		  transition t(q1, s, q2);
		  int ti = d.transid[t];

		  out << ti << ' ';
		}
	      out << "0\n";
	      ++nclauses;
	    }
	}

      dout << "(9) the initial state is reachable\n";
      {
	unsigned init = ref->get_init_state_number();
	dout << path(0, init) << '\n';
	out << d.pathid[path(0, init)] << " 0\n";
	++nclauses;
      }

      for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
	for (unsigned q1p = 0; q1p < ref_size; ++q1p)
	  {
	    if (!sm.reachable_state(q1p))
	      continue;
	    dout << "(10) augmenting paths based on Cand[" << q1
		 << "] and Ref[" << q1p << "]\n";
	    path p1(q1, q1p);
	    int p1id = d.pathid[p1];

	    for (auto& tr: ref->out(q1p))
	      {
		unsigned dp = tr.dst;
		bdd all = tr.cond;
		while (all != bddfalse)
		  {
		    bdd s = bdd_satoneset(all, ap, bddfalse);
		    all -= s;

		    for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
		      {
			transition t(q1, s, q2);
			int ti = d.transid[t];

			path p2(q2, dp);
			int succ = d.pathid[p2];

			if (p1id == succ)
			  continue;

			dout << p1 << " ∧ " << t << "δ → " << p2 << '\n';
			out << -p1id << ' ' << -ti << ' ' << succ << " 0\n";
			++nclauses;
		      }
		  }
	      }
	  }

      // construction of constraints (11,12,13)
      for (unsigned q1p = 0; q1p < ref_size; ++q1p)
	{
	  if (!sm.reachable_state(q1p))
	    continue;
	  unsigned q1p_scc = sm.scc_of(q1p);
	  for (unsigned q2p = 0; q2p < ref_size; ++q2p)
	    {
	      if (!sm.reachable_state(q2p))
		continue;
	      // We are only interested in transition that can form a
	      // cycle, so they must belong to the same SCC.
	      if (sm.scc_of(q2p) != q1p_scc)
		continue;
	      bool is_weak = d.is_weak_scc[q1p_scc];
	      bool is_acc = sm.is_accepting_scc(q1p_scc);

	      for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
		for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
		  {
		    size_t sf = d.all_cand_acc.size();
		    size_t sfp = is_weak ? 1 : d.all_ref_acc.size();
		    for (size_t f = 0; f < sf; ++f)
		      for (size_t fp = 0; fp < sfp; ++fp)
			{
			  path p(q1, q1p, q2, q2p,
				 d.all_cand_acc[f], d.all_ref_acc[fp]);

			  dout << "(11&12&13) paths from " << p << '\n';

			  int pid = d.pathid[p];

			  for (auto& tr: ref->out(q2p))
			    {
			      unsigned dp = tr.dst;
			      // Skip destinations not in the SCC.
			      if (sm.scc_of(dp) != q1p_scc)
				continue;

			      for (unsigned q3 = 0; q3 < d.cand_size; ++q3)
				{
				  bdd all = tr.cond;
				  acc_cond::mark_t curacc = tr.acc;
				  while (all != bddfalse)
				    {
				      bdd l = bdd_satoneset(all, ap, bddfalse);
				      all -= l;

				      transition t(q2, l, q3);
				      int ti = d.transid[t];

				      if (dp == q1p && q3 == q1) // (11,12) loop
					{
					  if ((!is_acc) ||
					      (!is_weak &&
					       !racc.accepting
					       (curacc | d.all_ref_acc[fp])))
					    {
#if DEBUG
					      dout << "(11) " << p << " ∧ "
						   << t << "δ → ¬(";

					      bool notfirst = false;
					      acc_cond::mark_t all_ =
						d.all_cand_acc.back() -
						d.all_cand_acc[f];
					      for (auto m: d.cacc.sets(all_))
						{
						  transition_acc
						    ta(q2, l,
						       d.cacc.mark(m), q1);
						  if (notfirst)
						    out << " ∧ ";
						  else
						    notfirst = true;
						  out << ta << "FC";
						}
					      out << ")\n";
#endif // DEBUG
					      out << -pid << ' ' << -ti;

					      // 11
					      acc_cond::mark_t all_f =
						d.all_cand_acc.back() -
						d.all_cand_acc[f];
					      for (auto m: d.cacc.sets(all_f))
						{
						  transition_acc
						    ta(q2, l,
						       d.cacc.mark(m), q1);
						  int tai = d.transaccid[ta];
						  assert(tai != 0);
						  out << ' ' << -tai;
						}
					      out << " 0\n";
					      ++nclauses;
					    }
					  else
					    {
#if DEBUG
					      dout << "(12) " << p << " ∧ "
						   << t << "δ → (";
					      bool notfirst = false;
					      // 11
					      acc_cond::mark_t all_ =
						d.cacc.comp(d.all_cand_acc[f]);
					      for (auto m: d.cacc.sets(all_))
						{
						  transition_acc
						    ta(q2, l,
						       d.cacc.mark(m), q1);
						  if (notfirst)
						    out << " ∧ ";
						  else
						    notfirst = true;
						  out << ta << "FC";
						}
					      out << ")\n";
#endif // DEBUG
					      // 12
					      acc_cond::mark_t all_f =
						d.cacc.comp(d.all_cand_acc[f]);
					      for (auto m: d.cacc.sets(all_f))
						{
						  transition_acc
						    ta(q2, l,
						       d.cacc.mark(m), q1);
						  int tai = d.transaccid[ta];
						  assert(tai != 0);

						  out << -pid << ' ' << -ti
						      << ' ' << tai << " 0\n";
						  ++nclauses;
						}
					    }
					}
				      // (13) augmenting paths (always).
				      {
					size_t sf = d.all_cand_acc.size();
					for (size_t f = 0; f < sf; ++f)
					  {
					    acc_cond::mark_t f2 =
					      p.acc_cand | d.all_cand_acc[f];
					    acc_cond::mark_t f2p = 0U;
					    if (!is_weak)
					      f2p = p.acc_ref | curacc;

					    path p2(p.src_cand, p.src_ref,
						    q3, dp, f2, f2p);
					    int p2id = d.pathid[p2];
					    if (pid == p2id)
					      continue;
#if DEBUG
					    dout << "(13) " << p << " ∧ "
						 << t << "δ ";

					    auto biga_ = d.all_cand_acc[f];
					    for (unsigned m = 0;
						 m < d.cand_nacc; ++m)
					      {
						transition_acc
						  ta(q2, l,
						     d.cacc.mark(m), q3);
						const char* not_ = "¬";
						if (d.cacc.has(biga_, m))
						  not_ = "";
						out <<  " ∧ " << not_
						    << ta << "FC";
					      }
					    out << " → " << p2 << '\n';
#endif
					    out << -pid << ' ' << -ti << ' ';
					    auto biga = d.all_cand_acc[f];
					    for (unsigned m = 0;
						 m < d.cand_nacc; ++m)
					      {
						transition_acc
						  ta(q2, l,
						     d.cacc.mark(m), q3);
						int tai = d.transaccid[ta];
						if (d.cacc.has(biga, m))
						  tai = -tai;
						out << tai << ' ';
					      }

					    out << p2id << " 0\n";
					    ++nclauses;
					  }
				      }
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

    static tgba_digraph_ptr
    sat_build(const satsolver::solution& solution, dict& satdict,
	      const_tgba_digraph_ptr aut, bool state_based)
    {
      auto autdict = aut->get_dict();
      auto a = make_tgba_digraph(autdict);
      a->copy_ap_of(aut);
      a->set_generalized_buchi(satdict.cand_nacc);

      a->new_states(satdict.cand_size);

      // Last transition set in the automaton.
      unsigned last_aut_trans = -1U;
      // Last transition read from the SAT result.
      const transition* last_sat_trans = nullptr;

#if DEBUG
      std::fstream out("dtgba-sat.dbg",
		       std::ios_base::trunc | std::ios_base::out);
      out.exceptions(std::ifstream::failbit | std::ifstream::badbit);
      std::set<int> positive;
#endif

      dout << "--- transition variables ---\n";
      std::map<int, acc_cond::mark_t> state_acc;
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
		  acc_cond::mark_t acc = 0U;
		  if (state_based)
		    {
		      auto i = state_acc.find(t->second.src);
		      if (i != state_acc.end())
			acc = i->second;
		    }

		  last_aut_trans = a->new_transition(t->second.src,
						     t->second.dst,
						     t->second.cond,
						     acc);
		  last_sat_trans = &t->second;

		  dout << v << '\t' << t->second << "δ\n";
		}
	    }
	  else
	    {
	      dict::rev_acc_map::const_iterator ta;
	      ta = satdict.revtransaccid.find(v);
	      // This assumes that the sat solvers output variables in
	      // increasing order.
	      if (ta != satdict.revtransaccid.end())
		{
		  dout << v << '\t' << ta->second << "F\n";

		  if (last_sat_trans &&
		      ta->second.src == last_sat_trans->src &&
		      ta->second.cond == last_sat_trans->cond &&
		      ta->second.dst == last_sat_trans->dst)
		    {
		      assert(!state_based);
		      auto& v = a->trans_data(last_aut_trans).acc;
		      v |= ta->second.acc;
		    }
		  else if (state_based)
		    {
		      auto& v = state_acc[ta->second.src];
		      v |= ta->second.acc;
		    }
		}
	    }
	}
#if DEBUG
      dout << "--- pathid variables ---\n";
      for (auto pit: satdict.pathid)
	if (positive.find(pit.second) != positive.end())
	  dout << pit.second << '\t' << pit.first << "C\n";
#endif

      a->merge_transitions();

      return a;
    }
  }

  tgba_digraph_ptr
  dtgba_sat_synthetize(const const_tgba_digraph_ptr& a,
		       unsigned target_acc_number,
		       int target_state_number, bool state_based)
  {
    if (!a->acc().is_generalized_buchi())
      throw std::runtime_error
	("dtgba_sat() can only work with generalized Büchi acceptance");
    if (target_state_number == 0)
      return nullptr;
    trace << "dtgba_sat_synthetize(..., acc = " << target_acc_number
	  << ", states = " << target_state_number
	  << ", state_based = " << state_based << ")\n";

    dict d(a);
    d.cand_size = target_state_number;
    d.cand_nacc = target_acc_number;

    satsolver solver;
    satsolver::solution_pair solution;

    timer_map t;
    t.start("encode");
    sat_stats s = dtgba_to_sat(solver(), a, d, state_based);
    t.stop("encode");
    t.start("solve");
    solution = solver.get_solution();
    t.stop("solve");

    tgba_digraph_ptr res = nullptr;
    if (!solution.second.empty())
      res = sat_build(solution.second, d, a, state_based);

    static const char* log = getenv("SPOT_SATLOG");
    if (log)
      {
	std::fstream out(log,
			 std::ios_base::app | std::ios_base::out);
	out.exceptions(std::ifstream::failbit | std::ifstream::badbit);
	const timer& te = t.timer("encode");
	const timer& ts = t.timer("solve");
	out << target_state_number << ',';
	if (res)
	  {
	    tgba_sub_statistics st = sub_stats_reachable(res);
	    out << st.states << ',' << st.transitions
		<< ',' << st.sub_transitions;
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
    static const char* show = getenv("SPOT_SATSHOW");
    if (show && res)
      dotty_reachable(std::cout, res);

    trace << "dtgba_sat_synthetize(...) = " << res << '\n';
    return res;
  }

  tgba_digraph_ptr
  dtgba_sat_minimize(const const_tgba_digraph_ptr& a,
		     unsigned target_acc_number,
		     bool state_based)
  {
    int n_states = stats_reachable(a).states;

    tgba_digraph_ptr prev = nullptr;
    for (;;)
      {
	auto next =
	  dtgba_sat_synthetize(prev ? prev : a, target_acc_number,
			       --n_states, state_based);
	if (!next)
	  return prev;
	else
	  n_states = stats_reachable(next).states;
	prev = next;
      }
    SPOT_UNREACHABLE();
  }

  tgba_digraph_ptr
  dtgba_sat_minimize_dichotomy(const const_tgba_digraph_ptr& a,
			       unsigned target_acc_number,
			       bool state_based)
  {
    int max_states = stats_reachable(a).states - 1;
    int min_states = 1;

    tgba_digraph_ptr prev = nullptr;
    while (min_states <= max_states)
      {
	int target = (max_states + min_states) / 2;
	auto next =
	  dtgba_sat_synthetize(prev ? prev : a, target_acc_number, target,
			       state_based);
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
