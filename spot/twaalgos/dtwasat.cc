// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015, 2016 Laboratoire de Recherche et
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
#include <spot/twaalgos/dtwasat.hh>
#include <spot/twaalgos/dtbasat.hh>
#include <map>
#include <utility>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/stats.hh>
#include <spot/tl/defaultenv.hh>
#include <spot/misc/satsolver.hh>
#include <spot/misc/timer.hh>
#include <spot/twaalgos/isweakscc.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/dot.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/misc/optionmap.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/postproc.hh>

// If you set the SPOT_TMPKEEP environment variable the temporary
// file used to communicate with the sat solver will be left in
// the current directory.
//
// Additionally, if the following DEBUG macro is set to 1, the CNF
// file will be output with a comment before each clause, and an
// additional output file (dtwa-sat.dbg) will be created with a list
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
    static bdd_dict_ptr debug_dict = nullptr;
    static const acc_cond* debug_ref_acc = nullptr;
    static const acc_cond* debug_cand_acc = nullptr;

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

    // If the DNF is
    //  Fin(1)&Fin(2)&Inf(3) | Fin(0)&Inf(3) | Fin(4)&Inf(5)&Inf(6)
    // this returns the following map:
    //  {3} => [{1,2} {0}]
    //  {5} => [{4}]
    //  {6} => [{4}]
    // We use that do detect (and disallow) what we call "silly histories",
    // i.e., transitions or histories labeled by sets such as
    // {3,1,0}, that have no way to be satisfied.  So whenever we see
    // such history in a path, we actually map it to {1,0} instead,
    // which is enough to remember that this history is not satisfiable.
    // We also forbid any transition from being labeled by {3,1,0}.
    typedef std::map<unsigned, std::vector<acc_cond::mark_t>> trimming_map;
    static trimming_map
    split_dnf_acc_by_inf(const acc_cond::acc_code& input_acc)
    {
      trimming_map res;
      auto acc = input_acc.to_dnf();
      auto pos = &acc.back();
      if (pos->op == acc_cond::acc_op::Or)
        --pos;
      acc_cond::mark_t all_fin = 0U;
      auto start = &acc.front();
      while (pos > start)
        {
          if (pos->op == acc_cond::acc_op::Fin)
            {
              // We have only a Fin term, without Inf.
              // There is nothing to do about it.
              pos -= pos->size + 1;
            }
          else
            {
              // We have a conjunction of Fin and Inf sets.
              auto end = pos - pos->size - 1;
              acc_cond::mark_t fin = 0U;
              acc_cond::mark_t inf = 0U;
              while (pos > end)
                {
                  switch (pos->op)
                    {
                    case acc_cond::acc_op::And:
                      --pos;
                      break;
                    case acc_cond::acc_op::Fin:
                      fin |= pos[-1].mark;
                      assert(pos[-1].mark.count() == 1);
                      pos -= 2;
                      break;
                    case acc_cond::acc_op::Inf:
                      inf |= pos[-1].mark;
                      pos -= 2;
                      break;
                    case acc_cond::acc_op::FinNeg:
                    case acc_cond::acc_op::InfNeg:
                    case acc_cond::acc_op::Or:
                      SPOT_UNREACHABLE();
                      break;
                    }
                }
              assert(pos == end);

              all_fin |= fin;
              for (unsigned i: inf.sets())
                if (fin)
                  {
                    res[i].emplace_back(fin);
                  }
                else
                  {
                    // Make sure the empty set is always the first one.
                    res[i].clear();
                    res[i].emplace_back(fin);
                  }
            }
        }
      // Remove entries that are necessarily false because they
      // contain an emptyset, or entries that also appear as Fin
      // somewhere in the acceptance.
      auto i = res.begin();
      while (i != res.end())
        {
          if (all_fin.has(i->first) || !i->second[0])
            i = res.erase(i);
          else
            ++i;
        }

      return res;
    }

    struct dict
    {
      dict(const const_twa_ptr& a)
        : aut(a)
      {
      }

      const_twa_ptr aut;
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
      unsigned cand_size;
      unsigned int cand_nacc;
      acc_cond::acc_code cand_acc;

      std::vector<acc_cond::mark_t> all_cand_acc;
      std::vector<acc_cond::mark_t> all_ref_acc;
      // Markings that make no sense and that we do not want to see in
      // the candidate.  See comment above split_dnf_acc_by_inf().
      std::vector<acc_cond::mark_t> all_silly_cand_acc;

      std::vector<bool> is_weak_scc;
      std::vector<acc_cond::mark_t> scc_marks;

      acc_cond cacc;
      trimming_map ref_inf_trim_map;
      trimming_map cand_inf_trim_map;

      ~dict()
      {
        aut->get_dict()->unregister_all_my_variables(this);
      }

      acc_cond::mark_t
      inf_trim(acc_cond::mark_t m, trimming_map& tm)
      {
        for (auto& s: tm)
          {
            unsigned inf = s.first;
            if (m.has(inf))
              {
                bool remove = true;
                for (auto fin: s.second)
                  if (!(m & fin))
                    {
                      remove = false;
                      break;
                    }
                if (remove)
                  m.clear(inf);
              }
          }
        return m;
      }

      acc_cond::mark_t
      ref_inf_trim(acc_cond::mark_t m)
      {
        return inf_trim(m, ref_inf_trim_map);
      }

      acc_cond::mark_t
      cand_inf_trim(acc_cond::mark_t m)
      {
        return inf_trim(m, cand_inf_trim_map);
      }
    };


    unsigned declare_vars(const const_twa_graph_ptr& aut,
                          dict& d, bdd ap, bool state_based, scc_info& sm)
    {
      d.is_weak_scc = sm.weak_sccs();
      unsigned scccount = sm.scc_count();
      {
        auto tmp = sm.used_acc();
        d.scc_marks.reserve(scccount);
        for (auto& v: tmp)
          {
            acc_cond::mark_t m = 0U;
            for (auto i: v)
              m |= i;
            d.scc_marks.emplace_back(m);
          }
      }

      d.cacc.add_sets(d.cand_nacc);
      d.cacc.set_acceptance(d.cand_acc);

      // If the acceptance conditions use both Fin and Inf primitives,
      // we may have some silly history configurations to ignore.
      if (aut->acc().uses_fin_acceptance())
        d.ref_inf_trim_map = split_dnf_acc_by_inf(aut->get_acceptance());
      if (d.cacc.uses_fin_acceptance())
        d.cand_inf_trim_map = split_dnf_acc_by_inf(d.cand_acc);

      bdd_dict_ptr bd = aut->get_dict();
      d.all_cand_acc.emplace_back(0U);
      for (unsigned n = 0; n < d.cand_nacc; ++n)
        {
          auto c = d.cacc.mark(n);

          size_t ss = d.all_silly_cand_acc.size();
          for (size_t i = 0; i < ss; ++i)
            d.all_silly_cand_acc.emplace_back(d.all_silly_cand_acc[i] | c);

          size_t s = d.all_cand_acc.size();
          for (size_t i = 0; i < s; ++i)
            {
              acc_cond::mark_t m = d.all_cand_acc[i] | c;
              if (d.cand_inf_trim(m) == m)
                d.all_cand_acc.emplace_back(m);
              else
                d.all_silly_cand_acc.emplace_back(m);
            }
        }

      d.all_ref_acc.emplace_back(0U);
      unsigned ref_nacc = aut->num_sets();
      for (unsigned n = 0; n < ref_nacc; ++n)
        {
          auto c = aut->acc().mark(n);
          size_t s = d.all_ref_acc.size();
          for (size_t i = 0; i < s; ++i)
            {
              acc_cond::mark_t m = d.all_ref_acc[i] | c;
              if (d.ref_inf_trim(m) != m)
                continue;
              d.all_ref_acc.emplace_back(m);
            }
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
                      acc_cond::mark_t sccmarks = d.scc_marks[i_scc];
                      for (size_t fp = 0; fp < sfp; ++fp)
                        {
                          auto refhist = d.all_ref_acc[fp];
                          // refhist cannot have more sets than used in the SCC
                          if (!is_weak && (sccmarks & refhist) != refhist)
                            continue;

                          size_t sf = d.all_cand_acc.size();
                          for (size_t f = 0; f < sf; ++f)
                            {
                              path p(j, i, l, k,
                                     d.all_cand_acc[f], refhist);
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
                        transition_acc ta(i, one, d.cacc.mark(n), j);
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
                for (unsigned j = 0; j < d.cand_size; ++j)
                  {
                    bdd all = bddtrue;
                    while (all != bddfalse)
                      {
                        bdd one = bdd_satoneset(all, ap, bddfalse);
                        all -= one;

                        transition_acc ta(i, one, d.cacc.mark(n), j);
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
    sat_stats dtwa_to_sat(std::ostream& out, const_twa_graph_ptr ref,
                           dict& d, bool state_based, bool colored)
    {
#if DEBUG
      debug_dict = ref->get_dict();
#endif
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
      sm.determine_unknown_acceptance();

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

      if (colored)
        {
          unsigned nacc = d.cand_nacc;
          dout << "transitions belong to exactly one of the "
               << nacc << " acceptance set\n";
          bdd all = bddtrue;
          while (all != bddfalse)
            {
              bdd l = bdd_satoneset(all, ap, bddfalse);
              all -= l;
              for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
                for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
                  {
                    for (unsigned i = 0; i < nacc; ++i)
                      {
                        transition_acc ti(q1, l, {i}, q2);
                        int tai = d.transaccid[ti];

                        for (unsigned j = 0; j < nacc; ++j)
                          if (i != j)
                            {
                              transition_acc tj(q1, l, {j}, q2);
                              int taj = d.transaccid[tj];
                              out << -tai << ' ' << -taj << " 0\n";
                              ++nclauses;
                            }
                      }
                    for (unsigned i = 0; i < nacc; ++i)
                      {
                        transition_acc ti(q1, l, {i}, q2);
                        int tai = d.transaccid[ti];
                        out << tai << ' ';
                      }
                    out << "0\n";
                    ++nclauses;
                  }
            }
        }

      if (!d.all_silly_cand_acc.empty())
        {
          dout << "no transition with silly acceptance\n";
          bdd all = bddtrue;
          while (all != bddfalse)
            {
              bdd l = bdd_satoneset(all, ap, bddfalse);
              all -= l;
              for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
                for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
                  for (auto& s: d.all_silly_cand_acc)
                    {
                      dout << "no (" << q1 << ','
                           << bdd_format_formula(debug_dict, l)
                           << ',' << s << ',' << q2 << ")\n";
                      for (unsigned v: s.sets())
                        {
                          transition_acc ta(q1, l, d.cacc.mark(v), q2);
                          int tai = d.transaccid[ta];
                          assert(tai != 0);
                          out << ' ' << -tai;
                        }
                      for (unsigned v: d.cacc.comp(s).sets())
                        {
                          transition_acc ta(q1, l, d.cacc.mark(v), q2);
                          int tai = d.transaccid[ta];
                          assert(tai != 0);
                          out << ' ' << tai;
                        }
                      out << " 0\n";
                      ++nclauses;
                    }
            }
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
              bool is_rej = sm.is_rejecting_scc(q1p_scc);

              for (unsigned q1 = 0; q1 < d.cand_size; ++q1)
                for (unsigned q2 = 0; q2 < d.cand_size; ++q2)
                  {
                    size_t sf = d.all_cand_acc.size();
                    size_t sfp = is_weak ? 1 : d.all_ref_acc.size();
                    acc_cond::mark_t sccmarks = d.scc_marks[q1p_scc];

                    for (size_t f = 0; f < sf; ++f)
                      for (size_t fp = 0; fp < sfp; ++fp)
                        {
                          auto refhist = d.all_ref_acc[fp];
                          // refhist cannot have more sets than used in the SCC
                          if (!is_weak && (sccmarks & refhist) != refhist)
                            continue;

                          path p(q1, q1p, q2, q2p,
                                 d.all_cand_acc[f], refhist);

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
                                          bool rejloop =
                                            (is_rej ||
                                             !racc.accepting
                                             (curacc | d.all_ref_acc[fp]));

                                          auto missing =
                                            d.cand_acc.
                                            missing(d.all_cand_acc[f],
                                                    !rejloop);

                                          for (auto& v: missing)
                                            {
#if DEBUG
                                              dout << (rejloop ?
                                                       "(11) " : "(12) ")
                                                   << p << " ∧ "
                                                   << t << "δ → (";
                                              const char* orsep = "";
                                              for (int s: v)
                                                {
                                                  if (s < 0)
                                                    {
                                                      transition_acc
                                                        ta(q2, l,
                                                           d.cacc.mark(-s - 1),
                                                           q1);
                                                      out << orsep << "¬" << ta;
                                                    }
                                                  else
                                                    {
                                                      transition_acc
                                                        ta(q2, l,
                                                           d.cacc.mark(s), q1);
                                                      out << orsep << ta;
                                                    }
                                                  out << "FC";
                                                  orsep = " ∨ ";
                                                }
                                              out << ")\n";
#endif // DEBUG
                                              out << -pid << ' ' << -ti;
                                              for (int s: v)
                                                if (s < 0)
                                                  {
                                                    transition_acc
                                                      ta(q2, l,
                                                         d.cacc.mark(-s - 1),
                                                         q1);
                                                    int tai = d.transaccid[ta];
                                                    assert(tai != 0);
                                                    out << ' ' << -tai;
                                                  }
                                                else
                                                  {
                                                    transition_acc
                                                      ta(q2, l,
                                                         d.cacc.mark(s), q1);
                                                    int tai = d.transaccid[ta];
                                                    assert(tai != 0);
                                                    out << ' ' << tai;
                                                  }
                                              out << " 0\n";
                                              ++nclauses;
                                            }
                                        }
                                      // (13) augmenting paths (always).
                                      {
                                        size_t sf = d.all_cand_acc.size();
                                        for (size_t f = 0; f < sf; ++f)
                                          {
                                            acc_cond::mark_t f2 =
                                              d.cand_inf_trim
                                              (p.acc_cand |
                                               d.all_cand_acc[f]);
                                            acc_cond::mark_t f2p = 0U;
                                            if (!is_weak)
                                              f2p = d.ref_inf_trim(p.acc_ref |
                                                                   curacc);

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
                                                if (biga_.has(m))
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
                                                if (biga.has(m))
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

    static twa_graph_ptr
    sat_build(const satsolver::solution& solution, dict& satdict,
              const_twa_graph_ptr aut, bool state_based)
    {
      auto autdict = aut->get_dict();
      auto a = make_twa_graph(autdict);
      a->copy_ap_of(aut);
      if (state_based)
        a->prop_state_acc(true);
      a->prop_deterministic(true);
      a->set_acceptance(satdict.cand_nacc, satdict.cand_acc);
      a->new_states(satdict.cand_size);

      // Last transition set in the automaton.
      unsigned last_aut_trans = -1U;
      // Last transition read from the SAT result.
      const transition* last_sat_trans = nullptr;

#if DEBUG
      std::fstream out("dtwa-sat.dbg",
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

                  last_aut_trans = a->new_edge(t->second.src,
                                               t->second.dst,
                                               t->second.cond, acc);
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
                      auto& v = a->edge_data(last_aut_trans).acc;
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

      a->merge_edges();
      return a;
    }
  }

  twa_graph_ptr
  dtwa_sat_synthetize(const const_twa_graph_ptr& a,
                      unsigned target_acc_number,
                      const acc_cond::acc_code& target_acc,
                      int target_state_number,
                      bool state_based, bool colored)
  {
    if (target_state_number == 0)
      return nullptr;
    trace << "dtwa_sat_synthetize(..., nacc = " << target_acc_number
          << ", acc = \"" << target_acc
          << "\", states = " << target_state_number
          << ", state_based = " << state_based << ")\n";

    dict d(a);
    d.cand_size = target_state_number;
    d.cand_nacc = target_acc_number;
    d.cand_acc = target_acc;

    satsolver solver;
    satsolver::solution_pair solution;

    timer_map t;
    t.start("encode");
    sat_stats s = dtwa_to_sat(solver(), a, d, state_based, colored);
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
            << te.utime() + te.cutime() << ','
            << te.stime() + te.cstime() << ','
            << ts.utime() + ts.cutime() << ','
            << ts.stime() + ts.cstime() << '\n';
      }
    static bool show = getenv("SPOT_SATSHOW");
    if (show && res)
      print_dot(std::cout, res);

    trace << "dtwa_sat_synthetize(...) = " << res << '\n';
    return res;
  }


  namespace
  {
    // Chose a good reference automaton given two automata.
    //
    // The right automaton only is allowed to be null.  In that
    // case the left automaton is returned.
    //
    // The selection relies on the fact that the SAT encoding is
    // quadratic in the number of input states, and exponential in the
    // number of input sets.
    static const_twa_graph_ptr
    best_aut(const const_twa_graph_ptr& left,
             const const_twa_graph_ptr& right)
    {
      if (right == nullptr)
        return left;
      auto lstates = left->num_states();
      auto lsets = left->num_sets();
      auto rstates = right->num_states();
      auto rsets = right->num_sets();
      if (lstates <= rstates && lsets <= rsets)
        return left;
      if (lstates >= rstates && lsets >= rsets)
        return right;

      long long unsigned lw = (1ULL << lsets) * lstates * lstates;
      long long unsigned rw = (1ULL << rsets) * rstates * rstates;

      return lw <= rw ? left : right;
    }
  }

  twa_graph_ptr
  dtwa_sat_minimize(const const_twa_graph_ptr& a,
                    unsigned target_acc_number,
                    const acc_cond::acc_code& target_acc,
                    bool state_based, int max_states,
                    bool colored)
  {
    int n_states = (max_states < 0) ?
      stats_reachable(a).states : max_states + 1;

    twa_graph_ptr prev = nullptr;
    for (;;)
      {
        auto src = best_aut(a, prev);
        auto next = dtwa_sat_synthetize(src, target_acc_number,
                                        target_acc, --n_states,
                                        state_based, colored);
        if (!next)
          return prev;
        else
          n_states = stats_reachable(next).states;
        prev = next;
      }
    SPOT_UNREACHABLE();
  }

  twa_graph_ptr
  dtwa_sat_minimize_dichotomy(const const_twa_graph_ptr& a,
                              unsigned target_acc_number,
                              const acc_cond::acc_code& target_acc,
                              bool state_based, int max_states,
                              bool colored)
  {
    if (max_states < 1)
      max_states = stats_reachable(a).states - 1;
    int min_states = 1;

    twa_graph_ptr prev = nullptr;
    while (min_states <= max_states)
      {
        int target = (max_states + min_states) / 2;
        auto src = best_aut(a, prev);
        auto next = dtwa_sat_synthetize(src, target_acc_number,
                                        target_acc, target, state_based,
                                        colored);
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

  twa_graph_ptr
  sat_minimize(twa_graph_ptr a, const char* opt, bool state_based)
  {
    option_map om;
    auto err = om.parse_options(opt);
    if (err)
      {
        std::string e = "failed to parse option near ";
        e += err;
        throw std::runtime_error(e);
      }

    if (!is_deterministic(a))
      throw std::runtime_error
        ("SAT-based minimization only works with deterministic automata");

    bool dicho = om.get("dichotomy", 0);
    int states = om.get("states", -1);
    int max_states = om.get("max-states", -1);
    auto accstr = om.get_str("acc");
    bool colored = om.get("colored", 0);
    int preproc = om.get("preproc", 3);

    // No more om.get() below this.
    om.report_unused_options();

    // Assume we are going to use the input automaton acceptance...
    bool user_supplied_acc = false;
    acc_cond::acc_code target_acc = a->get_acceptance();
    int nacc = a->num_sets();

    if (accstr == "same")
      accstr.clear();
    // ... unless the user specified otherwise
    if (!accstr.empty())
      {
        user_supplied_acc = true;
        target_acc = acc_cond::acc_code(accstr.c_str());
        // Just in case we were given something like
        //  Fin(1) | Inf(3)
        // Rewrite it as
        //  Fin(0) | Inf(1)
        // without holes in the set numbers
        acc_cond::mark_t used = target_acc.used_sets();
        acc_cond a(used.max_set());
        target_acc = target_acc.strip(a.comp(used), true);
        nacc = used.count();
      }

    bool target_is_buchi = false;
    {
      acc_cond acccond(nacc);
      acccond.set_acceptance(target_acc);
      target_is_buchi = acccond.is_buchi();
    }

    if (preproc)
      {
        postprocessor post;
        auto sba = (state_based && a->prop_state_acc()) ?
          postprocessor::SBAcc : postprocessor::Any;
        post.set_pref(postprocessor::Deterministic
                      | postprocessor::Complete
                      | sba);
        post.set_type(postprocessor::Generic);
        postprocessor::optimization_level level;
        switch (preproc)
          {
          case 1:
            level = postprocessor::Low;
            break;
          case 2:
            level = postprocessor::Medium;
            break;
          case 3:
            level = postprocessor::High;
            break;
          default:
            throw
              std::runtime_error("preproc should be a value between 0 and 3.");
          }
        post.set_level(level);
        a = post.run(a, nullptr);
        // If we have WDBA, it is necessarily minimal because
        // postprocessor always run WDBA minimization in Deterministic
        // mode.  If the desired output is a Büchi automaton, or not
        // desired acceptance was specified, stop here.  There is not
        // point in minimizing a minimal automaton.
        if (a->prop_inherently_weak() && a->prop_deterministic()
            && (target_is_buchi || !user_supplied_acc))
          return a;
      }
    else
      {
        complete_here(a);
      }

    if (states == -1 && max_states == -1)
      {
        if (state_based)
          max_states = sbacc(a)->num_states();
        else
          max_states = a->num_states();
        // If we have not user-supplied acceptance, the input
        // automaton is a valid one, so we start the search with one
        // less state.
        max_states -= !user_supplied_acc;
      }


    if (states == -1)
      {
        auto orig = a;
        if (!target_is_buchi || !a->acc().is_buchi() || colored)
          a = (dicho ? dtwa_sat_minimize_dichotomy : dtwa_sat_minimize)
            (a, nacc, target_acc, state_based, max_states, colored);
        else
          a = (dicho ? dtba_sat_minimize_dichotomy : dtba_sat_minimize)
            (a, state_based, max_states);

        if (!a && !user_supplied_acc)
          a = orig;
      }
    else
      {
        if (!target_is_buchi || !a->acc().is_buchi() || colored)
          a = dtwa_sat_synthetize(a, nacc, target_acc, states,
                                  state_based, colored);
        else
          a = dtba_sat_synthetize(a, states, state_based);
      }

    if (a)
      {
        if (state_based)
          a = scc_filter_states(a);
        else
          a = scc_filter(a);
      }
    return a;
  }

}
