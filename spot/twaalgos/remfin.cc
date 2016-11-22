// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016 Laboratoire de Recherche et
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

#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <iostream>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/mask.hh>

//#define TRACE
#ifdef TRACE
#define trace std::cerr
#else
#define trace while (0) std::cerr
#endif

namespace spot
{
  namespace
  {
    // Check whether the SCC composed of all states STATES, and
    // visiting all acceptance marks in SETS contains non-accepting
    // cycles.
    //
    // A cycle is accepting (in a Rabin automaton) if there exists an
    // acceptance pair (Fᵢ, Iᵢ) such that some states from Iᵢ are
    // visited while no states from Fᵢ are visited.
    //
    // Consequently, a cycle is non-accepting if for all acceptance
    // pairs (Fᵢ, Iᵢ), either no states from Iᵢ are visited or some
    // states from Fᵢ are visited.  (This corresponds to an accepting
    // cycle with Streett acceptance.)
    static bool
    is_scc_ba_type(const const_twa_graph_ptr& aut,
                   const std::vector<unsigned>& states,
                   std::vector<bool>& final,
                   acc_cond::mark_t inf_pairs,
                   acc_cond::mark_t inf_alone,
                   acc_cond::mark_t sets)
    {
      // Consider the SCC as one large cycle and check its
      // intersection with all Fᵢs and Iᵢs: This is the SETS
      // variable.
      //
      // Let f=[F₁,F₂,...] and i=[I₁,I₂,...] be bitvectors where bit
      // Fᵢ (resp. Iᵢ) indicates that Fᵢ (resp. Iᵢ) has been visited
      // in the SCC.
      acc_cond::mark_t f = (sets << 1U) & inf_pairs;
      acc_cond::mark_t i = sets & inf_pairs;
      // If we have i&!f = [0,0,...] that means that the cycle formed
      // by the entire SCC is not accepting.  However that does not
      // necessarily imply that all cycles in the SCC are also
      // non-accepting.  We may have a smaller cycle that is
      // accepting, but which becomes non-accepting when extended with
      // more states.
      i -= f;
      i |= (inf_alone & sets);
      if (!i)
        {
          // Check whether the SCC is accepting.  We do that by simply
          // converting that SCC into a TGBA and running our emptiness
          // check.  This is not a really smart implementation and
          // could be improved.
          std::vector<bool> keep(aut->num_states(), false);
          for (auto s: states)
            keep[s] = true;
          auto sccaut = mask_keep_accessible_states(aut, keep, states.front());
          // Force SBA to false.  It does not affect the emptiness
          // check result, however it prevent recurring into this
          // procedure, because empty() will call to_tgba() which will
          // call remove_fin()...
          sccaut->prop_state_acc(false);
          // If SCCAUT is empty, the SCC is BA-type (and none
          // of its states are final).  If SCCAUT is nonempty, the SCC
          // is not BA type.
          return sccaut->is_empty();
        }
      // The bits remaining sets in i corresponds to I₁s that have
      // been seen with seeing the mathing F₁.  In this SCC any state
      // in these I₁ is therefore final.  Otherwise we do not know: it
      // is possible that there is a non-accepting cycle in the SCC
      // that do not visit Fᵢ.
      std::set<unsigned> unknown;
      for (auto s: states)
        {
          if (aut->state_acc_sets(s) & i)
            final[s] = true;
          else
            unknown.insert(s);
        }
      // Check whether it is possible to build non-accepting cycles
      // using only the "unknown" states.
      while (!unknown.empty())
        {
          std::vector<bool> keep(aut->num_states(), false);
          for (auto s: unknown)
            keep[s] = true;

          scc_info si(mask_keep_states(aut, keep, *unknown.begin()));
          unsigned scc_max = si.scc_count();
          for (unsigned scc = 0; scc < scc_max; ++scc)
            {
              for (auto s: si.states_of(scc))
                unknown.erase(s);
              if (si.is_rejecting_scc(scc)) // this includes trivial SCCs
                continue;
              if (!is_scc_ba_type(aut, si.states_of(scc),
                                  final, inf_pairs, 0U, si.acc(scc)))
                return false;
            }
        }
      return true;
    }

    // Specialized conversion from Rabin acceptance to Büchi acceptance.
    // Is able to detect SCCs that are Büchi-type (i.e., they can be
    // converted to Büchi acceptance without chaning their structure).
    // Currently only works with state-based acceptance.
    //
    // See "Deterministic ω-automata vis-a-vis Deterministic Büchi
    // Automata", S. Krishnan, A. Puri, and R. Brayton (ISAAC'94) for
    // some details about detecting Büchi-typeness.
    //
    // We essentially apply this method SCC-wise.  The paper is
    // concerned about *deterministic* automata, but we apply the
    // algorithm on non-deterministic automata as well: in the worst
    // case it is possible that a Büchi-type SCC with some
    // non-deterministic has one accepting and one rejecting run for
    // the same word.  In this case we may fail to detect the
    // Büchi-typeness of the SCC, but the resulting automaton should
    // be correct nonetheless.
    static twa_graph_ptr
    ra_to_ba(const const_twa_graph_ptr& aut,
             acc_cond::mark_t inf_pairs,
             acc_cond::mark_t inf_alone,
             acc_cond::mark_t fin_alone)
    {
      assert((bool)aut->prop_state_acc());

      scc_info si(aut);
      // For state-based Rabin automata, we check each SCC for
      // BA-typeness.  If an SCC is BA-type, its final states are stored
      // in BA_FINAL_STATES.
      std::vector<bool> scc_is_ba_type(si.scc_count(), false);
      bool ba_type = false;
      std::vector<bool> ba_final_states;

#ifdef DEBUG
      acc_cond::mark_t fin;
      acc_cond::mark_t inf;
      std::tie(inf, fin) = aut->get_acceptance().used_inf_fin_sets();
      assert(inf == (inf_pairs | inf_alone));
      assert(fin == ((inf_pairs >> 1U) | fin_alone));
#endif
      ba_final_states.resize(aut->num_states(), false);
      ba_type = true;                // until proven otherwise
      unsigned scc_max = si.scc_count();
      for (unsigned scc = 0; scc < scc_max; ++scc)
        {
          if (si.is_rejecting_scc(scc)) // this includes trivial SCCs
            {
              scc_is_ba_type[scc] = true;
              continue;
            }
          bool scc_ba_type = false;
          auto sets = si.acc(scc);
          // If there is one fin_alone that is not in the SCC,
          // any cycle in the SCC is accepting.  Mark all states
          // as final.
          if ((sets & fin_alone) != fin_alone)
            {
              for (auto s: si.states_of(scc))
                ba_final_states[s] = true;
              scc_ba_type = true;
            }
          // Conversely, if all fin_alone appear in the SCC, then it
          // cannot be accepting.
          else if (sets & fin_alone)
            {
              scc_ba_type = false;
            }
          // In the generale case (no fin_alone involved), we need
          // a dedicated check.
          else
            {
              scc_ba_type = is_scc_ba_type(aut, si.states_of(scc),
                                           ba_final_states,
                                           inf_pairs, inf_alone, si.acc(scc));
            }
          ba_type &= scc_ba_type;
          scc_is_ba_type[scc] = scc_ba_type;
        }

#ifdef TRACE
      trace << "SCC DBA-realizibility\n";
      for (unsigned scc = 0; scc < scc_max; ++scc)
        {
            trace << scc << ": " << scc_is_ba_type[scc] << " {";
            for (auto s: si.states_of(scc))
              trace << ' ' << s;
            trace << " }\n";
        }
#endif

      unsigned nst = aut->num_states();
      auto res = make_twa_graph(aut->get_dict());
      res->copy_ap_of(aut);
      res->prop_copy(aut, { true, false, false, true });
      res->new_states(nst);
      res->set_buchi();
      res->set_init_state(aut->get_init_state_number());
      trival deterministic = aut->prop_deterministic();

      std::vector<unsigned> state_map(aut->num_states());
      for (unsigned n = 0; n < scc_max; ++n)
        {
          auto states = si.states_of(n);

          if (scc_is_ba_type[n])
            {
              // If the SCC is BA-type, we know exactly what state need to
              // be marked as accepting.
              for (auto s: states)
                {
                  bool acc = ba_final_states[s];
                  for (auto& t: aut->out(s))
                    res->new_acc_edge(s, t.dst, t.cond, acc);
                }
              continue;
            }
          else
            {
              deterministic = false;

              // The main copy is only accepting for inf_alone
              // and for all Inf sets that have no matching Fin
              // sets in this SCC.
              acc_cond::mark_t sccsets = si.acc(n);
              acc_cond::mark_t f = (sccsets << 1U) & inf_pairs;
              acc_cond::mark_t i = sccsets & (inf_pairs | inf_alone);
              i -= f;
              for (auto s: states)
                {
                  bool acc = aut->state_acc_sets(s) & i;
                  for (auto& t: aut->out(s))
                    res->new_acc_edge(s, t.dst, t.cond, acc);
                }

              auto rem = sccsets & ((inf_pairs >> 1U) | fin_alone);
              assert(rem != 0U);
              auto sets = rem.sets();

              unsigned ss = states.size();

              for (auto r: sets)
                {
                  unsigned base = res->new_states(ss);
                  for (auto s: states)
                    state_map[s] = base++;
                  for (auto s: states)
                    {
                      auto ns = state_map[s];
                      acc_cond::mark_t acc = aut->state_acc_sets(s);
                      if (acc.has(r))
                        continue;
                      bool jacc = acc & inf_alone;
                      bool cacc = fin_alone.has(r) || acc.has(r + 1);
                      for (auto& t: aut->out(s))
                        {
                          if (si.scc_of(t.dst) != n)
                            continue;
                          auto nd = state_map[t.dst];
                          res->new_acc_edge(ns, nd, t.cond, cacc);
                          // We need only one non-deterministic jump per
                          // cycle.  As an approximation, we only do
                          // them on back-links.
                          if (t.dst <= s)
                            res->new_acc_edge(s, nd, t.cond, jacc);
                        }
                    }
                }
            }
        }
      res->purge_dead_states();
      res->prop_deterministic(deterministic);
      return res;
    }

    static twa_graph_ptr
    rabin_to_buchi_maybe(const const_twa_graph_ptr& aut)
    {
      if (!aut->prop_state_acc().is_true())
        return nullptr;

      auto code = aut->get_acceptance();

      if (code.is_t())
        return nullptr;

      acc_cond::mark_t inf_pairs = 0U;
      acc_cond::mark_t inf_alone = 0U;
      acc_cond::mark_t fin_alone = 0U;

      auto s = code.back().size;

      // Rabin 1
      if (code.back().op == acc_cond::acc_op::And && s == 4)
        goto start_and;
      // Co-Büchi
      else if (code.back().op == acc_cond::acc_op::Fin && s == 1)
        goto start_fin;
      // Rabin >1
      else if (code.back().op != acc_cond::acc_op::Or)
        return nullptr;

      while (s)
        {
          --s;
          if (code[s].op == acc_cond::acc_op::And)
            {
            start_and:
              auto o1 = code[--s].op;
              auto m1 = code[--s].mark;
              auto o2 = code[--s].op;
              auto m2 = code[--s].mark;
              // We expect
              //   Fin({n}) & Inf({n+1})
              if (o1 != acc_cond::acc_op::Fin ||
                  o2 != acc_cond::acc_op::Inf ||
                  m1.count() != 1 ||
                  m2.count() != 1 ||
                  m2 != (m1 << 1U))
                return nullptr;
              inf_pairs |= m2;
            }
          else if (code[s].op == acc_cond::acc_op::Fin)
            {
            start_fin:
              fin_alone |= code[--s].mark;
            }
          else if (code[s].op == acc_cond::acc_op::Inf)
            {
              auto m1 = code[--s].mark;
              if (m1.count() != 1)
                return nullptr;
              inf_alone |= m1;
            }
          else
            {
              return nullptr;
            }
        }

      trace << "inf_pairs: " << inf_pairs << '\n';
      trace << "inf_alone: " << inf_alone << '\n';
      trace << "fin_alone: " << fin_alone << '\n';
      return ra_to_ba(aut, inf_pairs, inf_alone, fin_alone);
    }



    // If the DNF is
    //  Fin(1)&Inf(2)&Inf(4) | Fin(2)&Fin(3)&Inf(1) |
    //  Inf(1)&Inf(3) | Inf(1)&Inf(2) | Fin(4)
    // this returns the following map:
    //  {1}   => Inf(2)&Inf(4)
    //  {2,3} => Inf(1)
    //  {}    => Inf(1)&Inf(3) | Inf(1)&Inf(2)
    //  {4}   => t
    static std::map<acc_cond::mark_t, acc_cond::acc_code>
    split_dnf_acc_by_fin(const acc_cond::acc_code& acc)
    {
      std::map<acc_cond::mark_t, acc_cond::acc_code> res;
      auto pos = &acc.back();
      if (pos->op == acc_cond::acc_op::Or)
        --pos;
      auto start = &acc.front();
      while (pos > start)
        {
          if (pos->op == acc_cond::acc_op::Fin)
            {
              // We have only a Fin term, without Inf.  In this case
              // only, the Fin() may encode a disjunction of sets.
              for (auto s: pos[-1].mark.sets())
                {
                  acc_cond::mark_t fin = 0U;
                  fin.set(s);
                  res[fin] = acc_cond::acc_code{};
                }
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
              acc_cond::acc_word w[2];
              w[0].mark = inf;
              w[1].op = acc_cond::acc_op::Inf;
              w[1].size = 1;
              acc_cond::acc_code c;
              c.insert(c.end(), w, w + 2);
              auto p = res.emplace(fin, c);
              if (!p.second)
                p.first->second |= std::move(c);
            }
        }
      return res;
    }

    static twa_graph_ptr
    remove_fin_weak(const const_twa_graph_ptr& aut)
    {
      // Clone the original automaton.
      auto res = make_twa_graph(aut,
                                {
                                  true, // state based
                                    true, // inherently weak
                                    true, // determinisitic
                                    true,  // stutter inv.
                                    });
      scc_info si(res);

      // We will modify res in place, and the resulting
      // automaton will only have one acceptance set.
      acc_cond::mark_t all_acc = res->set_buchi();
      res->prop_state_acc(true);
      unsigned n = res->num_states();

      for (unsigned src = 0; src < n; ++src)
        {
          acc_cond::mark_t acc = 0U;
          unsigned scc = si.scc_of(src);
          if (si.is_accepting_scc(scc) && !si.is_trivial(scc))
            acc = all_acc;
          for (auto& t: res->out(src))
            t.acc = acc;
        }
      return res;
    }
  }

  twa_graph_ptr remove_fin(const const_twa_graph_ptr& aut)
  {
    if (!aut->acc().uses_fin_acceptance())
      return std::const_pointer_cast<twa_graph>(aut);

    // FIXME: we should check whether the automaton is inherently weak.
    if (aut->prop_weak().is_true())
      return remove_fin_weak(aut);

    if (auto maybe = streett_to_generalized_buchi_maybe(aut))
      return maybe;

    if (auto maybe = rabin_to_buchi_maybe(aut))
      return maybe;

    {
      // We want a clean acceptance condition, i.e., one where all
      // sets are useful.  If that is not the case, clean it first.
      acc_cond::mark_t unused = aut->acc().all_sets();
      for (auto& t: aut->edges())
        {
          unused -= t.acc;
          if (!unused)
            break;
        }
      if (unused)
        return remove_fin(cleanup_acceptance(aut));
    }

    std::vector<acc_cond::acc_code> code;
    std::vector<acc_cond::mark_t> rem;
    std::vector<acc_cond::mark_t> keep;
    std::vector<acc_cond::mark_t> add;
    bool has_true_term = false;
    acc_cond::mark_t allinf = 0U;
    acc_cond::mark_t allfin = 0U;
    {
      auto acccode = aut->get_acceptance();
      if (!acccode.is_dnf())
        acccode = acccode.to_dnf();

      auto split = split_dnf_acc_by_fin(acccode);

      auto sz = split.size();
      assert(sz > 0);

      rem.reserve(sz);
      code.reserve(sz);
      keep.reserve(sz);
      add.reserve(sz);
      for (auto p: split)
        {
          // The empty Fin should always come first
          assert(p.first != 0U || rem.empty());
          rem.emplace_back(p.first);
          allfin |= p.first;
          acc_cond::mark_t inf = 0U;
          if (!p.second.empty())
            {
              auto pos = &p.second.back();
              auto end = &p.second.front();
              while (pos > end)
                {
                  switch (pos->op)
                    {
                    case acc_cond::acc_op::And:
                    case acc_cond::acc_op::Or:
                      --pos;
                      break;
                    case acc_cond::acc_op::Inf:
                      inf |= pos[-1].mark;
                      pos -= 2;
                      break;
                    case acc_cond::acc_op::Fin:
                    case acc_cond::acc_op::FinNeg:
                    case acc_cond::acc_op::InfNeg:
                      SPOT_UNREACHABLE();
                      break;
                    }
                }
            }
          if (inf == 0U)
            {
              has_true_term = true;
            }
          code.emplace_back(std::move(p.second));
          keep.emplace_back(inf);
          allinf |= inf;
          add.emplace_back(0U);
        }
    }
    assert(add.size() > 0);

    acc_cond acc = aut->acc();
    unsigned extra_sets = 0;

    // Do we have common sets between the acceptance terms?
    // If so, we need extra sets to distinguish the terms.
    bool interference = false;
    {
      auto sz = keep.size();
      acc_cond::mark_t sofar = 0U;
      for (unsigned i = 0; i < sz; ++i)
        {
          auto k = keep[i];
          if (k & sofar)
            {
              interference = true;
              break;
            }
          sofar |= k;
        }
      if (interference)
        {
          trace << "We have interferences\n";
          // We need extra set, but we will try
          // to reuse the Fin number if they are
          // not used as Inf as well.
          std::vector<int> exs(acc.num_sets());
          for (auto f: allfin.sets())
            {
              if (allinf.has(f)) // Already used as Inf
                {
                  exs[f] = acc.add_set();
                  ++extra_sets;
                }
              else
                {
                  exs[f] = f;
                }
            }
          for (unsigned i = 0; i < sz; ++i)
            {
              acc_cond::mark_t m = 0U;
              for (auto f: rem[i].sets())
                m.set(exs[f]);
              trace << "rem[" << i << "] = " << rem[i]
                    << "  m = " << m << '\n';
              add[i] = m;
              code[i] &= acc.inf(m);
              trace << "code[" << i << "] = " << code[i] << '\n';
            }
        }
      else if (has_true_term)
        {
          trace << "We have a true term\n";
          unsigned one = acc.add_sets(1);
          extra_sets += 1;
          acc_cond::mark_t m({one});
          auto c = acc.inf(m);
          for (unsigned i = 0; i < sz; ++i)
            {
              if (!code[i].is_t())
                continue;
              add[i] = m;
              code[i] &= std::move(c);
              c = acc.fin(0U);        // Use false for the other terms.
              trace << "code[" << i << "] = " << code[i] << '\n';
            }

        }
    }

    acc_cond::acc_code new_code = aut->acc().fin(0U);
    for (auto c: code)
      new_code |= std::move(c);

    unsigned cs = code.size();
    for (unsigned i = 0; i < cs; ++i)
      trace << i << " Rem " << rem[i] << "  Code " << code[i]
            << " Keep " << keep[i] << '\n';

    unsigned nst = aut->num_states();
    auto res = make_twa_graph(aut->get_dict());
    res->copy_ap_of(aut);
    res->prop_copy(aut, { true, false, false, true });
    res->new_states(nst);
    res->set_acceptance(aut->num_sets() + extra_sets, new_code);
    res->set_init_state(aut->get_init_state_number());

    bool sbacc = aut->prop_state_acc().is_true();
    scc_info si(aut);
    unsigned nscc = si.scc_count();
    std::vector<unsigned> state_map(nst);
    for (unsigned n = 0; n < nscc; ++n)
      {
        auto m = si.acc(n);
        auto states = si.states_of(n);
        trace << "SCC #" << n << " uses " << m << '\n';

        // What to keep and add into the main copy
        acc_cond::mark_t main_sets = 0U;
        acc_cond::mark_t main_add = 0U;
        bool intersects_fin = false;
        for (unsigned i = 0; i < cs; ++i)
          if (!(m & rem[i]))
            {
              main_sets |= keep[i];
              main_add |= add[i];
            }
          else
            {
              intersects_fin = true;
            }
        trace << "main_sets " << main_sets << "\nmain_add " << main_add << '\n';

        // Create the main copy
        for (auto s: states)
          for (auto& t: aut->out(s))
            {
              acc_cond::mark_t a = 0U;
              if (sbacc || SPOT_LIKELY(si.scc_of(t.dst) == n))
                a = (t.acc & main_sets) | main_add;
              res->new_edge(s, t.dst, t.cond, a);
            }

        // We do not need any other copy if the SCC is non-accepting,
        // of if it does not intersect any Fin.
        if (!intersects_fin || si.is_rejecting_scc(n))
          continue;

        // Create clones
        for (unsigned i = 0; i < cs; ++i)
          if (m & rem[i])
            {
              auto r = rem[i];
              trace << "rem[" << i << "] = " << r << " requires a copy\n";
              unsigned base = res->new_states(states.size());
              for (auto s: states)
                state_map[s] = base++;
              auto k = keep[i];
              auto a = add[i];
              for (auto s: states)
                {
                  auto ns = state_map[s];
                  for (auto& t: aut->out(s))
                    {
                      if ((t.acc & r) || si.scc_of(t.dst) != n)
                        continue;
                      auto nd = state_map[t.dst];
                      res->new_edge(ns, nd, t.cond, (t.acc & k) | a);
                      // We need only one non-deterministic jump per
                      // cycle.  As an approximation, we only do
                      // them on back-links.
                      if (t.dst <= s)
                        {
                          acc_cond::mark_t a = 0U;
                          if (sbacc)
                            a = (t.acc & main_sets) | main_add;
                          res->new_edge(s, nd, t.cond, a);
                        }
                    }
                }
            }
      }

    // If the input had no Inf, the output is a state-based automaton.
    if (allinf == 0U)
      res->prop_state_acc(true);

    res->purge_dead_states();
    trace << "before cleanup: " << res->get_acceptance() << '\n';
    cleanup_acceptance_here(res);
    trace << "after cleanup: " << res->get_acceptance() << '\n';
    res->merge_edges();
    return res;
  }
}
