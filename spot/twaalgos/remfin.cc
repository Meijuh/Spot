// -*- coding: utf-8 -*-
// Copyright (C) 2015-2017 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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
#include <spot/twaalgos/alternation.hh>

// #define TRACE
#ifdef TRACE
#define trace std::cerr
#else
#define trace while (0) std::cerr
#endif

namespace spot
{
  namespace
  {
    enum strategy_t
    {
      trivial     = 1U,
      weak        = 2U,
      alternation = 4U,
      rabin       = 8U,
      streett     = 16U,
    };

    using strategy =
        std::function<twa_graph_ptr(const const_twa_graph_ptr& aut)>;

    twa_graph_ptr
    remove_fin_impl(const const_twa_graph_ptr&, const strategy_t);

    using EdgeMask = std::vector<bool>;

    template< typename Edges, typename Apply >
    void for_each_edge(const const_twa_graph_ptr& aut,
                       const Edges& edges,
                       const EdgeMask& mask,
                       Apply apply)
    {
      for (const auto& e: edges)
        {
          unsigned edge_id = aut->edge_number(e);
          if (mask[edge_id])
            apply(edge_id);
        }
    }

    template< typename Edges >
    acc_cond::mark_t scc_acc_marks(const_twa_graph_ptr aut,
                                   const Edges& edges,
                                   const EdgeMask& mask)
    {
      acc_cond::mark_t scc_mark = 0U;
      for_each_edge(aut, edges, mask, [&] (unsigned e)
        {
          scc_mark |= aut->edge_data(e).acc;
        });
      return scc_mark;
    }

    // Transforms automaton from transition based acceptance to state based
    // acceptance.
    void make_state_acc(twa_graph_ptr & aut)
    {
      unsigned nst = aut->num_states();
      for (unsigned s = 0; s < nst; ++s)
        {
          acc_cond::mark_t acc = 0U;
          for (auto& t: aut->out(s))
            acc |= t.acc;
          for (auto& t: aut->out(s))
            t.acc = acc;
        }
      aut->prop_state_acc(true);
    }


    // Check whether the SCC contains non-accepting cycles.
    //
    // A cycle is accepting (in a Rabin automaton) if there exists an
    // acceptance pair (Fᵢ, Iᵢ) such that some states from Iᵢ are
    // visited while no states from Fᵢ are visited.
    //
    // Consequently, a cycle is non-accepting if for all acceptance
    // pairs (Fᵢ, Iᵢ), either no states from Iᵢ are visited or some
    // states from Fᵢ are visited.  (This corresponds to an accepting
    // cycle with Streett acceptance.)
    //
    // final are those edges which are used in the resulting tba
    // acceptance condition.
    bool is_scc_tba_type(const_twa_graph_ptr aut,
                         const scc_info& si,
                         const unsigned scc,
                         const std::vector<bool>& keep,
                         const rs_pairs_view& aut_pairs,
                         std::vector<bool>& final)
    {
      if (si.is_rejecting_scc(scc))
        return true;

      auto scc_acc = scc_acc_marks(aut, si.inner_edges_of(scc), keep);
      auto scc_pairs = rs_pairs_view(aut_pairs.pairs(), scc_acc);
      // If there is one aut_fin_alone that is not in the SCC,
      // any cycle in the SCC is accepting.
      if (scc_pairs.fins_alone().proper_subset(aut_pairs.fins_alone()))
        {
          for_each_edge(aut, si.edges_of(scc), keep, [&](unsigned e)
            {
              final[e] = true;
            });
          return true;
        }

      auto scc_infs_alone = scc_pairs.infs_alone();
      // Firstly consider whole SCC as one large cycle.  If there is
      // no inf without matching fin then the cycle formed by the
      // entire SCC is not accepting.  However that does not
      // necessarily imply that all cycles in the SCC are also
      // non-accepting.  We may have a smaller cycle that is
      // accepting, but which becomes non-accepting when extended with
      // more edges.
      if (!scc_infs_alone)
        {
          // Check whether the SCC is accepting.  We do that by simply
          // converting that SCC into a TGBA and running our emptiness
          // check.  This is not a really smart implementation and
          // could be improved.
          auto& states = si.states_of(scc);
          std::vector<bool> keep_states(aut->num_states(), false);
          for (auto s: states)
            keep_states[s] = true;
          auto sccaut = mask_keep_accessible_states(aut,
                                                    keep_states,
                                                    states.front());
          // Prevent recurring into this function by skipping the
          // Rabin strategy
          auto skip = strategy_t::rabin;
          // If SCCAUT is empty, the SCC is BA-type (and none of its
          // states are final).  If SCCAUT is nonempty, the SCC is not
          // BA type
          return remove_fin_impl(sccaut, skip)->is_empty();
        }

      // Remaining infs corresponds to I₁s that have been seen with seeing
      // the mathing F₁. In this SCC any edge in these I₁ is therefore
      // final. Otherwise we do not know: it is possible that there is
      // a non-accepting cycle in the SCC that do not visit Fᵢ.
      std::set<unsigned> unknown;
      for_each_edge(aut, si.inner_edges_of(scc), keep, [&](unsigned e)
        {
          const auto& ed = aut->edge_data(e);
          if (ed.acc & scc_infs_alone)
              final[e] = true;
          else
              unknown.insert(e);
        });

      // Erase edges that cannot belong to a cycle, i.e., that edges
      // whose 'dst' is not 'src' of any unknown edges.
      std::vector<unsigned> remove;
      do
        {
          remove.clear();
          std::set<unsigned> srcs;
          for (auto e: unknown)
            srcs.insert(aut->edge_storage(e).src);
          for (auto e: unknown)
            if (srcs.find(aut->edge_storage(e).dst) == srcs.end())
              remove.push_back(e);
          for (auto r: remove)
            unknown.erase(r);
        }
      while (!remove.empty());

      // Check whether it is possible to build non-accepting cycles
      // using only the "unknown" edges.
      using filter_data_t = std::pair<const_twa_graph_ptr, std::vector<bool>&>;

      scc_info::edge_filter filter =
        [](const twa_graph::edge_storage_t& t, unsigned, void* data)
          -> scc_info::edge_filter_choice
        {
          auto& d = *static_cast<filter_data_t*>(data);
          if (d.second[d.first->edge_number(t)])
            return scc_info::edge_filter_choice::keep;
          else
            return scc_info::edge_filter_choice::ignore;
        };

      {
        std::vector<bool> keep;
        while (!unknown.empty())
          {
            keep.assign(aut->edge_vector().size(), false);
            for (auto e: unknown)
              keep[e] = true;

            auto filter_data = filter_data_t{aut, keep};
            auto init = aut->edge_storage(*unknown.begin()).src;
            scc_info si(aut, init, filter, &filter_data);

            for (unsigned uscc = 0; uscc < si.scc_count(); ++uscc)
              {
                for_each_edge(aut, si.edges_of(uscc), keep, [&](unsigned e)
                              {
                                unknown.erase(e);
                              });
                if (si.is_rejecting_scc(uscc))
                  continue;
                if (!is_scc_tba_type(aut, si, uscc, keep, aut_pairs, final))
                  return false;
              }
          }
      }
      return true;
    }

    // Specialized conversion from transition based Rabin acceptance to
    // transition based Büchi acceptance.
    // Is able to detect SCCs that are TBA-type (i.e., they can be
    // converted to Büchi acceptance without chaning their structure).
    //
    // See "Deterministic ω-automata vis-a-vis Deterministic Büchi
    // Automata", S. Krishnan, A. Puri, and R. Brayton (ISAAC'94) for
    // some details about detecting Büchi-typeness.
    //
    // We essentially apply this method SCC-wise. The paper is
    // concerned about *deterministic* automata, but we apply the
    // algorithm on non-deterministic automata as well: in the worst
    // case it is possible that a TBA-type SCC with some
    // non-deterministic has one accepting and one rejecting run for
    // the same word.  In this case we may fail to detect the
    // TBA-typeness of the SCC, but the resulting automaton should
    // be correct nonetheless.
    twa_graph_ptr
    tra_to_tba(const const_twa_graph_ptr& inaut)
    {
      // cleanup acceptance for easy detection of alone fins and infs
      auto aut = cleanup_acceptance(inaut);

      std::vector<acc_cond::rs_pair> pairs;
      if (!aut->acc().is_rabin_like(pairs))
        return nullptr;

      auto aut_pairs = rs_pairs_view(pairs);
      auto code = aut->get_acceptance();
      if (code.is_t())
        return nullptr;

      // if is TBA type
      scc_info si(aut, scc_info_options::TRACK_STATES);
      std::vector<bool> scc_is_tba_type(si.scc_count(), false);
      std::vector<bool> final(aut->edge_vector().size(), false);
      std::vector<bool> keep(aut->edge_vector().size(), true);

      for (unsigned scc = 0; scc < si.scc_count(); ++scc)
        scc_is_tba_type[scc] = is_scc_tba_type(aut, si, scc, keep,
                                               aut_pairs, final);

      auto res = make_twa_graph(aut->get_dict());
      res->copy_ap_of(aut);
      res->prop_copy(aut, { false, false, false, false, false, true });
      res->new_states(aut->num_states());
      res->set_buchi();
      res->set_init_state(aut->get_init_state_number());
      trival deterministic = aut->prop_universal();
      trival complete = aut->prop_complete();

      std::vector<unsigned> state_map(aut->num_states());
      for (unsigned scc = 0; scc < si.scc_count(); ++scc)
        {
          auto states = si.states_of(scc);

          if (scc_is_tba_type[scc])
            {
              for (const auto& e: si.edges_of(scc))
                {
                  bool acc = final[aut->edge_number(e)];
                  res->new_acc_edge(e.src, e.dst, e.cond, acc);
                }
            }
          else
            {
              complete = trival::maybe();

              // The main copy is only accepting for inf_alone
              // and for all Inf sets that have no matching Fin
              // sets in this SCC.
              auto scc_pairs = rs_pairs_view(pairs, si.acc_sets_of(scc));
              auto scc_infs_alone = scc_pairs.infs_alone();

              for (const auto& e: si.edges_of(scc))
                {
                  bool acc{e.acc & scc_infs_alone};
                  res->new_acc_edge(e.src, e.dst, e.cond, acc);
                }

              auto fins_alone = aut_pairs.fins_alone();

              for (auto r: scc_pairs.fins().sets())
                {
                  unsigned base = res->new_states(states.size());
                  for (auto s: states)
                      state_map[s] = base++;
                  for (const auto& e: si.inner_edges_of(scc))
                    {
                      if (e.acc.has(r))
                        continue;
                      auto src = state_map[e.src];
                      auto dst = state_map[e.dst];
                      bool cacc = fins_alone.has(r)
                                ? true
                                : ((scc_pairs.paired_with(r) & e.acc) != 0);
                      res->new_acc_edge(src, dst, e.cond, cacc);
                      // We need only one non-deterministic jump per
                      // cycle.  As an approximation, we only do
                      // them on back-links.
                      if (e.dst <= e.src)
                        {
                          deterministic = false;
                          bool jacc = ((e.acc & scc_infs_alone) != 0);
                          res->new_acc_edge(e.src, dst, e.cond, jacc);
                        }
                    }
                }
            }
        }
      res->prop_complete(complete);
      res->prop_universal(deterministic);
      res->purge_dead_states();
      res->merge_edges();
      if (!aut_pairs.infs())
        make_state_acc(res);
      return res;
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
      if (pos->sub.op == acc_cond::acc_op::Or)
        --pos;
      auto start = &acc.front();
      while (pos > start)
        {
          if (pos->sub.op == acc_cond::acc_op::Fin)
            {
              // We have only a Fin term, without Inf.  In this case
              // only, the Fin() may encode a disjunction of sets.
              for (auto s: pos[-1].mark.sets())
                {
                  acc_cond::mark_t fin = 0U;
                  fin.set(s);
                  res[fin] = acc_cond::acc_code{};
                }
              pos -= pos->sub.size + 1;
            }
          else
            {
              // We have a conjunction of Fin and Inf sets.
              auto end = pos - pos->sub.size - 1;
              acc_cond::mark_t fin = 0U;
              acc_cond::mark_t inf = 0U;
              while (pos > end)
                {
                  switch (pos->sub.op)
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
              w[1].sub.op = acc_cond::acc_op::Inf;
              w[1].sub.size = 1;
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
                                  true, true, // determinisitic
                                  true,       // complete
                                  true,  // stutter inv.
                                });
      scc_info si(res, scc_info_options::NONE);

      // We will modify res in place, and the resulting
      // automaton will only have one acceptance set.
      acc_cond::mark_t all_acc = res->set_buchi();
      res->prop_state_acc(true);
      unsigned n = res->num_states();

      for (unsigned src = 0; src < n; ++src)
        {
          if (!si.reachable_state(src))
            continue;
          acc_cond::mark_t acc = 0U;
          unsigned scc = si.scc_of(src);
          if (si.is_accepting_scc(scc) && !si.is_trivial(scc))
            acc = all_acc;
          for (auto& t: res->out(src))
            t.acc = acc;
        }
      return res;
    }

    twa_graph_ptr trivial_strategy(const const_twa_graph_ptr& aut)
    {
      return (!aut->acc().uses_fin_acceptance())
             ? std::const_pointer_cast<twa_graph>(aut)
             : nullptr;
    }

    twa_graph_ptr weak_strategy(const const_twa_graph_ptr& aut)
    {
      // FIXME: we should check whether the automaton is inherently weak.
      return (aut->prop_weak().is_true())
             ? remove_fin_weak(aut)
             : nullptr;
    }

    twa_graph_ptr alternation_strategy(const const_twa_graph_ptr& aut)
    {
      return (!aut->is_existential())
             ? remove_fin(remove_alternation(aut))
             : nullptr;
    }

    twa_graph_ptr streett_strategy(const const_twa_graph_ptr& aut)
    {
      return (aut->get_acceptance().used_inf_fin_sets().first)
             ? streett_to_generalized_buchi_maybe(aut)
             : nullptr;
    }

    twa_graph_ptr rabin_strategy(const const_twa_graph_ptr& aut)
    {
      return rabin_to_buchi_maybe(aut);
    }

    twa_graph_ptr default_strategy(const const_twa_graph_ptr& aut)
    {
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
                    switch (pos->sub.op)
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
      res->prop_copy(aut, { true, false, false, false, false, true });
      res->new_states(nst);
      res->set_acceptance(aut->num_sets() + extra_sets, new_code);
      res->set_init_state(aut->get_init_state_number());

      // If the input had no Inf, the output is a state-based automaton.
      if (allinf == 0U)
        res->prop_state_acc(true);

      bool sbacc = res->prop_state_acc().is_true();
      scc_info si(aut, scc_info_options::TRACK_STATES);
      unsigned nscc = si.scc_count();
      std::vector<unsigned> state_map(nst);
      for (unsigned n = 0; n < nscc; ++n)
        {
          auto m = si.acc_sets_of(n);
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
          trace << "main_sets " << main_sets << "\nmain_add "
                << main_add << '\n';

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


      res->purge_dead_states();
      trace << "before cleanup: " << res->get_acceptance() << '\n';
      cleanup_acceptance_here(res);
      trace << "after cleanup: " << res->get_acceptance() << '\n';
      res->merge_edges();
      return res;
    }

    twa_graph_ptr remove_fin_impl(const const_twa_graph_ptr& aut,
                                  const strategy_t skip = {})
    {
      auto handle = [&](strategy stra, strategy_t type) -> twa_graph_ptr
      {
        return (type & skip) ? nullptr : stra(aut);
      };

      if (auto maybe = handle(trivial_strategy, strategy_t::trivial))
        return maybe;
      if (auto maybe = handle(weak_strategy, strategy_t::weak))
        return maybe;
      if (auto maybe = handle(alternation_strategy, strategy_t::alternation))
        return maybe;
      // The order between Rabin and Streett matters because for
      // instance "Streett 1" (even generalized Streett 1) is
      // Rabin-like, and dually "Rabin 1" is Streett-like.
      //
      // We therefore check Rabin before Streett, because the
      // resulting automata are usually smaller, and it can preserve
      // determinism.
      //
      // Note that SPOT_STREETT_CONV_MIN default to 3, which means
      // that regardless of this order, Rabin 1 is not handled by
      // streett_strategy unless SPOT_STREETT_CONV_MIN is changed.
      if (auto maybe = handle(rabin_strategy, strategy_t::rabin))
        return maybe;
      if (auto maybe = handle(streett_strategy, strategy_t::streett))
        return maybe;
      return default_strategy(aut);
    }
  }

  twa_graph_ptr
  rabin_to_buchi_maybe(const const_twa_graph_ptr& aut)
  {
    bool is_state_acc = aut->prop_state_acc().is_true();
    auto res = tra_to_tba(aut);
    if (res && is_state_acc)
      make_state_acc(res);
    return res;
  }

  twa_graph_ptr remove_fin(const const_twa_graph_ptr& aut)
  {
    return remove_fin_impl(aut);
  }
}
