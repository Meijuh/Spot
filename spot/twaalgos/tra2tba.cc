// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement
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

#include <spot/twa/acc.hh>
#include <spot/twaalgos/tra2tba.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/mask.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twa/formula2bdd.hh>

namespace spot
{
  namespace
  {
    std::vector<unsigned> scc_edges(const const_twa_graph_ptr& aut,
                                    const scc_info& si,
                                    const unsigned scc)
    {
      std::vector<unsigned> edges;
      for (unsigned s : si.states_of(scc))
        for (const auto& t: aut->succ(aut->state_from_number(s)))
          edges.push_back(aut->edge_number(t));
      return edges;

    }
    //
    std::vector<unsigned> scc_inner_edges(const const_twa_graph_ptr& aut,
                                          const scc_info& si,
                                          const unsigned scc)
    {
      auto edges = scc_edges(aut, si, scc);
      edges.erase(std::remove_if(edges.begin(), edges.end(),
        [&](unsigned e)
        {
          return si.scc_of(aut->edge_storage(e).dst) != scc;
        }),
        edges.end());
      return edges;
    }

    twa_graph_ptr mask_keep_edges(const const_twa_graph_ptr& aut,
                                  std::vector<bool>& to_keep,
                                  unsigned int init)
    {
      if (to_keep.size() < aut->edge_vector().size())
        to_keep.resize(aut->edge_vector().size(), false);

      auto res = make_twa_graph(aut->get_dict());
      res->copy_ap_of(aut);
      res->prop_copy(aut, { false, true, false, true, false, false });
      res->copy_acceptance_of(aut);

      size_t states = aut->num_states();
      std::vector<std::vector<bool>> edges;
      edges.resize(states);
      for (size_t i = 0; i < states; ++i)
        edges[i].resize(states, false);

      for (size_t i = 0; i < aut->edge_vector().size(); ++i)
        {
          if (to_keep[i])
            {
              const auto& es = aut->edge_storage(i);
              edges[es.src][es.dst] = true;
            }
        }

      transform_copy(aut, res,
                     [&](unsigned src, bdd& cond, acc_cond::mark_t&,
                         unsigned dst)
                     {
                       if (!edges[src][dst])
                         cond = bddfalse;
                     },
                     init);
      return res;
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
    bool is_scc_tba_type(const const_twa_graph_ptr& aut,
                         const scc_info& si,
                         const unsigned scc,
                         const acc_cond::mark_t fin_alone,
                         std::vector<bool>& final)
    {
      if (si.is_rejecting_scc(scc))
        return true;

      auto acc_pairs = aut->get_acceptance().used_inf_fin_sets();
      auto infs = si.acc(scc) & acc_pairs.first;
      auto fins = si.acc(scc) & acc_pairs.second;
      auto infs_with_fins = (si.acc(scc) << 1U) & acc_pairs.first;
      infs -= infs_with_fins;

      // If there is one fin_alone that is not in the SCC,
      // any cycle in the SCC is accepting.
      if ((fins & fin_alone) != fin_alone)
        {
          for (auto e: scc_edges(aut, si, scc))
            final[e] = true;
          return true;
        }
      auto& states = si.states_of(scc);
      // Firstly consider whole SCC as one large cycle.
      // If there is no inf without matching fin then the cycle formed
      // by the entire SCC is not accepting.  However that does not
      // necessarily imply that all cycles in the SCC are also
      // non-accepting.  We may have a smaller cycle that is
      // accepting, but which becomes non-accepting when extended with
      // more states.
      if (!infs)
        {
          // Check whether the SCC is accepting.  We do that by simply
          // converting that SCC into a TGBA and running our emptiness
          // check.  This is not a really smart implementation and
          // could be improved.
          std::vector<bool> keep(aut->num_states(), false);
          for (auto s: states)
            keep[s] = true;
          auto sccaut = mask_keep_accessible_states(aut,
                                                    keep,
                                                    states.front());
          sccaut->prop_state_acc(false);
          return sccaut->is_empty();
        }

      // Remaining infs corresponds to I₁s that have been seen with seeing
      // the mathing F₁. In this SCC any edge in these I₁ is therefore
      // final. Otherwise we do not know: it is possible that there is
      // a non-accepting cycle in the SCC that do not visit Fᵢ.
      std::set<unsigned> unknown;
      for (auto e: scc_inner_edges(aut, si, scc))
        if (aut->edge_data(e).acc & infs)
          final[e] = true;
        else
          unknown.insert(e);
      // Check whether it is possible to build non-accepting cycles
      // using only the "unknown" edges.
      std::vector<bool> keep(aut->edge_vector().size(), false);
      for (auto e: unknown)
        keep[e] = true;

      while (!unknown.empty())
        {
          unsigned init = aut->edge_storage(*unknown.begin()).src;
          scc_info si(mask_keep_edges(aut, keep, init));
          unsigned scc_max = si.scc_count();
          for (unsigned uscc = 0; uscc < scc_max; ++uscc)
            {
              for (auto e: scc_edges(aut, si, uscc))
                {
                  unknown.erase(e);
                  keep[e] = false;
                }
              if (si.is_rejecting_scc(uscc))
                continue;
              if (!is_scc_tba_type(aut, si, uscc, fin_alone, final))
                return false;
            }
        }
      return true;
    }
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
  tra_to_tba(const const_twa_graph_ptr& aut)
  {
    if (aut->prop_state_acc().is_true())
      return nullptr;

    std::vector<acc_cond::rs_pair> pairs;
    if (!aut->acc().is_rabin_like(pairs))
      return nullptr;

    auto code = aut->get_acceptance();
    if (code.is_t())
      return nullptr;

    // if is TBA type
    scc_info si{aut};
    std::vector<bool> scc_is_tba_type(si.scc_count(), false);
    std::vector<bool> final(aut->edge_vector().size(), false);

    acc_cond::mark_t inf_alone = 0U;
    acc_cond::mark_t fin_alone = 0U;
    for (const auto& p: pairs)
      if (!p.fin)
        inf_alone &= p.inf;
      else if (!p.inf)
        fin_alone &= p.fin;

    for (unsigned scc = 0; scc < si.scc_count(); ++scc)
      {
        scc_is_tba_type[scc] = is_scc_tba_type(aut, si, scc, fin_alone, final);
      }
    // compute final edges
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
            for (unsigned e: scc_edges(aut, si, scc))
              {
                const auto& ed = aut->edge_data(e);
                const auto& es = aut->edge_storage(e);
                bool acc = final[e];
                res->new_acc_edge(es.src, es.dst, ed.cond, acc);
              }
          }
        else
          {
            deterministic = false;
            complete = trival::maybe();

            auto acc_pairs = aut->get_acceptance().used_inf_fin_sets();
            auto infs = si.acc(scc) & acc_pairs.first;
            auto infs_with_fins = (si.acc(scc) << 1U) & acc_pairs.first;
            infs -= infs_with_fins;

            for (auto e: scc_edges(aut, si, scc))
              {
                const auto& ed = aut->edge_data(e);
                const auto& es = aut->edge_storage(e);
                bool acc{ ed.acc & infs };
                res->new_acc_edge(es.src, es.dst, ed.cond, acc);
              }

            auto rem = si.acc(scc) & acc_pairs.second;
            assert(rem != 0U);
            for (auto r: rem.sets())
              {
                unsigned base = res->new_states(states.size());
                for (auto s: states)
                    state_map[s] = base++;
                for (auto e: scc_inner_edges(aut, si, scc))
                  {
                    const auto& ed = aut->edge_data(e);
                    const auto& es = aut->edge_storage(e);
                    if (ed.acc.has(r))
                      continue;
                    auto src = state_map[es.src];
                    auto dst = state_map[es.dst];
                    res->new_acc_edge(src, dst, ed.cond, ed.acc.has(r + 1));
                    // We need only one non-deterministic jump per
                    // cycle.  As an approximation, we only do
                    // them on back-links.
                    bool jacc{ed.acc & inf_alone};
                    if (es.dst <= es.src)
                      res->new_acc_edge(es.src, dst, ed.cond, jacc);
                  }
              }
          }
      }
    res->prop_complete(complete);
    res->prop_universal(deterministic);
    res->purge_dead_states();
    return res;
  }

}
