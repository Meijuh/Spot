// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2017 Laboratoire de Recherche et Développement
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

#include <spot/twaalgos/cleanacc.hh>

namespace spot
{
  twa_graph_ptr cleanup_acceptance_here(twa_graph_ptr aut, bool strip)
  {
    auto& acc = aut->acc();
    if (acc.num_sets() == 0)
      return aut;

    auto c = aut->get_acceptance();
    acc_cond::mark_t used_in_cond = c.used_sets();

    acc_cond::mark_t used_in_aut = 0U;
    acc_cond::mark_t used_on_all_edges = used_in_cond;
    for (auto& t: aut->edges())
      {
        used_in_aut |= t.acc;
        used_on_all_edges &= t.acc;
      }

    auto useful = used_in_aut & used_in_cond;
    auto useless = strip ? acc.comp(useful) : (used_in_cond - used_in_aut);

    useless |= used_on_all_edges;

    if (!useless)
      return aut;

    // Remove useless marks from the automaton
    if (strip)
      for (auto& t: aut->edges())
        t.acc = t.acc.strip(useless);

    // if x appears on all edges, then
    //   Fin(x) = false and Inf(x) = true
    if (used_on_all_edges)
      c = c.remove(used_on_all_edges, false);

    // Remove useless marks from the acceptance condition
    if (strip)
      aut->set_acceptance(useful.count(), c.strip(useless, true));
    else
      aut->set_acceptance(aut->num_sets(), c.remove(useless, true));

    // This may in turn cause even more set to be unused, because of
    // some simplifications in the acceptance condition, so do it again.
    return cleanup_acceptance_here(aut, strip);
  }

  twa_graph_ptr cleanup_acceptance(const_twa_graph_ptr aut)
  {
    return cleanup_acceptance_here(make_twa_graph(aut,
                                                     twa::prop_set::all()));
  }

  namespace
  {
    twa_graph_ptr merge_identical_marks_here(twa_graph_ptr aut)
    {
      // always cleanup before proceeding, otherwise if some mark appears in the
      // acceptance condition, but not in the automaton the result is undefined.
      cleanup_acceptance_here(aut, false);

      auto& acc = aut->acc();
      auto& c = acc.get_acceptance();
      acc_cond::mark_t used_in_cond = c.used_sets();

      if (!used_in_cond)
        return aut;

      unsigned num_sets = acc.num_sets();
      std::vector<acc_cond::mark_t> always_together(num_sets);

      for (unsigned i = 0; i < num_sets; ++i)
        if (used_in_cond.has(i))
          always_together[i] = used_in_cond;
        else
          always_together[i] = acc_cond::mark_t({i});

      acc_cond::mark_t previous_a = 0U;
      for (auto& t: aut->edges())
        {
          acc_cond::mark_t a = t.acc & used_in_cond;
          if (a == previous_a)
            continue;
          previous_a = a;
          for (unsigned m: a.sets())
            {
              acc_cond::mark_t at = always_together[m];
              acc_cond::mark_t newm = at & a;

              for (unsigned rem: (at - newm).sets())
                always_together[rem] -= newm;

              always_together[m] = newm;
            }
        }

      acc_cond::mark_t to_remove = 0U;
      for (unsigned i = 0; i < num_sets; ++i)
        {
          auto oldm = always_together[i];
          if (oldm == acc_cond::mark_t({i}))
            continue;

          acc_cond::mark_t newm = oldm.lowest();
          to_remove |= oldm - newm;
          always_together[i] = newm;
        }
      for (auto& t: aut->edges())
        t.acc -= to_remove;

      // Replace the marks in the acceptance condition
      auto pos = &c.back();
      auto end = &c.front();
      while (pos > end)
        {
          switch (pos->sub.op)
            {
            case acc_cond::acc_op::And:
            case acc_cond::acc_op::Or:
              --pos;
              break;
            case acc_cond::acc_op::Fin:
            case acc_cond::acc_op::Inf:
            case acc_cond::acc_op::FinNeg:
            case acc_cond::acc_op::InfNeg:
              acc_cond::mark_t replace = pos[-1].mark & to_remove;
              pos[-1].mark -= replace;
              for (unsigned m: replace.sets())
                pos[-1].mark |= always_together[m];
              pos -= 2;
              break;
            }
        }
      return aut;
    }

    // Eventually remove complementary marks from the acceptance condition.
    acc_cond::acc_code remove_compl_rec(const acc_cond::acc_word* pos,
                                        const std::vector<acc_cond::mark_t>&
                                                          complement)
    {
      auto start = pos - pos->sub.size;
      switch (pos->sub.op)
        {
          case acc_cond::acc_op::And:
            {
              --pos;
              auto res = acc_cond::acc_code::t();
              acc_cond::mark_t seen_fin = 0U;
              auto inf = acc_cond::acc_code::inf(0U);
              do
                {
                  auto tmp = remove_compl_rec(pos, complement);

                  if (!tmp.empty())
                    {
                      if (tmp.back().sub.op == acc_cond::acc_op::Fin
                          && tmp.front().mark.count() == 1)
                        seen_fin |= tmp.front().mark;

                      if (tmp.back().sub.op == acc_cond::acc_op::Inf)
                        {
                          inf &= std::move(tmp);
                          pos -= pos->sub.size + 1;
                          continue;
                        }
                    }
                  tmp &= std::move(res);
                  std::swap(tmp, res);
                  pos -= pos->sub.size + 1;
                }
              while (pos > start);

              // Fin(i) & Inf(i) = f;
              if (inf.front().mark & seen_fin)
                return acc_cond::acc_code::f();
              for (auto m: seen_fin.sets())
                {
                  acc_cond::mark_t cm = complement[m];
                  // Fin(i) & Fin(!i) = f;
                  if (cm & seen_fin)
                    return acc_cond::acc_code::f();
                  // Inf({!i}) & Fin({i}) = Fin({i})
                  inf.front().mark -= complement[m];
                }

              return inf & res;
            }
          case acc_cond::acc_op::Or:
            {
              --pos;
              auto res = acc_cond::acc_code::f();
              acc_cond::mark_t seen_inf = 0U;
              auto fin = acc_cond::acc_code::f();
              do
                {
                  auto tmp = remove_compl_rec(pos, complement);

                  if (!tmp.empty())
                    {
                      if (tmp.back().sub.op == acc_cond::acc_op::Inf
                          && tmp.front().mark.count() == 1)
                        seen_inf |= tmp.front().mark;

                      if (tmp.back().sub.op == acc_cond::acc_op::Fin)
                        {
                          fin |= std::move(tmp);
                          pos -= pos->sub.size + 1;
                          continue;
                        }
                    }
                  tmp |= std::move(res);
                  std::swap(tmp, res);
                  pos -= pos->sub.size + 1;
                }
              while (pos > start);

              // Fin(i) | Inf(i) = t;
              if (fin.front().mark & seen_inf)
                return acc_cond::acc_code::t();
              for (auto m: seen_inf.sets())
                {
                  acc_cond::mark_t cm = complement[m];
                  // Inf({i}) | Inf({!i}) = t;
                  if (cm & seen_inf)
                    return acc_cond::acc_code::t();
                  // Fin({!i}) | Inf({i}) = Inf({i})
                  fin.front().mark -= complement[m];
                }
              return res | fin;
            }
          case acc_cond::acc_op::Fin:
            return acc_cond::acc_code::fin(pos[-1].mark);
          case acc_cond::acc_op::Inf:
            return acc_cond::acc_code::inf(pos[-1].mark);
          case acc_cond::acc_op::FinNeg:
          case acc_cond::acc_op::InfNeg:
            SPOT_UNREACHABLE();
        };
        SPOT_UNREACHABLE();
        return {};
    }

    // Always cleanup_acceptance_here with stripping after calling this function
    // As complementary marks might be simplified in the acceptance condition.
    twa_graph_ptr simplify_complementary_marks_here(twa_graph_ptr aut)
    {
      auto& acc = aut->acc();
      auto c = acc.get_acceptance();
      acc_cond::mark_t used_in_cond = c.used_sets();
      if (!used_in_cond)
        return aut;

      unsigned num_sets = acc.num_sets();
      std::vector<acc_cond::mark_t> complement(num_sets);


      for (unsigned i = 0; i < num_sets; ++i)
        if (used_in_cond.has(i))
          complement[i] = used_in_cond - acc_cond::mark_t({i});

      acc_cond::mark_t previous_a = 0U;
      for (auto& t: aut->edges())
        {
          if (t.acc == previous_a)
            continue;
          previous_a = t.acc;
          for (unsigned m: used_in_cond.sets())
            {
              if (t.acc.has(m))
                complement[m] -= t.acc;
              else
                complement[m] &= t.acc;
            }
        }
      aut->set_acceptance(num_sets,
                          remove_compl_rec(&acc.get_acceptance().back(),
                                           complement));
      return aut;
    }
  }

  twa_graph_ptr simplify_acceptance_here(twa_graph_ptr aut)
  {
    cleanup_acceptance_here(aut, false);
    merge_identical_marks_here(aut);
    simplify_complementary_marks_here(aut);
    cleanup_acceptance_here(aut, true);

    return aut;
  }

  twa_graph_ptr simplify_acceptance(const_twa_graph_ptr aut)
  {
    return simplify_acceptance_here(make_twa_graph(aut, twa::prop_set::all()));
  }
}
