// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2011, 2013, 2014, 2015, 2016, 2017 Laboratoire
// de Recherche et Développement de l'Epita (LRDE)
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

#include <spot/twaalgos/strength.hh>
#include <spot/misc/hash.hh>
#include <spot/twaalgos/isweakscc.hh>
#include <spot/twaalgos/mask.hh>

namespace spot
{
  namespace
  {
    template <bool terminal, bool inweak = false, bool set = false>
    bool is_type_automaton(const twa_graph_ptr& aut, scc_info* si,
                           bool ignore_trivial_term = false)
    {
      // Create an scc_info if the user did not give one to us.
      bool need_si = !si;
      if (need_si)
        si = new scc_info(aut);
      if (inweak)
        si->determine_unknown_acceptance();

      bool is_inweak = true;
      bool is_weak = true;
      bool is_single_state_scc = true;
      bool is_term = true;
      unsigned n = si->scc_count();
      for (unsigned i = 0; i < n; ++i)
        {
          if (si->is_trivial(i))
            continue;
          if (si->states_of(i).size() > 1)
            is_single_state_scc = false;
          bool first = true;
          acc_cond::mark_t m = 0U;
          if (is_weak)
            for (auto src: si->states_of(i))
              for (auto& t: aut->out(src))
                // In case of a universal edge we only need to check
                // the first destination of an inside the SCC, because
                // the other have the same t.acc.
                if (si->scc_of(*aut->univ_dests(t.dst).begin()) == i)
                  {
                    if (first)
                      {
                        first = false;
                        m = t.acc;
                      }
                    else if (m != t.acc)
                      {
                        is_weak = false;
                        if (!inweak)
                          goto exit;
                      }
                  }
          if (!is_weak && si->is_accepting_scc(i))
            {
              assert(inweak);
              if (scc_has_rejecting_cycle(*si, i))
                {
                  is_inweak = false;
                  break;
                }
            }
          if (terminal && si->is_accepting_scc(i) && !is_complete_scc(*si, i))
            {
              is_term = false;
              if (!set)
                break;
            }
        }
      // A terminal automaton should accept any word that as a prefix
      // leading to an accepting edge.  In other words, we cannot have
      // an accepting edge that goes into a rejecting SCC.
      if (terminal && is_term && !ignore_trivial_term)
        for (auto& e: aut->edges())
          if (si->is_rejecting_scc(si->scc_of(e.dst))
              && aut->acc().accepting(e.acc))
            {
              is_term = false;
              break;
            }
    exit:
      if (need_si)
        delete si;
      if (set)
        {
          if (terminal)
            {
              if (!ignore_trivial_term)
                aut->prop_terminal(is_term && is_weak);
              else if (is_term && is_weak)
                aut->prop_terminal(true);
            }
          aut->prop_weak(is_weak);
          aut->prop_very_weak(is_single_state_scc && is_weak);
          if (inweak)
            aut->prop_inherently_weak(is_inweak);
        }
      if (inweak)
        return is_inweak;
      return is_weak && is_term;
    }
  }

  bool
  is_terminal_automaton(const const_twa_graph_ptr& aut, scc_info* si,
                        bool ignore_trivial_term)
  {
    trival v = aut->prop_terminal();
    if (v.is_known())
      return v.is_true();
    bool res =
      is_type_automaton<true>(std::const_pointer_cast<twa_graph>(aut), si,
                              ignore_trivial_term);
    std::const_pointer_cast<twa_graph>(aut)->prop_terminal(res);
    return res;
  }

  bool
  is_weak_automaton(const const_twa_graph_ptr& aut, scc_info* si)
  {
    trival v = aut->prop_weak();
    if (v.is_known())
      return v.is_true();
    bool res =
      is_type_automaton<false>(std::const_pointer_cast<twa_graph>(aut), si);
    std::const_pointer_cast<twa_graph>(aut)->prop_weak(res);
    return res;
  }

  bool
  is_very_weak_automaton(const const_twa_graph_ptr& aut, scc_info* si)
  {
    trival v = aut->prop_very_weak();
    if (v.is_known())
      return v.is_true();
    is_type_automaton<false, false, true>
      (std::const_pointer_cast<twa_graph>(aut), si);
    return aut->prop_very_weak().is_true();
  }

  bool
  is_inherently_weak_automaton(const const_twa_graph_ptr& aut, scc_info* si)
  {
    trival v = aut->prop_inherently_weak();
    if (v.is_known())
      return v.is_true();
    bool res = is_type_automaton<false, true>
      (std::const_pointer_cast<twa_graph>(aut), si);
    std::const_pointer_cast<twa_graph>(aut)->prop_inherently_weak(res);
    return res;
  }

  void check_strength(const twa_graph_ptr& aut, scc_info* si)
  {
    if (!aut->is_existential())
      is_type_automaton<false, false, true>(aut, si);
    else
      is_type_automaton<true, true, true>(aut, si);
  }

  bool is_safety_automaton(const const_twa_graph_ptr& aut, scc_info* si)
  {
    if (aut->acc().is_t())
      return true;

    bool need_si = !si;
    if (need_si)
      si = new scc_info(aut);

    bool res = true;
    unsigned scount = si->scc_count();
    for (unsigned scc = 0; scc < scount; ++scc)
      if (!si->is_trivial(scc) && si->is_rejecting_scc(scc))
        {
          res = false;
          break;
        }

    if (need_si)
      delete si;
    return res;
  }


  twa_graph_ptr
  decompose_strength(const const_twa_graph_ptr& aut, const char* keep_opt)
  {
    if (keep_opt == nullptr || *keep_opt == 0)
      throw std::runtime_error
        (std::string("option for decompose_strength() should not be empty"));

    enum strength {
      Ignore = 0,
      Terminal = 1,
      WeakStrict = 2,
      Weak = Terminal | WeakStrict,
      Strong = 4,
      Needed = 8,                // Needed SCCs are those that lead to
                                // the SCCs we want to keep.
    };
    unsigned char keep = Ignore;
    while (auto c = *keep_opt++)
      switch (c)
        {
        case 's':
          keep |= Strong;
          break;
        case 't':
          keep |= Terminal;
          break;
        case 'w':
          keep |= WeakStrict;
          break;
        default:
          throw std::runtime_error
            (std::string("unknown option for decompose_strength(): ") + c);
        }

    auto p = aut->acc().unsat_mark();
    bool all_accepting = !p.first;
    acc_cond::mark_t wacc = 0U;        // Acceptance for weak SCCs
    acc_cond::mark_t uacc = p.second; // Acceptance for "needed" SCCs, that
                                      // we only want to traverse.

    // If the acceptance condition is always satisfiable, we will
    // consider the automaton as weak (even if that is not the
    // case syntactically) and not output any strong part.
    if (all_accepting)
      {
        keep &= ~Strong;
        if (keep == Ignore)
          return nullptr;
      }

    scc_info si(aut);
    si.determine_unknown_acceptance();

    unsigned n = si.scc_count();
    std::vector<unsigned char> want(n, Ignore);
    bool nonempty = false;
    bool strong_seen = false;

    for (unsigned i = 0; i < n; ++i) // SCC are topologically ordered
      {
        if (si.is_accepting_scc(i))
          {
            if (all_accepting | is_inherently_weak_scc(si, i))
              {
                if (keep & Weak)
                  {
                    if ((keep & Weak) == Weak)
                      want[i] = Weak;
                    else
                      want[i] = keep &
                        (is_complete_scc(si, i) ? Terminal : WeakStrict);
                  }
              }
            else
              {
                want[i] = keep & Strong;
                strong_seen = true;
              }
            nonempty |= want[i];
          }
        // An SCC is needed if one of its successor is.
        for (unsigned j: si.succ(i))
          if (want[j])
            {
              want[i] |= Needed;
              break;
            }
      }

    if (!nonempty)
      return nullptr;

    twa_graph_ptr res = make_twa_graph(aut->get_dict());
    res->copy_ap_of(aut);
    res->prop_copy(aut, { true, false, false, true, false, false });

    if (keep & Strong)
      res->copy_acceptance_of(aut);
    else
      wacc = res->set_buchi();

    auto fun = [&si, &want, uacc, wacc, keep]
      (unsigned src, bdd& cond, acc_cond::mark_t& acc, unsigned dst)
      {
        if (want[si.scc_of(dst)] == Ignore)
          {
            cond = bddfalse;
            return;
          }
        if (want[si.scc_of(src)] == Needed)
          {
            acc = uacc;
            return;
          }
        if (keep & Strong)
          return;
        acc = wacc;
      };

    transform_accessible(aut, res, fun);

    if (!(keep & Strong))
      {
        res->prop_weak(true);
        if (!(keep & WeakStrict))
          {
            assert(keep & Terminal);
            res->prop_terminal(true);
          }
      }
    else
      {
        res->prop_weak(!strong_seen);
      }
    return res;
  }

  twa_graph_ptr
  decompose_scc(scc_info& sm, unsigned scc_num)
  {
    unsigned n = sm.scc_count();

    if (n <= scc_num)
      throw std::invalid_argument
        (std::string("decompose_scc(): requested SCC index is out of bounds"));

    std::vector<bool> want(n, false);
    want[scc_num] = true;

    // mark all the SCCs that can reach scc_num as wanted
    for (unsigned i = scc_num + 1; i < n; ++i)
      for (unsigned succ : sm.succ(i))
        if (want[succ])
          {
            want[i] = true;
            break;
          }

    const_twa_graph_ptr aut = sm.get_aut();
    twa_graph_ptr res = make_twa_graph(aut->get_dict());
    res->copy_ap_of(aut);
    res->prop_copy(aut, { true, false, false, true, false, false });
    res->copy_acceptance_of(aut);

    auto um = aut->acc().unsat_mark();

    // If aut has an unsatisfying mark, we are going to use it to remove the
    // acceptance of some transitions. If it doesn't, we make res a rejecting
    // Büchi automaton, and get back an accepting mark that we are going to set
    // on the transitions of the SCC we selected.
    auto new_mark = um.first ? um.second : res->set_buchi();
    auto fun = [sm, &want, um, new_mark, scc_num]
      (unsigned src, bdd& cond, acc_cond::mark_t& acc, unsigned dst)
      {
        if (!want[sm.scc_of(dst)])
          {
            cond = bddfalse;
            return;
          }
        // no need to check if src is wanted, we already know dst is.
        // if res is accepting, make only the upstream SCCs rejecting
        // if res is rejecting, make only the requested SCC accepting
        if (um.first != (sm.scc_of(src) == scc_num))
          acc = new_mark;
      };

    transform_accessible(aut, res, fun);

    return res;
  }

  twa_graph_ptr
  decompose_acc_scc(const const_twa_graph_ptr& aut, int scc_index)
  {
    scc_info si(aut);
    unsigned scc_num = 0;

    for (; scc_num < si.scc_count(); ++scc_num)
      {
        if (si.is_accepting_scc(scc_num))
          {
            if (!scc_index)
              break;
            --scc_index;
          }
      }

    return decompose_scc(si, scc_num);
  }
}
