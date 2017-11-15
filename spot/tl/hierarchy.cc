// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement de
// l'Epita (LRDE)
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

#include <sstream>
#include <spot/tl/hierarchy.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/strength.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/twaalgos/cobuchi.hh>


namespace spot
{
  namespace
  {
    static bool
    cobuchi_realizable(spot::formula f,
                       const const_twa_graph_ptr& aut)
    {
      twa_graph_ptr cobuchi = nullptr;
      std::vector<acc_cond::rs_pair> pairs;
      if (aut->acc().is_streett_like(pairs) || aut->acc().is_parity())
        cobuchi = nsa_to_dca(aut, false);
      else if (aut->get_acceptance().is_dnf())
        cobuchi = dnf_to_dca(aut, false);
      else
        throw std::runtime_error("cobuchi_realizable() only works with "
                                 "Streett-like, Parity or any "
                                 "acceptance condition in DNF");

      return !cobuchi->intersects(ltl_to_tgba_fm(formula::Not(f),
                                                 cobuchi->get_dict(),
                                                 true));
    }

    static bool
    detbuchi_realizable(const twa_graph_ptr& aut)
    {
      if (is_universal(aut))
        return true;

      // if aut is a non-deterministic TGBA, we do
      // TGBA->DPA->DRA->(D?)BA.  The conversion from DRA to
      // BA will preserve determinism if possible.
      spot::postprocessor p;
      p.set_type(spot::postprocessor::Generic);
      p.set_pref(spot::postprocessor::Deterministic);
      p.set_level(spot::postprocessor::Low);
      auto dra = p.run(aut);
      if (dra->acc().is_generalized_buchi())
        {
          assert(is_deterministic(dra));
          return true;
        }
      else
        {
          auto ba = rabin_to_buchi_maybe(to_generalized_rabin(dra));
          assert(ba);
          return is_deterministic(ba);
        }
    }
  }

  static prcheck
  algo_to_perform(bool is_persistence, bool aut_given, prcheck algo)
  {
    if (algo == prcheck::PR_Auto)
      {
        // Check environment variable.
        static int val_s = []()
          {
            try
              {
                auto s = getenv("SPOT_PR_CHECK");
                return s ? std::stoi(s) : 0;
              }
            catch (const std::exception& e)
              {
                throw std::runtime_error("invalid value for SPOT_PR_CHECK "
                                         "(should be 1 or 2)");
              }
          }();

        if (val_s == 1)
          {
            return prcheck::PR_via_CoBuchi;
          }
        else if (val_s == 2)
          {
            return prcheck::PR_via_Rabin;
          }
        else if (!val_s)
          {
            if (aut_given && !is_persistence)
              return prcheck::PR_via_Rabin;
            else if ((aut_given && is_persistence) || !aut_given)
              return prcheck::PR_via_CoBuchi;
            else
              SPOT_UNREACHABLE();
          }
        else
          {
            throw std::runtime_error("invalid value for SPOT_PR_CHECK "
                                     "(should be 1 or 2)");
          }
      }
    else
      return algo;
  }

  bool
  is_persistence(formula f, twa_graph_ptr aut, prcheck algo)
  {
    if (f.is_syntactic_persistence())
      return true;

    switch (algo_to_perform(true, aut != nullptr, algo))
      {
      case prcheck::PR_via_CoBuchi:
        return cobuchi_realizable(f, aut ? aut :
                                  ltl_to_tgba_fm(f, make_bdd_dict(), true));

      case prcheck::PR_via_Rabin:
        return detbuchi_realizable(ltl_to_tgba_fm(formula::Not(f),
                                                  make_bdd_dict(), true));

      case prcheck::PR_Auto:
        SPOT_UNREACHABLE();
      }

    SPOT_UNREACHABLE();
  }

  bool
  is_recurrence(formula f, twa_graph_ptr aut, prcheck algo)
  {
    if (f.is_syntactic_recurrence())
      return true;

    switch (algo_to_perform(false, aut != nullptr, algo))
      {
      case prcheck::PR_via_CoBuchi:
        return cobuchi_realizable(formula::Not(f),
                                  ltl_to_tgba_fm(formula::Not(f),
                                                 make_bdd_dict(), true));

      case prcheck::PR_via_Rabin:
        return detbuchi_realizable(aut ? aut :
                                   ltl_to_tgba_fm(f, make_bdd_dict(), true));

      case prcheck::PR_Auto:
        SPOT_UNREACHABLE();
      }

    SPOT_UNREACHABLE();
  }


  [[noreturn]] static void invalid_spot_o_check()
  {
    throw std::runtime_error("invalid value for SPOT_O_CHECK "
                             "(should be 1, 2, or 3)");
  }

  // This private function is defined in minimize.cc for technical
  // reasons.
  SPOT_LOCAL bool is_wdba_realizable(formula f, twa_graph_ptr aut = nullptr);

  bool
  is_obligation(formula f, twa_graph_ptr aut, ocheck algo)
  {
    if (algo == ocheck::Auto)
      {
        static ocheck env_algo = []()
          {
            int val;
            try
              {
                auto s = getenv("SPOT_O_CHECK");
                val = s ? std::stoi(s) : 0;
              }
            catch (const std::exception& e)
              {
                invalid_spot_o_check();
              }
            if (val == 0)
              return ocheck::via_WDBA;
            else if (val == 1)
              return ocheck::via_CoBuchi;
            else if (val == 2)
              return ocheck::via_Rabin;
            else if (val == 3)
              return ocheck::via_WDBA;
            else
              invalid_spot_o_check();
          }();
        algo = env_algo;
      }
    switch (algo)
      {
      case ocheck::via_WDBA:
        return is_wdba_realizable(f, aut);
      case ocheck::via_CoBuchi:
        return (is_persistence(f, aut, prcheck::PR_via_CoBuchi)
                && is_recurrence(f, aut, prcheck::PR_via_CoBuchi));
      case ocheck::via_Rabin:
        return (is_persistence(f, aut, prcheck::PR_via_Rabin)
                && is_recurrence(f, aut, prcheck::PR_via_Rabin));
      case ocheck::Auto:
        SPOT_UNREACHABLE();
      }
    SPOT_UNREACHABLE();
  }


  char mp_class(formula f)
  {
    if (f.is_syntactic_safety() && f.is_syntactic_guarantee())
      return 'B';
    auto dict = make_bdd_dict();
    auto aut = ltl_to_tgba_fm(f, dict, true);
    auto min = minimize_obligation(aut, f);
    if (aut != min) // An obligation.
      {
        scc_info si(min);
        // The minimba WDBA can have some trivial accepting SCCs
        // that we should ignore in is_terminal_automaton().
        bool g = is_terminal_automaton(min, &si, true);
        bool s = is_safety_automaton(min, &si);
        if (g)
          return s ? 'B' : 'G';
        else
          return s ? 'S' : 'O';
      }
    // Not an obligation.  Could by 'P', 'R', or 'T'.
    if (is_recurrence(f, aut))
      return 'R';
    if (is_persistence(f, aut))
      return 'P';
    return 'T';
  }

  std::string mp_class(formula f, const char* opt)
  {
    return mp_class(mp_class(f), opt);
  }

  std::string mp_class(char mpc, const char* opt)
  {
    bool verbose = false;
    bool wide = false;
    if (opt)
      for (;;)
        switch (int o = *opt++)
          {
          case 'v':
            verbose = true;
            break;
          case 'w':
            wide = true;
            break;
          case ' ':
          case '\t':
          case '\n':
          case ',':
            break;
          case '\0':
          case ']':
            goto break2;
          default:
            {
              std::ostringstream err;
              err << "unknown option '" << o << "' for mp_class()";
              throw std::runtime_error(err.str());
            }
          }
  break2:
    std::string c(1, mpc);
    if (wide)
      {
        switch (mpc)
          {
          case 'B':
            c = "GSOPRT";
            break;
          case 'G':
            c = "GOPRT";
            break;
          case 'S':
            c = "SOPRT";
            break;
          case 'O':
            c = "OPRT";
            break;
          case 'P':
            c = "PT";
            break;
          case 'R':
            c = "RT";
            break;
          case 'T':
            break;
          default:
            throw std::runtime_error("mp_class() called with unknown class");
          }
      }
    if (!verbose)
      return c;

    std::ostringstream os;
    bool first = true;
    for (char ch: c)
      {
        if (first)
          first = false;
        else
          os << ' ';
        switch (ch)
          {
          case 'B':
            os << "guarantee safety";
            break;
          case 'G':
            os << "guarantee";
            break;
          case 'S':
            os << "safety";
            break;
          case 'O':
            os << "obligation";
            break;
          case 'P':
            os << "persistence";
            break;
          case 'R':
            os << "recurrence";
            break;
          case 'T':
            os << "reactivity";
            break;
          }
      }
    return os.str();
  }

}
