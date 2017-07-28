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


namespace spot
{
  bool
  is_recurrence(formula f, const twa_graph_ptr& aut)
  {
    if (f.is_syntactic_recurrence() || is_universal(aut))
      return true;
    // If aut is a non-deterministic TGBA, we do
    // TGBA->DPA->DRA->(D?)BA.  The conversion from DRA to
    // BA will preserve determinism if possible.
    spot::postprocessor p;
    p.set_type(spot::postprocessor::Generic);
    p.set_pref(spot::postprocessor::Deterministic
               | spot::postprocessor::SBAcc);
    p.set_level(spot::postprocessor::Low);
    auto dra = p.run(aut);
    if (dra->acc().is_generalized_buchi())
      {
        return true;
      }
    else
      {
        auto ba = rabin_to_buchi_maybe(to_generalized_rabin(dra));
        assert(ba);
        return is_deterministic(ba);
      }
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
    f = formula::Not(f);
    aut = ltl_to_tgba_fm(f, dict, true);
    if (is_recurrence(f, aut))
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
