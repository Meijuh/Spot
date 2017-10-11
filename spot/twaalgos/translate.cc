// -*- coding: utf-8 -*-
// Copyright (C) 2013-2017 Laboratoire de Recherche et Développement
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

#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/compsusp.hh>
#include <spot/misc/optionmap.hh>
#include <spot/tl/relabel.hh>
#include <spot/twaalgos/relabel.hh>

namespace spot
{

  void translator::setup_opt(const option_map* opt)
  {
    comp_susp_ = early_susp_ = skel_wdba_ = skel_simul_ = 0;
    relabel_bool_ = tls_impl_ = -1;

    if (!opt)
      return;

    relabel_bool_ = opt->get("relabel-bool", 4);
    comp_susp_ = opt->get("comp-susp", 0);
    if (comp_susp_ == 1)
      {
        early_susp_ = opt->get("early-susp", 0);
        skel_wdba_ = opt->get("skel-wdba", -1);
        skel_simul_ = opt->get("skel-simul", 1);
      }
    tls_impl_ = opt->get("tls-impl", -1);
  }

  void translator::build_simplifier(const bdd_dict_ptr& dict)
  {
    tl_simplifier_options options(false, false, false);
    switch (level_)
      {
      case High:
        options.containment_checks = true;
        options.containment_checks_stronger = true;
        SPOT_FALLTHROUGH;
      case Medium:
        options.synt_impl = true;
        SPOT_FALLTHROUGH;
      case Low:
        options.reduce_basics = true;
        options.event_univ = true;
      }
    // User-supplied fine-tuning?
    if (tls_impl_ >= 0)
      switch (tls_impl_)
        {
        case 0:
          options.synt_impl = false;
          options.containment_checks = false;
          options.containment_checks_stronger = false;
          break;
        case 1:
          options.synt_impl = true;
          options.containment_checks = false;
          options.containment_checks_stronger = false;
          break;
        case 2:
          options.synt_impl = true;
          options.containment_checks = true;
          options.containment_checks_stronger = false;
          break;
        case 3:
          options.synt_impl = true;
          options.containment_checks = true;
          options.containment_checks_stronger = true;
          break;
        default:
          throw std::runtime_error
            ("tls-impl should take a value between 0 and 3");
        }
    simpl_owned_ = simpl_ = new tl_simplifier(options, dict);
  }

  twa_graph_ptr translator::run(formula* f)
  {
    bool unambiguous = (pref_ & postprocessor::Unambiguous);
    if (unambiguous && type_ == postprocessor::Monitor)
      {
        // Deterministic monitor are unambiguous, so the unambiguous
        // option is not really relevant for monitors.
        unambiguous = false;
        set_pref(pref_ | postprocessor::Deterministic);
      }

    // Do we want to relabel Boolean subformulas?
    // If we have a huge formula such as
    //  (a1 & a2 & ... & an) U (b1 | b2 | ... | bm)
    // then it is more efficient to translate
    //  a U b
    // and then fix the automaton.  We use relabel_bse() to find
    // sub-formulas that are Boolean but do not have common terms.
    //
    // This rewriting is enabled only if the formula
    //  1) has some Boolean subformula
    //  2) has more than relabel_bool_ atomic propositions (the default
    //     is 4, but this can be changed)
    //  3) relabel_bse() actually reduces the number of atomic
    //     propositions.
    relabeling_map m;
    formula to_work_on = *f;
    if (relabel_bool_ > 0)
      {
        bool has_boolean_sub = false; // that is not atomic
        std::set<formula> aps;
        to_work_on.traverse([&](const formula& f)
                            {
                              if (f.is(op::ap))
                                aps.insert(f);
                              else if (f.is_boolean())
                                has_boolean_sub = true;
                              return false;
                            });
        unsigned atomic_props = aps.size();
        if (has_boolean_sub && (atomic_props >= (unsigned) relabel_bool_))
          {
            formula relabeled = relabel_bse(to_work_on, Pnn, &m);
            if (m.size() < atomic_props)
              to_work_on = relabeled;
            else
              m.clear();
          }
      }

    formula r = simpl_->simplify(to_work_on);
    if (to_work_on == *f)
      *f = r;

    // This helps ltl_to_tgba_fm() to order BDD variables in a more
    // natural way (improving the degeneralization).
    simpl_->clear_as_bdd_cache();

    twa_graph_ptr aut;
    if (comp_susp_ > 0)
      {
        // FIXME: Handle unambiguous_ automata?
        int skel_wdba = skel_wdba_;
        if (skel_wdba < 0)
          skel_wdba = (pref_ == postprocessor::Deterministic) ? 1 : 2;

        aut = compsusp(r, simpl_->get_dict(), skel_wdba == 0,
                       skel_simul_ == 0, early_susp_ != 0,
                       comp_susp_ == 2, skel_wdba == 2, false);
      }
    else
      {
        bool exprop = unambiguous || level_ == postprocessor::High;
        aut = ltl_to_tgba_fm(r, simpl_->get_dict(), exprop,
                             true, false, false, nullptr, nullptr,
                             unambiguous);
      }

    aut = this->postprocessor::run(aut, r);

    if (!m.empty())
      relabel_here(aut, &m);
    return aut;
  }

  twa_graph_ptr translator::run(formula f)
  {
    return run(&f);
  }

  void translator::clear_caches()
  {
    simpl_->clear_caches();
  }

}
