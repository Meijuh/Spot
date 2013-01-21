// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013 Laboratoire de Recherche et Développement
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

#include "postproc.hh"
#include "minimize.hh"
#include "simulation.hh"
#include "sccfilter.hh"
#include "degen.hh"
#include "stripacc.hh"
#include <cstdlib>
#include "misc/optionmap.hh"
#include "priv/countstates.hh"
#include "powerset.hh"
#include "isdet.hh"
#include "tgba/tgbatba.hh"

namespace spot
{

  postprocessor::postprocessor(const option_map* opt)
    : type_(TGBA), pref_(Small), level_(High),
      degen_reset_(true), degen_order_(false), degen_cache_(true),
      simul_(-1), scc_filter_(-1), ba_simul_(-1), tba_determinisation_(false)
  {
    if (opt)
      {
	degen_order_ = opt->get("degen-order", 0);
	degen_reset_ = opt->get("degen-reset", 1);
	degen_cache_ = opt->get("degen-lcache", 1);
	simul_ = opt->get("simul", -1);
	simul_limit_ = opt->get("simul-limit", -1);
	scc_filter_ = opt->get("scc-filter", -1);
	ba_simul_ = opt->get("ba-simul", -1);
	tba_determinisation_ = opt->get("tba-det", 0);
      }
  }

  const tgba* postprocessor::do_simul(const tgba* a, int opt)
  {
    switch (opt)
      {
      case 0:
	return a;
      case 1:
	return simulation(a);
      case 2:
	return cosimulation(a);
      case 3:
      default:
	return iterated_simulations(a);
      case 4:
	return dont_care_simulation(a, simul_limit_);
      case 5:
	return dont_care_iterated_simulations(a, simul_limit_);
      }
  }

  const tgba* postprocessor::do_ba_simul(const tgba* a, int opt)
  {
    switch (opt)
      {
      case 0:
	return a;
      case 1:
	return simulation_sba(a);
      case 2:
	return cosimulation_sba(a);
      case 3:
      default:
	return iterated_simulations_sba(a);
      }
  }


  const tgba* postprocessor::do_degen(const tgba* a)
  {
    const tgba* d = degeneralize(a,
				 degen_reset_,
				 degen_order_,
				 degen_cache_);
    delete a;
    if (ba_simul_ <= 0)
      return d;

    const tgba* s = do_ba_simul(d, ba_simul_);
    if (s != d)
      delete d;

    return s;
  }

  const tgba* postprocessor::run(const tgba* a, const ltl::formula* f)
  {
    if (type_ == TGBA && pref_ == Any && level_ == Low)
      return a;

    if (simul_ < 0)
      simul_ = (level_ == Low) ? 1 : 3;
    if (ba_simul_ < 0)
      ba_simul_ = (level_ == High) ? 3 : 0;
    if (scc_filter_ < 0)
      scc_filter_ = 1;

    // Remove useless SCCs.
    if (type_ == Monitor)
      {
	// Do not bother about acceptance conditions, they we be
	// ignored.
	const tgba* s = scc_filter_states(a);
	delete a;
	a = s;
      }
    else if (scc_filter_ > 0)
      {
	const tgba* s = scc_filter(a, scc_filter_ > 1);
	delete a;
	a = s;
      }

    if (type_ == Monitor)
      {
	if (pref_ == Deterministic)
	  {
	    const tgba* m = minimize_monitor(a);
	    delete a;
	    return m;
	  }
	else
	  {
	    const tgba* m = strip_acceptance(a);
	    delete a;
	    a = m;
	  }
	if (pref_ == Any)
	  return a;

	const tgba* sim = do_simul(a, simul_);
	if (a == sim)
	  // simulation was disabled.
	  return a;
	if (level_ != High)
	  {
	    delete a;
	    return sim;
	  }
	// For Small,High we return the smallest between the output of
	// the simulation, and that of the deterministic minimization.
	const tgba* m = minimize_monitor(a);
	delete a;
	if (count_states(m) > count_states(sim))
	  {
	    delete m;
	    return sim;
	  }
	else
	  {
	    delete sim;
	    return m;
	  }
      }

    if (pref_ == Any)
      {
	if (type_ == BA)
	  a = do_degen(a);
	return a;
      }

    const tgba* wdba = 0;
    const tgba* sim = 0;

    // (Small,Low) is the only configuration where we do not run
    // WDBA-minimization.
    if (pref_ != Small || level_ != Low)
      {
	bool reject_bigger = (pref_ == Small) && (level_ == Medium);
	wdba = minimize_obligation(a, f, 0, reject_bigger);
	if (wdba == a)	// Minimization failed.
	  wdba = 0;
	// The WDBA is a BA, so no degeneralization is required.
      }

    // Run a simulation when wdba failed (or was not run), or
    // at hard levels if we want a small output.
    if (!wdba || (level_ == High && pref_ == Small))
      {
	sim = do_simul(a, simul_);

	if (sim != a)
	  delete a;

	// Degeneralize the result of the simulation if needed.
	if (type_ == BA)
	  sim = do_degen(sim);
      }
    else
      {
	delete a;
      }

    // If WDBA failed attempt tba-determinization if requested.
    if (tba_determinisation_ && !wdba && !is_deterministic(sim))
      {
	const tgba* tmpd = 0;
	if (pref_ == Deterministic
	    && f
	    && f->is_syntactic_recurrence()
	    && sim->number_of_acceptance_conditions() > 1)
	  tmpd = new tgba_tba_proxy(sim);

	// This threshold is arbitrary.  For producing Small automata,
	// we assume that a deterministic automaton that is twice the
	// size of the original will never get reduced to a smaller
	// one.  For Deterministic automata, we accept automata that
	// are 4 times bigger.  The larger the value, the more likely
	// the cycle enumeration algorithm will encounter an automaton
	// that takes *eons* to explore.
	const tgba* in = tmpd ? tmpd : sim;
	const tgba* tmp =
	  tba_determinize_check(in, (pref_ == Small) ? 2 : 4, f);
	if (tmp != 0 && tmp != in)
	  {
	    // There is no point in running the reverse simulation on
	    // a deterministic automaton, since all prefixes are
	    // unique.
	    wdba = simulation(tmp);
	    delete tmp;
	    // Degeneralize the result (which is a TBA) if requested.
	    if (type_ == BA)
	      {
		const tgba* d = degeneralize(wdba);
		delete wdba;
		wdba = d;
	      }
	  }
	delete tmpd;
	if (wdba && pref_ == Deterministic)
	  {
	    // disregard the result of the simulation.
	    delete sim;
	    sim = 0;
	  }
      }

    if (wdba && sim)
      {
	if (count_states(wdba) > count_states(sim))
	  {
	    delete wdba;
	    wdba = 0;
	  }
	else
	  {
	    delete sim;
	    sim = 0;
	  }
      }

    if (sim && type_ == TGBA && level_ == High && scc_filter_ != 0)
      {
	const tgba* s = scc_filter(sim, true);
	delete sim;
	return s;
      }

    return wdba ? wdba : sim;
  }
}
