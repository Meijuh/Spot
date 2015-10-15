// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014, 2015 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include "common_post.hh"
#include "common_r.hh"
#include "error.h"

spot::postprocessor::output_type type = spot::postprocessor::TGBA;
spot::postprocessor::output_pref pref = spot::postprocessor::Small;
spot::postprocessor::output_pref comp = spot::postprocessor::Any;
spot::postprocessor::output_pref sbacc = spot::postprocessor::Any;
spot::postprocessor::optimization_level level = spot::postprocessor::High;

bool level_set = false;
bool pref_set = false;

enum {
  OPT_HIGH = 1,
  OPT_LOW,
  OPT_MEDIUM,
  OPT_SMALL,
};

static const argp_option options[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Translation intent:", 20 },
    { "small", OPT_SMALL, nullptr, 0, "prefer small automata (default)", 0 },
    { "deterministic", 'D', nullptr, 0, "prefer deterministic automata", 0 },
    { "any", 'a', nullptr, 0, "no preference, do not bother making it small "
      "or deterministic", 0 },
    { "complete", 'C', nullptr, 0, "output a complete automaton (combine "
      "with other intents)", 0 },
    { "state-based-acceptance", 'S', nullptr, 0,
      "define the acceptance using states", 0 },
    { "sbacc", 0, nullptr, OPTION_ALIAS, nullptr, 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Optimization level:", 21 },
    { "low", OPT_LOW, nullptr, 0, "minimal optimizations (fast)", 0 },
    { "medium", OPT_MEDIUM, nullptr, 0, "moderate optimizations", 0 },
    { "high", OPT_HIGH, nullptr, 0,
      "all available optimizations (slow, default)", 0 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

static const argp_option options_disabled[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Translation intent:", 20 },
    { "small", OPT_SMALL, nullptr, 0, "prefer small automata", 0 },
    { "deterministic", 'D', nullptr, 0, "prefer deterministic automata", 0 },
    { "any", 'a', nullptr, 0, "no preference, do not bother making it small "
      "or deterministic", 0 },
    { "complete", 'C', nullptr, 0, "output a complete automaton (combine "
      "with other intents)", 0 },
    { "state-based-acceptance", 'S', nullptr, 0,
      "define the acceptance using states", 0 },
    { "sbacc", 0, nullptr, OPTION_ALIAS, nullptr, 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Optimization level:", 21 },
    { "low", OPT_LOW, nullptr, 0, "minimal optimizations (fast)", 0 },
    { "medium", OPT_MEDIUM, nullptr, 0, "moderate optimizations", 0 },
    { "high", OPT_HIGH, nullptr, 0,
      "all available optimizations (slow)", 0 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

static int
parse_opt_post(int key, char*, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case 'a':
      pref = spot::postprocessor::Any;
      pref_set = true;
      break;
    case 'C':
      comp = spot::postprocessor::Complete;
      break;
    case 'D':
      pref = spot::postprocessor::Deterministic;
      pref_set = true;
      break;
    case 'S':
      sbacc = spot::postprocessor::SBAcc;
      break;
    case OPT_HIGH:
      level = spot::postprocessor::High;
      simplification_level = 3;
      level_set = true;
      break;
    case OPT_LOW:
      level = spot::postprocessor::Low;
      simplification_level = 1;
      level_set = true;
      break;
    case OPT_MEDIUM:
      level = spot::postprocessor::Medium;
      simplification_level = 2;
      level_set = true;
      break;
    case OPT_SMALL:
      pref = spot::postprocessor::Small;
      pref_set = true;
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

const struct argp post_argp = { options, parse_opt_post,
				nullptr, nullptr, nullptr, nullptr, nullptr };
const struct argp post_argp_disabled = { options_disabled, parse_opt_post,
					 nullptr, nullptr, nullptr,
					 nullptr, nullptr };
