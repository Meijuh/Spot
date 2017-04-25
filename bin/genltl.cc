// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2015-2017 Laboratoire de Recherche et
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


#include "common_sys.hh"

#include <iostream>
#include <fstream>
#include <argp.h>
#include <cstdlib>
#include "error.h"
#include <vector>

#include "common_setup.hh"
#include "common_output.hh"
#include "common_range.hh"
#include "common_cout.hh"

#include <cassert>
#include <iostream>
#include <sstream>
#include <set>
#include <string>
#include <cstdlib>
#include <cstring>
#include <spot/tl/formula.hh>
#include <spot/tl/relabel.hh>
#include <spot/gen/formulas.hh>

using namespace spot;

const char argp_program_doc[] ="\
Generate temporal logic formulas from predefined patterns.";

// We reuse the values from spot::gen::ltl_patterns as option keys.
// Additional options should therefore start after
// spot::gen::LAST_CLASS.
enum {
  OPT_POSITIVE = spot::gen::LAST_CLASS + 1,
  OPT_NEGATIVE,
};


#define OPT_ALIAS(o) { #o, 0, nullptr, OPTION_ALIAS, nullptr, 0 }

static const argp_option options[] =
  {
    /**************************************************/
    // Keep this alphabetically sorted (expect for aliases).
    { nullptr, 0, nullptr, 0, "Pattern selection:", 1},
    // J. Geldenhuys and H. Hansen (Spin'06): Larger automata and less
    // work for LTL model checking.
    { "and-f", spot::gen::AND_F, "RANGE", 0, "F(p1)&F(p2)&...&F(pn)", 0 },
    OPT_ALIAS(gh-e),
    { "and-fg", spot::gen::AND_FG, "RANGE", 0, "FG(p1)&FG(p2)&...&FG(pn)", 0 },
    { "and-gf", spot::gen::AND_GF, "RANGE", 0, "GF(p1)&GF(p2)&...&GF(pn)", 0 },
    OPT_ALIAS(ccj-phi),
    OPT_ALIAS(gh-c2),
    { "ccj-alpha", spot::gen::CCJ_ALPHA, "RANGE", 0,
      "F(p1&F(p2&F(p3&...F(pn)))) & F(q1&F(q2&F(q3&...F(qn))))", 0 },
    { "ccj-beta", spot::gen::CCJ_BETA, "RANGE", 0,
      "F(p&X(p&X(p&...X(p)))) & F(q&X(q&X(q&...X(q))))", 0 },
    { "ccj-beta-prime", spot::gen::CCJ_BETA_PRIME, "RANGE", 0,
      "F(p&(Xp)&(XXp)&...(X...X(p))) & F(q&(Xq)&(XXq)&...(X...X(q)))", 0 },
    { "dac-patterns", spot::gen::DAC_PATTERNS, "RANGE", OPTION_ARG_OPTIONAL,
      "Dwyer et al. [FMSP'98] Spec. Patterns for LTL "
      "(range should be included in 1..55)", 0 },
    OPT_ALIAS(spec-patterns),
    { "eh-patterns", spot::gen::EH_PATTERNS, "RANGE", OPTION_ARG_OPTIONAL,
      "Etessami and Holzmann [Concur'00] patterns "
      "(range should be included in 1..12)", 0 },
    { "gh-q", spot::gen::GH_Q, "RANGE", 0,
      "(F(p1)|G(p2))&(F(p2)|G(p3))&...&(F(pn)|G(p{n+1}))", 0 },
    { "gh-r", spot::gen::GH_R, "RANGE", 0,
      "(GF(p1)|FG(p2))&(GF(p2)|FG(p3))&... &(GF(pn)|FG(p{n+1}))", 0 },
    { "go-theta", spot::gen::GO_THETA, "RANGE", 0,
      "!((GF(p1)&GF(p2)&...&GF(pn)) -> G(q->F(r)))", 0 },
    { "hkrss-patterns", spot::gen::HKRSS_PATTERNS, "RANGE", OPTION_ARG_OPTIONAL,
      "Holeček et al. patterns from the Liberouter project "
      "(range should be included in 1..55)", 0 },
    OPT_ALIAS(liberouter-patterns),
    { "kr-n", spot::gen::KR_N, "RANGE", 0,
      "linear formula with doubly exponential DBA", 0 },
    { "kr-nlogn", spot::gen::KR_NLOGN, "RANGE", 0,
      "quasilinear formula with doubly exponential DBA", 0 },
    { "kv-psi", spot::gen::KV_PSI, "RANGE", 0,
      "quadratic formula with doubly exponential DBA", 0 },
    OPT_ALIAS(kr-n2),
    { "or-fg", spot::gen::OR_FG, "RANGE", 0, "FG(p1)|FG(p2)|...|FG(pn)", 0 },
    OPT_ALIAS(ccj-xi),
    { "or-g", spot::gen::OR_G, "RANGE", 0, "G(p1)|G(p2)|...|G(pn)", 0 },
    OPT_ALIAS(gh-s),
    { "or-gf", spot::gen::OR_GF, "RANGE", 0, "GF(p1)|GF(p2)|...|GF(pn)", 0 },
    OPT_ALIAS(gh-c1),
    { "p-patterns", spot::gen::P_PATTERNS, "RANGE", OPTION_ARG_OPTIONAL,
      "Pelánek [Spin'07] patterns from BEEM "
      "(range should be included in 1..20)", 0 },
    OPT_ALIAS(beem-patterns),
    OPT_ALIAS(p),
    { "r-left", spot::gen::R_LEFT, "RANGE", 0,
      "(((p1 R p2) R p3) ... R pn)", 0 },
    { "r-right", spot::gen::R_RIGHT, "RANGE", 0,
      "(p1 R (p2 R (... R pn)))", 0 },
    { "rv-counter", spot::gen::RV_COUNTER, "RANGE", 0,
      "n-bit counter", 0 },
    { "rv-counter-carry", spot::gen::RV_COUNTER_CARRY, "RANGE", 0,
      "n-bit counter w/ carry", 0 },
    { "rv-counter-carry-linear", spot::gen::RV_COUNTER_CARRY_LINEAR, "RANGE", 0,
      "n-bit counter w/ carry (linear size)", 0 },
    { "rv-counter-linear", spot::gen::RV_COUNTER_LINEAR, "RANGE", 0,
      "n-bit counter (linear size)", 0 },
    { "sb-patterns", spot::gen::SB_PATTERNS, "RANGE", OPTION_ARG_OPTIONAL,
      "Somenzi and Bloem [CAV'00] patterns "
      "(range should be included in 1..27)", 0 },
    { "tv-f1", spot::gen::TV_F1, "RANGE", 0,
      "G(p -> (q | Xq | ... | XX...Xq)", 0 },
    { "tv-f2", spot::gen::TV_F2, "RANGE", 0,
      "G(p -> (q | X(q | X(... | Xq)))", 0 },
    { "tv-g1", spot::gen::TV_G1, "RANGE", 0,
      "G(p -> (q & Xq & ... & XX...Xq)", 0 },
    { "tv-g2", spot::gen::TV_G2, "RANGE", 0,
      "G(p -> (q & X(q & X(... & Xq)))", 0 },
    { "tv-uu", spot::gen::TV_UU, "RANGE", 0,
      "G(p1 -> (p1 U (p2 & (p2 U (p3 & (p3 U ...))))))", 0 },
    { "u-left", spot::gen::U_LEFT, "RANGE", 0,
      "(((p1 U p2) U p3) ... U pn)", 0 },
    OPT_ALIAS(gh-u),
    { "u-right", spot::gen::U_RIGHT, "RANGE", 0,
      "(p1 U (p2 U (... U pn)))", 0 },
    OPT_ALIAS(gh-u2),
    OPT_ALIAS(go-phi),
    RANGE_DOC,
  /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", -20 },
    { "negative", OPT_NEGATIVE, nullptr, 0,
      "output the negated versions of all formulas", 0 },
    OPT_ALIAS(negated),
    { "positive", OPT_POSITIVE, nullptr, 0,
      "output the positive versions of all formulas (done by default, unless"
      " --negative is specified without --positive)", 0 },
    { nullptr, 0, nullptr, 0, "The FORMAT string passed to --format may use "
      "the following interpreted sequences:", -19 },
    { "%f", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the formula (in the selected syntax)", 0 },
    { "%F", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the name of the pattern", 0 },
    { "%L", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the argument of the pattern", 0 },
    { "%%", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "a single %", 0 },
    COMMON_LTL_OUTPUT_SPECS,
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

struct job
{
  spot::gen::ltl_pattern pattern;
  struct range range;
};

typedef std::vector<job> jobs_t;
static jobs_t jobs;
bool opt_positive = false;
bool opt_negative = false;

const struct argp_child children[] =
  {
    { &output_argp, 0, nullptr, -20 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

static void
enqueue_job(int pattern, const char* range_str)
{
  job j;
  j.pattern = static_cast<spot::gen::ltl_pattern>(pattern);
  j.range = parse_range(range_str);
  jobs.push_back(j);
}

static void
enqueue_job(int pattern, int min, int max)
{
  job j;
  j.pattern = static_cast<spot::gen::ltl_pattern>(pattern);
  j.range = {min, max};
  jobs.push_back(j);
}

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case spot::gen::DAC_PATTERNS:
    case spot::gen::HKRSS_PATTERNS:
      if (arg)
        enqueue_job(key, arg);
      else
        enqueue_job(key, 1, 55);
      break;
    case spot::gen::EH_PATTERNS:
      if (arg)
        enqueue_job(key, arg);
      else
        enqueue_job(key, 1, 12);
      break;
    case spot::gen::P_PATTERNS:
      if (arg)
        enqueue_job(key, arg);
      else
        enqueue_job(key, 1, 20);
      break;
    case spot::gen::SB_PATTERNS:
      if (arg)
        enqueue_job(key, arg);
      else
        enqueue_job(key, 1, 27);
      break;
    case OPT_POSITIVE:
      opt_positive = true;
      break;
    case OPT_NEGATIVE:
      opt_negative = true;
      break;
    default:
      if (key >= spot::gen::FIRST_CLASS && key < spot::gen::LAST_CLASS)
        {
          enqueue_job(key, arg);
          break;
        }
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}


static void
output_pattern(spot::gen::ltl_pattern pattern, int n)
{
  formula f = spot::gen::genltl(pattern, n);

  // Make sure we use only "p42"-style of atomic propositions
  // in lbt's output.
  if (output_format == lbt_output && !f.has_lbt_atomic_props())
    f = relabel(f, Pnn);

  if (opt_positive || !opt_negative)
    {
      output_formula_checked(f, spot::gen::ltl_pattern_name(pattern), n);
    }
  if (opt_negative)
    {
      std::string tmp = "!";
      tmp += spot::gen::ltl_pattern_name(pattern);
      output_formula_checked(spot::formula::Not(f), tmp.c_str(), n);
    }
}

static void
run_jobs()
{
  for (auto& j: jobs)
    {
      int inc = (j.range.max < j.range.min) ? -1 : 1;
      int n = j.range.min;
      for (;;)
        {
          output_pattern(j.pattern, n);
          if (n == j.range.max)
            break;
          n += inc;
        }
    }
}


int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, parse_opt, nullptr, argp_program_doc,
                    children, nullptr, nullptr };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
    exit(err);

  if (jobs.empty())
    error(1, 0, "Nothing to do.  Try '%s --help' for more information.",
          program_name);

  try
    {
      run_jobs();
    }
  catch (const std::runtime_error& e)
    {
      error(2, 0, "%s", e.what());
    }

  flush_cout();
  return 0;
}
