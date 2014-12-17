// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014 Laboratoire de Recherche et
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
#include <sstream>
#include <iterator>
#include "error.h"

#include "common_setup.hh"
#include "common_range.hh"
#include "common_cout.hh"

#include "ltlenv/defaultenv.hh"
#include "misc/random.hh"

#include "tgba/bddprint.hh"
#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/lbtt.hh"
#include "tgbaalgos/hoa.hh"
#include "tgbaalgos/neverclaim.hh"
#include "tgbaalgos/randomgraph.hh"
#include "tgbaalgos/canonicalize.hh"


const char argp_program_doc[] = "\
Generate random connected automata.\n\n\
The automata are built over the atomic propositions named by PROPS...\n\
or, if N is a nonnegative number, using N arbitrary names.\n\
If the density is set to D, and the number of states to S, the degree\n\
of each state follows a normal distribution with mean 1+(S-1)D and\n\
variance (S-1)D(1-D).  In particular, for D=0 all states have a single\n\
successor, while for D=1 all states are interconnected.\v\
Examples:\n\
\n\
This builds a random neverclaim with 4 states and labeled using the two\n\
atomic propositions \"a\" and \"b\":\n\
  % randaut --spin -S4 a b\n\
\n\
This builds three random, complete, and deterministic TGBA with 5 to 10\n\
states, 1 to 3 acceptance sets, and three atomic propositions:\n\
  % randaut -n 3 --hoa -S5..10 -A1..3 3\n\
";

#define OPT_TGBA 1
#define OPT_DOT 2
#define OPT_LBTT 3
#define OPT_SEED 4
#define OPT_STATE_ACC 5
#define OPT_UNIQ 6

static const argp_option options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Generation:", 2 },
    { "acc-sets", 'A', "RANGE", 0, "number of acceptance sets (0)", 0 },
    { "acc-probability", 'a', "FLOAT", 0,
      "probability that a transition belong to one acceptance set (0.2)", 0 },
    { "automata", 'n', "INT", 0, "number of automata to output (1)\n"\
      "use a negative value for unbounded generation", 0 },
    { "ba", 'B', 0, 0,
      "build a Buchi automaton (implies --acc-sets=1 --state-acc)", 0 },
    { "density", 'd', "FLOAT", 0, "density of the transitions (0.2)", 0 },
    { "deterministic", 'D', 0, 0, "build a complete, deterministic automaton ",
      0 },
    { "uniq", OPT_UNIQ, 0, 0,
      "do not output the same automaton twice (same in the sense that they "\
      "are isomorphic)", 0 },
    { "seed", OPT_SEED, "INT", 0,
      "seed for the random number generator (0)", 0 },
    { "states", 'S', "RANGE", 0, "number of states to output (10)", 0 },
    { "state-acc", OPT_STATE_ACC, 0, 0, "use state-based acceptance", 0 },
    RANGE_DOC,
    /**************************************************/
    { 0, 0, 0, 0, "Output format:", 3 },
    { "dot", OPT_DOT, "c|h|n|N|t|v", OPTION_ARG_OPTIONAL,
      "GraphViz's format (default).  Add letters to chose (c) circular nodes, "
      "(h) horizontal layout, (v) vertical layout, (n) with name, "
      "(N) without name, (t) always transition-based acceptance.", 0 },
    { "hoaf", 'H', "s|t|m|l", OPTION_ARG_OPTIONAL,
      "Output the automaton in HOA format.  Add letters to select "
      "(s) state-based acceptance, (t) transition-based acceptance, "
      "(m) mixed acceptance, (l) single-line output", 0 },
    { "lbtt", OPT_LBTT, "t", OPTION_ARG_OPTIONAL,
      "LBTT's format (add =t to force transition-based acceptance even"
      " on Büchi automata)", 0 },
    { "spin", 's', 0, 0, "Spin neverclaim (implies --ba)", 0 },
    { "utf8", '8', 0, 0, "enable UTF-8 characters in output "
      "(ignored with --lbtt or --spin)", 0 },
    { 0, 0, 0, 0, 0, 0 }
  };


static const struct argp_child children[] =
  {
    { &misc_argp, 0, 0, -1 },
    { 0, 0, 0, 0 }
  };

typedef spot::tgba_digraph::graph_t::trans_storage_t tr_t;
typedef std::set<std::vector<tr_t>> unique_aut_t;
static enum output_format { Dot, Lbtt, Lbtt_t, Spin, Hoa } format = Dot;
const char* opt_dot = nullptr;
static const char* hoa_opt = 0;
static spot::ltl::atomic_prop_set aprops;
static bool ap_count_given = false;
static int opt_seed = 0;
static int opt_automata = 1;
static range opt_states = { 10, 10 };
static float opt_density = 0.2;
static range opt_acc_sets = { 0, 0 };
static float opt_acc_prob = 0.2;
static bool opt_deterministic = false;
static bool opt_state_acc = false;
static bool ba_wanted = false;
static std::unique_ptr<unique_aut_t> opt_uniq = nullptr;

static int
to_int(const char* s)
{
  char* endptr;
  int res = strtol(s, &endptr, 10);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as an integer.", s);
  return res;
}

static float
to_float(const char* s)
{
  char* endptr;
  float res = strtof(s, &endptr);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as a float.", s);
  return res;
}

static void
ba_options()
{
  opt_acc_sets = { 1, 1 };
  opt_state_acc = true;
}

static int
parse_opt(int key, char* arg, struct argp_state* as)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case '8':
      spot::enable_utf8();
      break;
    case 'a':
      opt_acc_prob = to_float(arg);
      if (opt_acc_prob < 0.0 || opt_acc_prob > 1.0)
	error(2, 0, "probability of acceptance set membership "
	      "should be between 0.0 and 1.0");
      break;
    case 'A':
      opt_acc_sets = parse_range(arg);
      if (opt_acc_sets.min > opt_acc_sets.max)
	std::swap(opt_acc_sets.min, opt_acc_sets.max);
      if (opt_acc_sets.min < 0)
	error(2, 0, "number of acceptance sets should be positive");
      break;
    case 'B':
      ba_options();
      ba_wanted = true;
      break;
    case 'd':
      opt_density = to_float(arg);
      if (opt_density < 0.0 || opt_density > 1.0)
	error(2, 0, "density should be between 0.0 and 1.0");
      break;
    case 'D':
      opt_deterministic = true;
      break;
    case 'H':
      format = Hoa;
      hoa_opt = arg;
      break;
    case 'n':
      opt_automata = to_int(arg);
      break;
    case 's':
      format = Spin;
      ba_options();
      break;
    case 'S':
      opt_states = parse_range(arg);
      if (opt_states.min > opt_states.max)
	std::swap(opt_states.min, opt_states.max);
      break;
    case OPT_DOT:
      format = Dot;
      opt_dot = arg;
      break;
    case OPT_LBTT:
      if (arg)
	{
	  if (arg[0] == 't' && arg[1] == 0)
	    format = Lbtt_t;
	  else
	    error(2, 0, "unknown argument for --lbtt: '%s'", arg);
	}
      else
	{
	  format = Lbtt;
	}
      break;
    case OPT_SEED:
      opt_seed = to_int(arg);
      break;
    case OPT_STATE_ACC:
      opt_state_acc = true;
      break;
    case OPT_UNIQ:
      opt_uniq =
        std::unique_ptr<unique_aut_t>(new std::set<std::vector<tr_t>>());
    case ARGP_KEY_ARG:
      // If this is the unique non-option argument, it can
      // be a number of atomic propositions to build.
      //
      // argp reorganizes argv[] so that options always come before
      // non-options.  So if as->argc == as->next we know this is the
      // last non-option argument, and if aprops.empty() we know this
      // is the also the first one.
      if (aprops.empty() && as->argc == as->next)
	{
	  char* endptr;
	  int res = strtol(arg, &endptr, 10);
	  if (!*endptr && res >= 0) // arg is a number
	    {
	      ap_count_given = true;
	      aprops = spot::ltl::create_atomic_prop_set(res);
	      break;
	    }
	}
      aprops.insert(spot::ltl::default_environment::instance().require(arg));
      break;

    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}


int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, parse_opt, "N|PROP...", argp_program_doc,
		    children, 0, 0 };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, 0, 0))
    exit(err);

  // running 'randaut 0' is one way to generate automata using no
  // atomic propositions so do not complain in that case.
  if (aprops.empty() && !ap_count_given)
    error(2, 0, "No atomic proposition supplied?   Run '%s --help' for usage.",
	  program_name);

  if (format == Spin && opt_acc_sets.max > 1)
    error(2, 0, "--spin is incompatible with --acc-sets=%d..%d",
	  opt_acc_sets.min, opt_acc_sets.max);
  if (ba_wanted && opt_acc_sets.min != 1 && opt_acc_sets.max != 1)
    error(2, 0, "--ba is incompatible with --acc-sets=%d..%d",
	  opt_acc_sets.min, opt_acc_sets.max);

  spot::srand(opt_seed);
  auto d = spot::make_bdd_dict();

  while (opt_automata < 0 || opt_automata--)
    {
      int size = opt_states.min;
      if (size != opt_states.max)
	size = spot::rrand(size, opt_states.max);

      int accs = opt_acc_sets.min;
      if (accs != opt_acc_sets.max)
	accs = spot::rrand(accs, opt_acc_sets.max);

      auto aut =
	spot::random_graph(size, opt_density, &aprops, d,
			   accs, opt_acc_prob, 0.5,
			   opt_deterministic, opt_state_acc);

      if (opt_uniq)
        {
          auto tmp = make_tgba_digraph(spot::canonicalize(aut));
          std::vector<tr_t> trans(tmp->transition_vector().begin() + 1,
                                  tmp->transition_vector().end());
          if (opt_uniq->emplace(trans).second)
            return 0;
        }

      bool is_ba = accs == 0 || (accs == 1 && opt_state_acc);

      switch (format)
	{
	case Dot:
	  spot::dotty_reachable(std::cout, aut, is_ba, opt_dot);
	  break;
	case Lbtt:
	  spot::lbtt_reachable(std::cout, aut, is_ba);
	  break;
	case Lbtt_t:
	  spot::lbtt_reachable(std::cout, aut, false);
	  break;
	case Hoa:
	  spot::hoa_reachable(std::cout, aut, hoa_opt) << '\n';
	  break;
	case Spin:
	  spot::never_claim_reachable(std::cout, aut);
	  break;
	}
      flush_cout();
    }
  spot::ltl::destroy_atomic_prop_set(aprops);
}
