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

#include "common_sys.hh"

#include <iostream>
#include <fstream>
#include <argp.h>
#include <cstdlib>
#include <sstream>
#include <iterator>
#include "error.h"
#include "argmatch.h"

#include "common_setup.hh"
#include "common_range.hh"
#include "common_cout.hh"
#include "common_aoutput.hh"
#include "common_conv.hh"

#include "ltlenv/defaultenv.hh"
#include "misc/timer.hh"
#include "misc/random.hh"

#include "tgba/bddprint.hh"
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

enum {
  OPT_SEED = 1,
  OPT_STATE_ACC,
  OPT_ACC_TYPE,
};

static const argp_option options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Generation:", 2 },
    { "acc-type", OPT_ACC_TYPE, "buchi|random", 0,
      "use a generalized buchi acceptance condition (default), or a "
      "random acceptance condition", 0 },
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
    { "unique", 'u', 0, 0,
      "do not output the same automaton twice (same in the sense that they "\
      "are isomorphic)", 0 },
    { "seed", OPT_SEED, "INT", 0,
      "seed for the random number generator (0)", 0 },
    { "states", 'S', "RANGE", 0, "number of states to output (10)", 0 },
    { "state-acc", OPT_STATE_ACC, 0, 0, "use state-based acceptance", 0 },
    RANGE_DOC,
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { 0, 0, 0, 0, 0, 0 }
  };


static const struct argp_child children[] =
  {
    { &aoutput_argp, 0, 0, 3 },
    { &aoutput_o_format_argp, 0, 0, 4 },
    { &misc_argp, 0, 0, -1 },
    { 0, 0, 0, 0 }
  };

enum acc_type { acc_buchi, acc_random };

static char const *const acc_args[] =
{
  "buchi", "ba", "gba",
  "random",
  0
};
static acc_type const acc_types[] =
{
  acc_buchi, acc_buchi, acc_buchi,
  acc_random,
};
ARGMATCH_VERIFY(acc_args, acc_types);


static acc_type opt_acc = acc_buchi;
typedef spot::twa_graph::graph_t::trans_storage_t tr_t;
typedef std::set<std::vector<tr_t>> unique_aut_t;
static spot::ltl::atomic_prop_set aprops;
static bool ap_count_given = false;
static int opt_seed = 0;
static const char* opt_seed_str = "0";
static int opt_automata = 1;
static range opt_states = { 10, 10 };
static float opt_density = 0.2;
static range opt_acc_sets = { 0, 0 };
static float opt_acc_prob = 0.2;
static bool opt_deterministic = false;
static bool opt_state_acc = false;
static bool ba_wanted = false;
static std::unique_ptr<unique_aut_t> opt_uniq = nullptr;

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
    case 'n':
      opt_automata = to_int(arg);
      break;
    case 'S':
      opt_states = parse_range(arg);
      if (opt_states.min > opt_states.max)
	std::swap(opt_states.min, opt_states.max);
      break;
    case 'u':
      opt_uniq =
        std::unique_ptr<unique_aut_t>(new std::set<std::vector<tr_t>>());
      break;
    case OPT_ACC_TYPE:
      opt_acc = XARGMATCH("--acc-type", arg, acc_args, acc_types);
      break;
    case OPT_SEED:
      opt_seed = to_int(arg);
      opt_seed_str = arg;
      break;
    case OPT_STATE_ACC:
      opt_state_acc = true;
      break;
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
  strcpy(F_doc, "seed number");
  strcpy(L_doc, "automaton number");
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

  if (automaton_format == Spin && opt_acc_sets.max > 1)
    error(2, 0, "--spin is incompatible with --acc-sets=%d..%d",
	  opt_acc_sets.min, opt_acc_sets.max);
  if (automaton_format == Spin && opt_acc != acc_buchi)
    error(2, 0,
	  "--spin implies --acc-type=buchi but a different --acc-type is used");
  if (ba_wanted && opt_acc_sets.min != 1 && opt_acc_sets.max != 1)
    error(2, 0, "--ba is incompatible with --acc-sets=%d..%d",
	  opt_acc_sets.min, opt_acc_sets.max);
  if (ba_wanted && opt_acc != acc_buchi)
    error(2, 0,
	  "--ba implies --acc-type=buchi but a different --acc-type is used");

  try
    {
      spot::srand(opt_seed);
      auto d = spot::make_bdd_dict();

      automaton_printer printer;

      constexpr unsigned max_trials = 10000;
      unsigned trials = max_trials;

      int automaton_num = 0;

      for (;;)
	{
	  spot::stopwatch sw;
	  sw.start();

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

	  switch (opt_acc)
	    {
	    case acc_buchi:
	      // Random_graph builds a GBA by default
	      break;
	    case acc_random:
	      aut->set_acceptance(accs, spot::random_acceptance(accs));
	      break;
	    }

	  if (opt_uniq)
	    {
	      auto tmp = spot::canonicalize
		(make_twa_graph(aut, spot::twa::prop_set::all()));
	      std::vector<tr_t> trans(tmp->transition_vector().begin() + 1,
				      tmp->transition_vector().end());
	      if (!opt_uniq->emplace(trans).second)
		{
		  --trials;
		  if (trials == 0)
		    error(2, 0, "failed to generate a new unique automaton"
			  " after %d trials", max_trials);
		  continue;
		}
	      trials = max_trials;
	    }

	  auto runtime = sw.stop();

	  printer.print(aut, nullptr,
			opt_seed_str, automaton_num, runtime, nullptr);

	  ++automaton_num;
	  if (opt_automata > 0 && automaton_num >= opt_automata)
	    break;
	}
    }
  catch (const std::runtime_error& e)
    {
      error(2, 0, "%s", e.what());
    }
  spot::ltl::destroy_atomic_prop_set(aprops);
}
