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
#include <iterator>
#include "error.h"

#include "common_setup.hh"
#include "common_output.hh"
#include "common_range.hh"
#include "common_r.hh"
#include "common_conv.hh"

#include <sstream>
#include <spot/tl/randomltl.hh>
#include <spot/tl/simplify.hh>
#include <spot/misc/random.hh>
#include <spot/misc/optionmap.hh>

const char argp_program_doc[] ="\
Generate random temporal logic formulas.\n\n\
The formulas are built over the atomic propositions named by PROPS...\n\
or, if N is a nonnegative number, using N arbitrary names.\v\
Examples:\n\
\n\
The following generates 10 random LTL formulas over the propositions a, b,\n\
and c, with the default tree-size, and all available operators.\n\
  % randltl -n10 a b c\n\
\n\
If you do not mind about the name of the atomic propositions, just give\n\
a number instead:\n\
  % randltl -n10 3\n\
\n\
You can disable or favor certain operators by changing their priority.\n\
The following disables xor, implies, and equiv, and multiply the probability\n\
of X to occur by 10.\n\
  % randltl --ltl-priorities='xor=0, implies=0, equiv=0, X=10' -n10 a b c\n\
";

enum {
  OPT_BOOLEAN_PRIORITIES = 1,
  OPT_DUMP_PRIORITIES,
  OPT_DUPS,
  OPT_LTL_PRIORITIES,
  OPT_PSL_PRIORITIES,
  OPT_SEED,
  OPT_SERE_PRIORITIES,
  OPT_TREE_SIZE,
  OPT_WF,
};

static const argp_option options[] =
  {
    // Keep this alphabetically sorted (expect for aliases).
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Type of formula to generate:", 1 },
    { "boolean", 'B', nullptr, 0, "generate Boolean formulas", 0 },
    { "ltl", 'L', nullptr, 0, "generate LTL formulas (default)", 0 },
    { "sere", 'S', nullptr, 0, "generate SERE", 0 },
    { "psl", 'P', nullptr, 0, "generate PSL formulas", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Generation:", 2 },
    { "weak-fairness", OPT_WF, nullptr, 0,
      "append some weak-fairness conditions", 0 },
    { "formulas", 'n', "INT", 0, "number of formulas to output (1)\n"\
      "use a negative value for unbounded generation", 0 },
    { "seed", OPT_SEED, "INT", 0,
      "seed for the random number generator (0)", 0 },
    { "tree-size", OPT_TREE_SIZE, "RANGE", 0,
      "tree size of the formulas generated, before mandatory "\
      "trivial simplifications (15)", 0 },
    { "allow-dups", OPT_DUPS, nullptr, 0,
      "allow duplicate formulas to be output", 0 },
    DECLARE_OPT_R,
    RANGE_DOC,
    LEVEL_DOC(3),
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Adjusting probabilities:", 4 },
    { "dump-priorities", OPT_DUMP_PRIORITIES, nullptr, 0,
      "show current priorities, do not generate any formula", 0 },
    { "ltl-priorities", OPT_LTL_PRIORITIES, "STRING", 0,
      "set priorities for LTL formulas", 0 },
    { "sere-priorities", OPT_SERE_PRIORITIES, "STRING", 0,
      "set priorities for SERE formulas", 0 },
    { "boolean-priorities", OPT_BOOLEAN_PRIORITIES, "STRING", 0,
      "set priorities for Boolean formulas", 0 },
    { nullptr, 0, nullptr, 0, "STRING should be a comma-separated list of "
      "assignments, assigning integer priorities to the tokens "
      "listed by --dump-priorities.", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", -20 },
    { nullptr, 0, nullptr, 0, "The FORMAT string passed to --format may use "
      "the following interpreted sequences:", -19 },
    { "%f", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the formula (in the selected syntax)", 0 },
    { "%L", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the (serial) number of the formula", 0 },
    { "%%", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "a single %", 0 },
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };


const struct argp_child children[] =
  {
    { &output_argp, 0, nullptr, -20 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

spot::atomic_prop_set aprops;
static int output = OUTPUTLTL;
static char* opt_pL = nullptr;
static char* opt_pS = nullptr;
static char* opt_pB = nullptr;
static bool opt_dump_priorities = false;
static int opt_formulas = 1;
static int opt_seed = 0;
static range opt_tree_size = { 15, 15 };
static bool opt_unique = true;
static bool opt_wf = false;
static bool ap_count_given = false;

static int
parse_opt(int key, char* arg, struct argp_state* as)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case 'B':
      output = OUTPUTBOOL;
      break;
    case 'L':
      output = OUTPUTLTL;
      break;
    case 'n':
      opt_formulas = to_int(arg);
      break;
    case 'P':
      output = OUTPUTPSL;
      break;
    case OPT_R:
      parse_r(arg);
      break;
    case 'S':
      output = OUTPUTSERE;
      break;
    case OPT_BOOLEAN_PRIORITIES:
      opt_pB = arg;
      break;
    case OPT_DUPS:
      opt_unique = false;
      break;
    case OPT_LTL_PRIORITIES:
      opt_pL = arg;
      break;
    case OPT_DUMP_PRIORITIES:
      opt_dump_priorities = true;
      break;
      // case OPT_PSL_PRIORITIES: break;
    case OPT_SERE_PRIORITIES:
      opt_pS = arg;
      break;
    case OPT_SEED:
      opt_seed = to_int(arg);
      break;
    case OPT_TREE_SIZE:
      opt_tree_size = parse_range(arg);
      if (opt_tree_size.min > opt_tree_size.max)
	std::swap(opt_tree_size.min, opt_tree_size.max);
      break;
    case OPT_WF:
      opt_wf = true;
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
	      aprops = spot::create_atomic_prop_set(res);
	      break;
	    }
	}
      aprops.insert(spot::default_environment::instance().require(arg));
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
		    children, nullptr, nullptr };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
    exit(err);

  // running 'randltl 0' is one way to generate formulas using no
  // atomic propositions so do not complain in that case.
  if (aprops.empty() && !ap_count_given)
    error(2, 0, "No atomic proposition supplied?   Run '%s --help' for usage.",
	  program_name);

  spot::srand(opt_seed);
  try
    {
      spot::randltlgenerator rg
	(aprops,
	 [&] (){
	  spot::option_map opts;
	  opts.set("output", output);
	  opts.set("tree_size_min", opt_tree_size.min);
	  opts.set("tree_size_max", opt_tree_size.max);
	  opts.set("wf", opt_wf);
	  opts.set("seed", opt_seed);
	  opts.set("simplification_level", simplification_level);
	  return opts;
	}(), opt_pL, opt_pS, opt_pB);

      if (opt_dump_priorities)
	{
	  switch (output)
	    {
	    case OUTPUTLTL:
	      std::cout <<
		"Use --ltl-priorities to set the following LTL priorities:\n";
	      rg.dump_ltl_priorities(std::cout);
	      break;
	    case OUTPUTBOOL:
	      std::cout <<
		"Use --boolean-priorities to set the following Boolean "
		"formula priorities:\n";
	      rg.dump_bool_priorities(std::cout);
	      break;
	    case OUTPUTPSL:
	      std::cout <<
		"Use --ltl-priorities to set the following LTL priorities:\n";
	      rg.dump_psl_priorities(std::cout);
	      // Fall through.
	    case OUTPUTSERE:
	      std::cout <<
		"Use --sere-priorities to set the following SERE priorities:\n";
	      rg.dump_sere_priorities(std::cout);
	      std::cout <<
		"Use --boolean-priorities to set the following Boolean "
		"formula priorities:\n";
	      rg.dump_sere_bool_priorities(std::cout);
	      break;
	    default:
	      error(2, 0, "internal error: unknown type of output");
	    }
	  exit(0);
	}

      while (opt_formulas < 0 || opt_formulas--)
	{
	  static int count = 0;
	  spot::formula f = rg.next();
	  if (!f)
	    {
	      error(2, 0, "failed to generate a new unique formula after %d " \
		    "trials", MAX_TRIALS);
	    }
	  else
	    {
	      output_formula_checked(f, nullptr, ++count);
	    }
	};
    }
  catch (const std::runtime_error& e)
    {
      error(2, 0, "%s", e.what());
    }
  catch (const std::invalid_argument& e)
    {
      error(2, 0, "%s", e.what());
    }

  return 0;
}