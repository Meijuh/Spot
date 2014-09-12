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
#include <argp.h>
#include <limits>
#include "common_setup.hh"
#include "common_finput.hh"
#include "common_output.hh"
#include "error.h"
#include "ltlast/allnodes.hh"
#include "ltlvisit/clone.hh"
#include "ltlvisit/apcollect.hh"
#include "ltlvisit/length.hh"
#include "ltlvisit/mutation.hh"

#define OPT_AP2CONST 1
#define OPT_SIMPLIFY_BOUNDS 2
#define OPT_REMOVE_MULTOP_OPERANDS 3
#define OPT_REMOVE_OPS 4
#define OPT_SPLIT_OPS 5
#define OPT_REWRITE_OPS 6
#define OPT_REMOVE_ONE_AP 7
#define OPT_SORT 8

static unsigned mutation_nb = 1;
static int max_output = std::numeric_limits<int>::max();

static unsigned opt_all = 0xfff;
static unsigned mut_opts = 0;
static bool opt_sort = false;

const char * argp_program_doc = "List formulas that are similar to but " \
  "simpler than a given formula.";

static const argp_option options[] = {
  {"mutations", 'm', "N", 0, "number of mutations to apply to the " \
   "formulae (default: 1)", -1},
  {"sort", OPT_SORT, 0, 0, "sort the result by formula size", 0},
  {0, 0, 0, 0, "Transformation rules:", 15},
  {"ap-to-const", OPT_AP2CONST, 0, 0,
   "atomic propositions are replaced with true/false", 15},
  {"remove-one-ap", OPT_REMOVE_ONE_AP, 0, 0,
   "all occurrences of an atomic proposition are replaced with another" \
   "atomic proposition used in the formula", 15},
  {"remove-multop-operands", OPT_REMOVE_MULTOP_OPERANDS, 0, 0,
   "remove one operand from multops", 15},
  {"remove-ops", OPT_REMOVE_OPS, 0, 0,
   "replace unary/binary operators with one of their operands",
   15},
  {"split-ops", OPT_SPLIT_OPS, 0, 0,
   "when an operator can be expressed as a conjunction/disjunction using " \
   "simpler operators, each term of the conjunction/disjunction is a " \
   "mutation. e.g. a <-> b can be written as ((a & b) | (!a & !b)) or as " \
   "((a -> b) & (b -> a)) so those four terms can be a mutation of a <-> b", 0},
  {"rewrite-ops", OPT_REWRITE_OPS, 0, 0,
   "rewrite operators that have a semantically simpler form: a U b becomes " \
   "a W b, etc.", 0},
  {"simplify-bounds", OPT_SIMPLIFY_BOUNDS, 0, 0,
   "on a bounded unary operator, decrement one of the bounds, or set min to " \
   "0 or max to " \
   "unbounded.", 15},
  {0, 0, 0, 0, "Output options:", 20},
  {"max-output", 'n', "N", 0, "maximum number of mutations to output", 20},
  {0, 0, 0, 0, "Miscellaneous options:", -1},
  {0, 0, 0, 0, 0, 0}
};

static const argp_child children[] = {
  {&finput_argp, 0, 0, 10},
  {&output_argp, 0, 0, 20},
  {&misc_argp, 0, 0, -1},
  {0, 0, 0, 0}
};

static int
to_int(const char *s)
{
  char* endptr;
  unsigned res = strtol(s, &endptr, 10);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as an unsigned integer.", s);
  return res;
}

static unsigned
to_unsigned (const char *s)
{
  char* endptr;
  unsigned res = strtoul(s, &endptr, 10);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as an unsigned integer.", s);
  return res;
}

namespace
{
  using namespace spot::ltl;

  class mutate_processor:
    public job_processor
  {
  public:
    int
    process_formula(const formula* f, const char *filename = 0,
		    int linenum = 0)
    {
      std::vector<const formula*> mutations =
      	get_mutations(f, mut_opts, opt_sort, max_output, mutation_nb);

      f->destroy();
      std::vector<const formula*>::iterator it;
      for (it = mutations.begin(); it != mutations.end(); ++it)
	{
	  output_formula_checked(*it, filename, linenum);
	  (*it)->destroy();
	}
      return 0;
    }
  };
}

int
parse_opt(int key, char* arg, struct argp_state*)
{
  switch (key)
    {
    case 'm':
      mutation_nb = to_unsigned(arg);
      break;
    case 'n':
      max_output = to_int(arg);
      break;
    case OPT_AP2CONST:
      opt_all = 0;
      mut_opts |= MUT_AP2CONST;
      break;
    case OPT_REMOVE_ONE_AP:
      opt_all = 0;
      mut_opts |= MUT_REMOVE_ONE_AP;
      break;
    case OPT_REMOVE_MULTOP_OPERANDS:
      opt_all = 0;
      mut_opts |= MUT_REMOVE_MULTOP_OPERANDS;
      break;
    case OPT_REMOVE_OPS:
      opt_all = 0;
      mut_opts |= MUT_REMOVE_OPS;
      break;
    case OPT_SPLIT_OPS:
      opt_all = 0;
      mut_opts |= MUT_SPLIT_OPS;
      break;
    case OPT_REWRITE_OPS:
      opt_all = 0;
      mut_opts |= MUT_REWRITE_OPS;
      break;
    case OPT_SIMPLIFY_BOUNDS:
      opt_all = 0;
      mut_opts |= MUT_SIMPLIFY_BOUNDS;
      break;
    case OPT_SORT:
      opt_sort = true;
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

int
main(int argc, char* argv[])
{
  setup(argv);

  const argp ap = { options, parse_opt, 0, argp_program_doc, children, 0, 0 };

  if (int err = argp_parse(&ap, argc, argv, 0, 0, 0))
    exit(err);

  mut_opts |= opt_all;

  if (jobs.empty())
    jobs.push_back(job("-", 1));

  mutate_processor processor;
  if (processor.run())
    return 2;
  return 0;
}
