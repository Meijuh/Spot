// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et
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

#include <string>
#include <iostream>
#include <limits>
#include <set>
#include <memory>

#include <argp.h>
#include "error.h"

#include "common_setup.hh"
#include "common_finput.hh"
#include "common_cout.hh"
#include "common_aoutput.hh"
#include "common_range.hh"
#include "common_post.hh"

#include "tgbaalgos/product.hh"
#include "tgbaalgos/isdet.hh"
#include "tgbaalgos/stutter.hh"
#include "misc/optionmap.hh"
#include "misc/timer.hh"
#include "misc/random.hh"
#include "hoaparse/public.hh"
#include "tgbaalgos/randomize.hh"
#include "tgbaalgos/are_isomorphic.hh"
#include "tgbaalgos/canonicalize.hh"


static const char argp_program_doc[] ="\
Convert, transform, and filter Büchi automata.\v\
Exit status:\n\
  0  if some automata were output\n\
  1  if no automata were output (no match)\n\
  2  if any error has been reported";


#define OPT_TGBA 1
#define OPT_RANDOMIZE 2
#define OPT_SEED 3
#define OPT_PRODUCT 4
#define OPT_MERGE 5
#define OPT_ARE_ISOMORPHIC 6
#define OPT_IS_COMPLETE 7
#define OPT_IS_DETERMINISTIC 8
#define OPT_STATES 9
#define OPT_COUNT 10
#define OPT_EDGES 11
#define OPT_ACC_SETS 12
#define OPT_DESTUT 13
#define OPT_INSTUT 14
#define OPT_IS_EMPTY 15
#define OPT_INTERSECT 16

static const argp_option options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Input:", 1 },
    { "file", 'F', "FILENAME", 0,
      "process the automaton in FILENAME", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Output automaton type:", 2 },
    { "tgba", OPT_TGBA, 0, 0,
      "Transition-based Generalized Büchi Automaton (default)", 0 },
    { "ba", 'B', 0, 0, "Büchi Automaton", 0 },
    { "monitor", 'M', 0, 0, "Monitor (accepts all finite prefixes "
      "of the given property)", 0 },
    /**************************************************/
    { "count", 'c', 0, 0, "print only a count of matched automata", 3 },
    { "max-count", 'n', "NUM", 0, "output at most NUM automata", 3 },
    /**************************************************/
    { 0, 0, 0, 0, "Transformations:", 5 },
    { "merge-transitions", OPT_MERGE, 0, 0,
      "merge transitions with same destination and acceptance", 0 },
    { "product", OPT_PRODUCT, "FILENAME", 0,
      "build the product with FILENAME", 0 },
    { "randomize", OPT_RANDOMIZE, "s|t", OPTION_ARG_OPTIONAL,
      "randomize states and transitions (specify 's' or 't' to "
      "randomize only states or transitions)", 0 },
    { "instut", OPT_INSTUT, "1|2", OPTION_ARG_OPTIONAL,
      "allow more stuttering (two possible algorithms)", 0 },
    { "destut", OPT_DESTUT, 0, 0, "allow less stuttering", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Filters:", 6 },
    { "are-isomorphic", OPT_ARE_ISOMORPHIC, "FILENAME", 0,
      "keep automata that are isomorphic to the automaton in FILENAME", 0 },
    { "isomorphic", 0, 0, OPTION_ALIAS | OPTION_HIDDEN, 0, 0 },
    { "unique", 'u', 0, 0,
      "do not output the same automaton twice (same in the sense that they "\
      "are isomorphic)", 0 },
    { "is-complete", OPT_IS_COMPLETE, 0, 0,
      "the automaton is complete", 0 },
    { "is-deterministic", OPT_IS_DETERMINISTIC, 0, 0,
      "the automaton is deterministic", 0 },
    { "is-empty", OPT_IS_EMPTY, 0, 0,
      "keep automata with an empty language", 0 },
    { "intersect", OPT_INTERSECT, "FILENAME", 0,
      "keep automata whose languages have an non-empty intersection with"
      " the automaton from FILENAME", 0 },
    { "invert-match", 'v', 0, 0, "select non-matching automata", 0 },
    { "states", OPT_STATES, "RANGE", 0,
      "keep automata whose number of states are in RANGE", 0 },
    { "edges", OPT_EDGES, "RANGE", 0,
      "keep automata whose number of edges are in RANGE", 0 },
    { "acc-sets", OPT_ACC_SETS, "RANGE", 0,
      "keep automata whose number of acceptance sets are in RANGE", 0 },
    RANGE_DOC_FULL,
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { "extra-options", 'x', "OPTS", 0,
      "fine-tuning options (see spot-x (7))", 0 },
    { "seed", OPT_SEED, "INT", 0,
      "seed for the random number generator (0)", 0 },
    { 0, 0, 0, 0, 0, 0 }
  };

static const struct argp_child children[] =
  {
    { &aoutput_argp, 0, 0, 0 },
    { &aoutput_io_format_argp, 0, 0, 4 },
    { &post_argp_disabled, 0, 0, 20 },
    { &misc_argp, 0, 0, -1 },
    { 0, 0, 0, 0 }
  };

typedef spot::tgba_digraph::graph_t::trans_storage_t tr_t;
typedef std::set<std::vector<tr_t>> unique_aut_t;
static long int match_count = 0;
static spot::option_map extra_options;
static bool randomize_st = false;
static bool randomize_tr = false;
static int opt_seed = 0;
static auto dict = spot::make_bdd_dict();
static spot::tgba_digraph_ptr opt_product = nullptr;
static spot::tgba_digraph_ptr opt_intersect = nullptr;
static bool opt_merge = false;
static std::unique_ptr<spot::isomorphism_checker>
  isomorphism_checker = nullptr;
static spot::tgba_digraph_ptr opt_are_isomorphic = nullptr;
static bool opt_is_complete = false;
static bool opt_is_deterministic = false;
static bool opt_invert = false;
static range opt_states = { 0, std::numeric_limits<int>::max() };
static range opt_edges = { 0, std::numeric_limits<int>::max() };
static range opt_accsets = { 0, std::numeric_limits<int>::max() };
static int opt_max_count = -1;
static bool opt_destut = false;
static char opt_instut = 0;
static bool opt_is_empty = false;
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

static int
to_pos_int(const char* s)
{
  int res = to_int(s);
  if (res < 0)
    error(2, 0, "%d is not positive", res);
  return res;
}

static spot::tgba_digraph_ptr
read_automaton(const char* filename)
{
  spot::hoa_parse_error_list pel;
  auto p = hoa_parse(filename, pel, dict);
  if (spot::format_hoa_parse_errors(std::cerr, filename, pel)
      || !p || p->aborted)
    error(2, 0, "failed to read automaton from %s", filename);
  return std::move(p->aut);
}

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case 'B':
      type = spot::postprocessor::BA;
      break;
    case 'c':
      automaton_format = Count;
      break;
    case 'F':
      jobs.emplace_back(arg, true);
      break;
    case 'M':
      type = spot::postprocessor::Monitor;
      break;
    case 'n':
      opt_max_count = to_pos_int(arg);
      break;
    case 'u':
      opt_uniq =
        std::unique_ptr<unique_aut_t>(new std::set<std::vector<tr_t>>());
      break;
    case 'v':
      opt_invert = true;
      break;
    case 'x':
      {
	const char* opt = extra_options.parse_options(arg);
	if (opt)
	  error(2, 0, "failed to parse --options near '%s'", opt);
      }
      break;
    case OPT_ACC_SETS:
      opt_accsets = parse_range(arg, 0, std::numeric_limits<int>::max());
      break;
    case OPT_ARE_ISOMORPHIC:
      opt_are_isomorphic = read_automaton(arg);
      break;
    case OPT_EDGES:
      opt_edges = parse_range(arg, 0, std::numeric_limits<int>::max());
      break;
    case OPT_INSTUT:
      if (!arg || (arg[0] == '1' && arg[1] == 0))
	opt_instut = 1;
      else if (arg[0] == '2' && arg[1] == 0)
	opt_instut = 2;
      else
	error(2, 0, "unknown argument for --instut: %s", arg);
      break;
    case OPT_INTERSECT:
      opt_intersect = read_automaton(arg);
      break;
    case OPT_DESTUT:
      opt_destut = true;
      break;
    case OPT_IS_COMPLETE:
      opt_is_complete = true;
      break;
    case OPT_IS_DETERMINISTIC:
      opt_is_deterministic = true;
      break;
    case OPT_IS_EMPTY:
      opt_is_empty = true;
      break;
    case OPT_MERGE:
      opt_merge = true;
      break;
    case OPT_PRODUCT:
      {
	auto a = read_automaton(arg);
	if (!opt_product)
	  opt_product = std::move(a);
	else
	  opt_product = spot::product(std::move(opt_product),
				      std::move(a));
      }
      break;
    case OPT_RANDOMIZE:
      if (arg)
	{
	  for (auto p = arg; *p; ++p)
	    switch (*p)
	      {
	      case 's':
		randomize_st = true;
		break;
	      case 't':
		randomize_tr = true;
		break;
	      default:
		error(2, 0, "unknown argument for --randomize: '%c'", *p);
	      }
	}
      else
	{
	  randomize_tr = true;
	  randomize_st = true;
	}
      break;
    case OPT_SEED:
      opt_seed = to_int(arg);
      break;
    case OPT_STATES:
      opt_states = parse_range(arg, 0, std::numeric_limits<int>::max());
      break;
    case OPT_TGBA:
      if (automaton_format == Spin)
	error(2, 0, "--spin and --tgba are incompatible");
      type = spot::postprocessor::TGBA;
      break;
    case ARGP_KEY_ARG:
      jobs.emplace_back(arg, true);
      break;

    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}


namespace
{
  class hoa_processor: public job_processor
  {
  private:
    spot::postprocessor& post;
    automaton_printer printer;
  public:

    hoa_processor(spot::postprocessor& post)
      : post(post), printer(aut_input)
    {
    }

    int
    process_formula(const spot::ltl::formula*, const char*, int)
    {
      SPOT_UNREACHABLE();
    }

    int
    process_automaton(const spot::const_hoa_aut_ptr& haut,
		      const char* filename)
    {
      spot::stopwatch sw;
      sw.start();

      // If --stats or --name is used, duplicate the automaton so we
      // never modify the original automaton (e.g. with
      // merge_transitions()) and the statistics about it make sense.
      auto aut = ((automaton_format == Stats) || opt_name)
	? spot::make_tgba_digraph(haut->aut, spot::tgba::prop_set::all())
	: haut->aut;

      // Preprocessing.

      if (opt_merge)
	aut->merge_transitions();

      // Filters.

      bool matched = true;

      matched &= opt_states.contains(aut->num_states());
      matched &= opt_edges.contains(aut->num_transitions());
      matched &= opt_accsets.contains(aut->acc().num_sets());
      if (opt_is_complete)
	matched &= is_complete(aut);
      if (opt_is_deterministic)
	matched &= is_deterministic(aut);
      if (opt_are_isomorphic)
        matched &= isomorphism_checker->is_isomorphic(aut);
      if (opt_is_empty)
	matched &= aut->is_empty();
      if (opt_intersect)
	matched &= !spot::product(aut, opt_intersect)->is_empty();

      // Drop or keep matched automata depending on the --invert option
      if (matched == opt_invert)
        return 0;

      ++match_count;

      // Postprocessing.

      if (opt_destut)
	aut = spot::closure(std::move(aut));
      if (opt_instut == 1)
	aut = spot::sl(std::move(aut));
      else if (opt_instut == 2)
	aut = spot::sl2(std::move(aut));

      if (opt_product)
	aut = spot::product(std::move(aut), opt_product);

      aut = post.run(aut, nullptr);

      if (randomize_st || randomize_tr)
	spot::randomize(aut, randomize_st, randomize_tr);

      const double conversion_time = sw.stop();

      if (opt_uniq)
        {
          auto tmp =
	    spot::canonicalize(make_tgba_digraph(aut,
						 spot::tgba::prop_set::all()));
          if (!opt_uniq->emplace(tmp->transition_vector().begin() + 1,
				 tmp->transition_vector().end()).second)
	    return 0;
        }

      printer.print(aut, nullptr, filename, -1, conversion_time, haut);

      if (opt_max_count >= 0 && match_count >= opt_max_count)
	abort_run = true;

      return 0;
    }

    int
    aborted(const spot::const_hoa_aut_ptr& h, const char* filename)
    {
      std::cerr << filename << ':' << h->loc << ": aborted input automaton\n";
      return 2;
    }

    int
    process_file(const char* filename)
    {
      spot::hoa_parse_error_list pel;
      auto hp = spot::hoa_stream_parser(filename);

      int err = 0;

      while (!abort_run)
	{
	  pel.clear();
	  auto haut = hp.parse(pel, dict);
	  if (!haut && pel.empty())
	    break;
	  if (spot::format_hoa_parse_errors(std::cerr, filename, pel))
	    err = 2;
	  if (!haut)
	    error(2, 0, "failed to read automaton from %s", filename);
	  else if (haut->aborted)
	    err = std::max(err, aborted(haut, filename));
	  else
            process_automaton(haut, filename);
	}

      return err;
    }
  };
}

int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, parse_opt, "[FILENAMES...]",
		    argp_program_doc, children, 0, 0 };

  // Disable post-processing as much as possible by default.
  level = spot::postprocessor::Low;
  pref = spot::postprocessor::Any;
  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, 0, 0))
    exit(err);

  if (jobs.empty())
    jobs.emplace_back("-", true);

  if (opt_are_isomorphic)
    {
      if (opt_merge)
        opt_are_isomorphic->merge_transitions();
      isomorphism_checker = std::unique_ptr<spot::isomorphism_checker>(
                            new spot::isomorphism_checker(opt_are_isomorphic));
    }


  spot::srand(opt_seed);

  spot::postprocessor post(&extra_options);
  post.set_pref(pref | comp);
  post.set_type(type);
  post.set_level(level);

  hoa_processor processor(post);
  try
    {
      if (processor.run())
	return 2;
    }
  catch (const std::runtime_error& e)
    {
      error(2, 0, "%s", e.what());
    }

  if (automaton_format == Count)
    std::cout << match_count << std::endl;
  return !match_count;
}
