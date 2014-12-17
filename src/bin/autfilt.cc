// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014 Laboratoire de Recherche et Développement
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

#include "common_sys.hh"

#include <string>
#include <iostream>
#include <limits>

#include <argp.h>
#include "error.h"

#include "common_setup.hh"
#include "common_finput.hh"
#include "common_cout.hh"
#include "common_range.hh"
#include "common_post.hh"

#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/lbtt.hh"
#include "tgbaalgos/hoa.hh"
#include "tgbaalgos/neverclaim.hh"
#include "tgbaalgos/product.hh"
#include "tgbaalgos/save.hh"
#include "tgbaalgos/stats.hh"
#include "tgbaalgos/isdet.hh"
#include "tgba/bddprint.hh"
#include "misc/optionmap.hh"
#include "misc/timer.hh"
#include "misc/random.hh"
#include "hoaparse/public.hh"
#include "tgbaalgos/sccinfo.hh"
#include "tgbaalgos/randomize.hh"
#include "tgbaalgos/are_isomorphic.hh"


static const char argp_program_doc[] ="\
Convert, transform, and filter Büchi automata.\v\
Exit status:\n\
  0  if some automata were output\n\
  1  if no automata were output (no match)\n\
  2  if any error has been reported";


#define OPT_TGBA 1
#define OPT_DOT 2
#define OPT_LBTT 3
#define OPT_SPOT 4
#define OPT_STATS 5
#define OPT_RANDOMIZE 6
#define OPT_SEED 7
#define OPT_PRODUCT 8
#define OPT_MERGE 9
#define OPT_ARE_ISOMORPHIC 10
#define OPT_IS_COMPLETE 11
#define OPT_IS_DETERMINISTIC 12
#define OPT_STATES 17
#define OPT_COUNT 18
#define OPT_NAME 19
#define OPT_EDGES 20
#define OPT_ACC_SETS 21

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
    { 0, 0, 0, 0, "Output format:", 3 },
    { "count", 'c', 0, 0, "print only a count of matched automata", 0 },
    { "dot", OPT_DOT, 0, 0, "GraphViz's format (default)", 0 },
    { "hoaf", 'H', "s|t|m|l", OPTION_ARG_OPTIONAL,
      "Output the automaton in HOA format.  Add letters to select "
      "(s) state-based acceptance, (t) transition-based acceptance, "
      "(m) mixed acceptance, (l) single-line output", 0 },
    { "lbtt", OPT_LBTT, "t", OPTION_ARG_OPTIONAL,
      "LBTT's format (add =t to force transition-based acceptance even"
      " on Büchi automata)", 0 },
    { "max-count", 'n', "NUM", 0,
      "output at most NUM automata", 0 },
    { "name", OPT_NAME, "FORMAT", OPTION_ARG_OPTIONAL,
      "set the name of the output automaton (default: %M)", 0 },
    { "quiet", 'q', 0, 0, "suppress all normal output", 0 },
    { "spin", 's', 0, 0, "Spin neverclaim (implies --ba)", 0 },
    { "spot", OPT_SPOT, 0, 0, "SPOT's format", 0 },
    { "utf8", '8', 0, 0, "enable UTF-8 characters in output "
      "(ignored with --lbtt or --spin)", 0 },
    { "stats", OPT_STATS, "FORMAT", 0,
      "output statistics about the automaton", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "The FORMAT string passed to --stats may use "\
      "the following interpreted sequences (capitals for input,"
      " minuscules for output):", 4 },
    { "%F", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "name of the input file", 0 },
    { "%L", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "location in the input file", 0 },
    { "%M, %m", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "name of the automaton (as specified in the HOA format)", 0 },
    { "%S, %s", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of states", 0 },
    { "%E, %e", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of edges", 0 },
    { "%T, %t", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of transitions", 0 },
    { "%A, %a", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of acceptance pairs or sets", 0 },
    { "%C, %c", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of SCCs", 0 },
    { "%n", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of nondeterministic states in output", 0 },
    { "%d", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "1 if the output is deterministic, 0 otherwise", 0 },
    { "%p", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "1 if the output is complete, 0 otherwise", 0 },
    { "%r", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "processing time (excluding parsing) in seconds", 0 },
    { "%%", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "a single %", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Transformations:", 5 },
    { "merge-transitions", OPT_MERGE, 0, 0,
      "merge transitions with same destination and acceptance", 0 },
    { "product", OPT_PRODUCT, "FILENAME", 0,
      "build the product with FILENAME", 0 },
    { "randomize", OPT_RANDOMIZE, "s|t", OPTION_ARG_OPTIONAL,
      "randomize states and transitions (specify 's' or 't' to "
      "randomize only states or transitions)", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Filters:", 6 },
    { "are-isomorphic", OPT_ARE_ISOMORPHIC, "FILENAME", 0,
      "keep automata that are isomorphic to the automaton in FILENAME", 0 },
    { "isomorphic", 0, 0, OPTION_ALIAS | OPTION_HIDDEN, 0, 0 },
    { "is-complete", OPT_IS_COMPLETE, 0, 0,
      "the automaton is complete", 0 },
    { "is-deterministic", OPT_IS_DETERMINISTIC, 0, 0,
      "the automaton is deterministic", 0 },
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
    { &post_argp_disabled, 0, 0, 20 },
    { &misc_argp, 0, 0, -1 },
    { 0, 0, 0, 0 }
  };

static enum output_format { Dot, Lbtt, Lbtt_t, Spin, Spot, Stats, Hoa,
			    Quiet, Count } format = Dot;
static long int match_count = 0;
static const char* stats = "";
static const char* hoa_opt = 0;
static spot::option_map extra_options;
static bool randomize_st = false;
static bool randomize_tr = false;
static int opt_seed = 0;
static auto dict = spot::make_bdd_dict();
static spot::tgba_digraph_ptr opt_product = nullptr;
static bool opt_merge = false;
static spot::tgba_digraph_ptr opt_are_isomorphic = nullptr;
static bool opt_is_complete = false;
static bool opt_is_deterministic = false;
static bool opt_invert = false;
static range opt_states = { 0, std::numeric_limits<int>::max() };
static range opt_edges = { 0, std::numeric_limits<int>::max() };
static range opt_accsets = { 0, std::numeric_limits<int>::max() };
static const char* opt_name = nullptr;
static int opt_max_count = -1;

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

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case '8':
      spot::enable_utf8();
      break;
    case 'B':
      type = spot::postprocessor::BA;
      break;
    case 'c':
      format = Count;
      break;
    case 'F':
      jobs.emplace_back(arg, true);
      break;
    case 'H':
      format = Hoa;
      hoa_opt = arg;
      break;
    case 'M':
      type = spot::postprocessor::Monitor;
      break;
    case 'n':
      opt_max_count = to_pos_int(arg);
      break;
    case 'q':
      format = Quiet;
      break;
    case 's':
      format = Spin;
      if (type != spot::postprocessor::Monitor)
	type = spot::postprocessor::BA;
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
    case OPT_DOT:
      format = Dot;
      break;
    case OPT_ACC_SETS:
      opt_accsets = parse_range(arg, 0, std::numeric_limits<int>::max());
      break;
    case OPT_ARE_ISOMORPHIC:
      {
	spot::hoa_parse_error_list pel;
	auto p = hoa_parse(arg, pel, dict);
	if (spot::format_hoa_parse_errors(std::cerr, arg, pel)
	    || !p || p->aborted)
	  error(2, 0, "failed to read automaton from %s", arg);
        opt_are_isomorphic = std::move(p->aut);
	break;
      }
    case OPT_EDGES:
      opt_edges = parse_range(arg, 0, std::numeric_limits<int>::max());
      break;
    case OPT_IS_COMPLETE:
      opt_is_complete = true;
      break;
    case OPT_IS_DETERMINISTIC:
      opt_is_deterministic = true;
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
    case OPT_NAME:
      if (arg)
	opt_name = arg;
      else
	opt_name = "%M";
    case OPT_MERGE:
      opt_merge = true;
      break;
    case OPT_PRODUCT:
      {
	spot::hoa_parse_error_list pel;
	auto p = hoa_parse(arg, pel, dict);
	if (spot::format_hoa_parse_errors(std::cerr, arg, pel)
	    || !p || p->aborted)
	  error(2, 0, "failed to read automaton from %s", arg);
	if (!opt_product)
	  opt_product = std::move(p->aut);
	else
	  opt_product = spot::product(std::move(opt_product),
				      std::move(p->aut));
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
    case OPT_SPOT:
      format = Spot;
      break;
    case OPT_STATES:
      opt_states = parse_range(arg, 0, std::numeric_limits<int>::max());
      break;
    case OPT_STATS:
      if (!*arg)
	error(2, 0, "empty format string for --stats");
      stats = arg;
      format = Stats;
      break;
    case OPT_TGBA:
      if (format == Spin)
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
  /// \brief prints various statistics about a TGBA
  ///
  /// This object can be configured to display various statistics
  /// about a TGBA.  Some %-sequence of characters are interpreted in
  /// the format string, and replaced by the corresponding statistics.
  class hoa_stat_printer: protected spot::stat_printer
  {
  public:
    hoa_stat_printer(std::ostream& os, const char* format)
      : spot::stat_printer(os, format)
    {
      declare('A', &haut_acc_);
      declare('C', &haut_scc_);
      declare('E', &haut_edges_);
      declare('F', &filename_);
      declare('f', &filename_);	// Override the formula printer.
      declare('L', &haut_loc_);
      declare('M', &haut_name_);
      declare('m', &aut_name_);
      declare('S', &haut_states_);
      declare('T', &haut_trans_);
    }

    /// \brief print the configured statistics.
    ///
    /// The \a f argument is not needed if the Formula does not need
    /// to be output.
    std::ostream&
    print(const spot::const_hoa_aut_ptr& haut,
	  const spot::const_tgba_digraph_ptr& aut,
	  const char* filename, double run_time)
    {
      filename_ = filename;
      haut_loc_ = haut->loc;

      if (has('T'))
	{
	  spot::tgba_sub_statistics s = sub_stats_reachable(haut->aut);
	  haut_states_ = s.states;
	  haut_edges_ = s.transitions;
	  haut_trans_ = s.sub_transitions;
	}
      else if (has('E'))
	{
	  spot::tgba_sub_statistics s = sub_stats_reachable(haut->aut);
	  haut_states_ = s.states;
	  haut_edges_ = s.transitions;
	}
      if (has('M'))
	{
	  auto n = haut->aut->get_named_prop<std::string>("automaton-name");
	  if (n)
	    haut_name_ = *n;
	  else
	    haut_name_.val().clear();
	}
      if (has('m'))
	{
	  auto n = aut->get_named_prop<std::string>("automaton-name");
	  if (n)
	    aut_name_ = *n;
	  else
	    aut_name_.val().clear();
	}
      if (has('S'))
	{
	  haut_states_ = haut->aut->num_states();
	}

      if (has('A'))
	haut_acc_ = haut->aut->acc().num_sets();

      if (has('C'))
	haut_scc_ = spot::scc_info(haut->aut).scc_count();

      return this->spot::stat_printer::print(aut, 0, run_time);
    }

  private:
    spot::printable_value<const char*> filename_;
    spot::printable_value<std::string> haut_name_;
    spot::printable_value<std::string> aut_name_;
    spot::printable_value<unsigned> haut_states_;
    spot::printable_value<unsigned> haut_edges_;
    spot::printable_value<unsigned> haut_trans_;
    spot::printable_value<unsigned> haut_acc_;
    spot::printable_value<unsigned> haut_scc_;
    spot::printable_value<spot::location> haut_loc_;
  };

  class hoa_processor: public job_processor
  {
  private:
    spot::postprocessor& post;
    hoa_stat_printer statistics;
    std::ostringstream name;
    hoa_stat_printer namer;
  public:

    hoa_processor(spot::postprocessor& post)
      : post(post), statistics(std::cout, stats), namer(name, opt_name)
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
      auto aut = ((format == Stats) || opt_name) ?
	spot::make_tgba_digraph(haut->aut) : haut->aut;

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
        matched &= !are_isomorphic(aut, opt_are_isomorphic).empty();

      // Drop or keep matched automata depending on the --invert option
      if (matched == opt_invert)
        return 0;

      ++match_count;

      // Postprocessing.

      if (opt_product)
	aut = spot::product(std::move(aut), opt_product);

      aut = post.run(aut, nullptr);

      if (randomize_st || randomize_tr)
	spot::randomize(aut, randomize_st, randomize_tr);

      const double conversion_time = sw.stop();

      // Name the output automaton.
      if (opt_name)
	{
	  name.str("");
	  namer.print(haut, aut, filename, conversion_time);
	  aut->set_named_prop("automaton-name", new std::string(name.str()));
	}

      // Output it.
      switch (format)
	{
	case Count:
	case Quiet:
	  // Do not output anything.
	  break;
	case Dot:
	  spot::dotty_reachable(std::cout, aut,
				(type == spot::postprocessor::BA)
				|| (type == spot::postprocessor::Monitor));
	  break;
	case Lbtt:
	  spot::lbtt_reachable(std::cout, aut, type == spot::postprocessor::BA);
	  break;
	case Lbtt_t:
	  spot::lbtt_reachable(std::cout, aut, false);
	  break;
	case Hoa:
	  spot::hoa_reachable(std::cout, aut, hoa_opt) << '\n';
	  break;
	case Spot:
	  spot::tgba_save_reachable(std::cout, aut);
	  break;
	case Spin:
	  spot::never_claim_reachable(std::cout, aut);
	  break;
	case Stats:
	  statistics.print(haut, aut, filename, conversion_time) << '\n';
	  break;
	}
      flush_cout();

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

  if (opt_are_isomorphic && opt_merge)
    opt_are_isomorphic->merge_transitions();

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

  if (format == Count)
    std::cout << match_count << std::endl;
  return !match_count;
}
