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

#include <string>
#include <iostream>
#include <sstream>
#include <cstdlib>
#include <cstdio>
#include <argp.h>
#include <unistd.h>
#include <cmath>
#include <sys/wait.h>
#include "error.h"
#include "argmatch.h"

#include "common_setup.hh"
#include "common_cout.hh"
#include "common_conv.hh"
#include "common_trans.hh"
#include "common_file.hh"
#include "common_finput.hh"
#include "parseaut/public.hh"
#include "ltlast/unop.hh"
#include "ltlvisit/print.hh"
#include "ltlvisit/apcollect.hh"
#include "ltlvisit/mutation.hh"
#include "ltlvisit/relabel.hh"
#include "twaalgos/lbtt.hh"
#include "twaalgos/hoa.hh"
#include "twaalgos/product.hh"
#include "twaalgos/remfin.hh"
#include "twaalgos/gtec/gtec.hh"
#include "twaalgos/randomgraph.hh"
#include "twaalgos/sccinfo.hh"
#include "twaalgos/isweakscc.hh"
#include "twaalgos/reducerun.hh"
#include "twaalgos/word.hh"
#include "twaalgos/dtgbacomp.hh"
#include "twaalgos/cleanacc.hh"
#include "misc/formater.hh"
#include "twaalgos/stats.hh"
#include "twaalgos/isdet.hh"
#include "twaalgos/isunamb.hh"
#include "misc/escape.hh"
#include "misc/hash.hh"
#include "misc/random.hh"
#include "misc/tmpfile.hh"
#include "misc/timer.hh"

const char argp_program_doc[] ="\
Call several LTL/PSL translators and cross-compare their output to detect \
bugs, or to gather statistics.  The list of formulas to use should be \
supplied on standard input, or using the -f or -F options.\v\
Exit status:\n\
  0  everything went fine (timeouts are OK too)\n\
  1  some translator failed to output something we understand, or failed\n\
     sanity checks (statistics were output nonetheless)\n\
  2  ltlcross aborted on error\n\
";

enum {
  OPT_AUTOMATA = 256,
  OPT_BOGUS,
  OPT_COLOR,
  OPT_CSV,
  OPT_DENSITY,
  OPT_DUPS,
  OPT_GRIND,
  OPT_IGNORE_EXEC_FAIL,
  OPT_JSON,
  OPT_NOCHECKS,
  OPT_NOCOMP,
  OPT_OMIT,
  OPT_PRODUCTS,
  OPT_SEED,
  OPT_STATES,
  OPT_STOP_ERR,
  OPT_VERBOSE,
};

static const argp_option options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "ltlcross behavior:", 5 },
    { "allow-dups", OPT_DUPS, 0, 0,
      "translate duplicate formulas in input", 0 },
    { "no-checks", OPT_NOCHECKS, 0, 0,
      "do not perform any sanity checks (negated formulas "
      "will not be translated)", 0 },
    { "no-complement", OPT_NOCOMP, 0, 0,
      "do not complement deterministic automata to perform extra checks", 0 },
    { "stop-on-error", OPT_STOP_ERR, 0, 0,
      "stop on first execution error or failure to pass"
      " sanity checks (timeouts are OK)", 0 },
    { "ignore-execution-failures", OPT_IGNORE_EXEC_FAIL, 0, 0,
      "ignore automata from translators that return with a non-zero exit code,"
      " but do not flag this as an error", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "State-space generation:", 6 },
    { "states", OPT_STATES, "INT", 0,
      "number of the states in the state-spaces (200 by default)", 0 },
    { "density", OPT_DENSITY, "FLOAT", 0,
      "probability, between 0.0 and 1.0, to add a transition between "
      "two states (0.1 by default)", 0 },
    { "seed", OPT_SEED, "INT", 0,
      "seed for the random number generator (0 by default)", 0 },
    { "products", OPT_PRODUCTS, "[+]INT", 0,
      "number of products to perform (1 by default), statistics will be "
      "averaged unless the number is prefixed with '+'", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Statistics output:", 7 },
    { "json", OPT_JSON, "[>>]FILENAME", OPTION_ARG_OPTIONAL,
      "output statistics as JSON in FILENAME or on standard output", 0 },
    { "csv", OPT_CSV, "[>>]FILENAME", OPTION_ARG_OPTIONAL,
      "output statistics as CSV in FILENAME or on standard output "
      "(if '>>' is used to request append mode, the header line is "
      "not output)", 0 },
    { "omit-missing", OPT_OMIT, 0, 0,
      "do not output statistics for timeouts or failed translations", 0 },
    { "automata", OPT_AUTOMATA, 0, 0,
      "store automata (in the HOA format) into the CSV or JSON output", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -2 },
    { "color", OPT_COLOR, "WHEN", OPTION_ARG_OPTIONAL,
      "colorize output; WHEN can be 'never', 'always' (the default if "
      "--color is used without argument), or "
      "'auto' (the default if --color is not used)", 0 },
    { "grind", OPT_GRIND, "[>>]FILENAME", 0,
      "for each formula for which a problem was detected, write a simpler " \
      "formula that fails on the same test in FILENAME", 0 },
    { "save-bogus", OPT_BOGUS, "[>>]FILENAME", 0,
      "save formulas for which problems were detected in FILENAME", 0 },
    { "verbose", OPT_VERBOSE, 0, 0,
      "print what is being done, for debugging", 0 },
    { 0, 0, 0, 0, "If an output FILENAME is prefixed with '>>', is it open "
      "in append mode instead of being truncated.", -1 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp_child children[] =
  {
    { &finput_argp, 0, 0, 1 },
    { &trans_argp, 0, 0, 0 },
    { &misc_argp, 0, 0, -2 },
    { 0, 0, 0, 0 }
  };

enum color_type { color_never, color_always, color_if_tty };

static char const *const color_args[] =
{
  "always", "yes", "force",
  "never", "no", "none",
  "auto", "tty", "if-tty", 0
};
static color_type const color_types[] =
{
  color_always, color_always, color_always,
  color_never, color_never, color_never,
  color_if_tty, color_if_tty, color_if_tty
};
ARGMATCH_VERIFY(color_args, color_types);

static color_type color_opt = color_if_tty;
static const char* bright_red = "\033[01;31m";
static const char* bright_blue = "\033[01;34m";
static const char* bright_yellow = "\033[01;33m";
static const char* reset_color = "\033[m";

static unsigned states = 200;
static float density = 0.1;
static const char* json_output = 0;
static const char* csv_output = 0;
static bool want_stats = false;
static bool allow_dups = false;
static bool no_checks = false;
static bool no_complement = false;
static bool stop_on_error = false;
static int seed = 0;
static unsigned products = 1;
static bool products_avg = true;
static bool opt_omit = false;
static const char* bogus_output_filename = 0;
static output_file* bogus_output = 0;
static output_file* grind_output = 0;
static bool verbose = false;
static bool ignore_exec_fail = false;
static unsigned ignored_exec_fail = 0;
static bool opt_automata = false;

static bool global_error_flag = false;
static unsigned oom_count = 0U;

static std::ostream&
global_error()
{
  global_error_flag = true;
  if (color_opt)
    std::cerr << bright_red;
  return std::cerr;
}

static std::ostream&
example()
{
  if (color_opt)
    std::cerr << bright_yellow;
  return std::cerr;
}


static void
end_error()
{
  if (color_opt)
    std::cerr << reset_color;
}


struct statistics
{
  statistics()
    : ok(false),
      status_str(0),
      status_code(0),
      time(0),
      states(0),
      edges(0),
      transitions(0),
      acc(0),
      scc(0),
      nonacc_scc(0),
      terminal_scc(0),
      weak_scc(0),
      strong_scc(0),
      nondetstates(0),
      nondeterministic(false),
      terminal_aut(false),
      weak_aut(false),
      strong_aut(false)
  {
  }

  // If OK is false, only the status_str, status_code, and time fields
  // should be valid.
  bool ok;
  const char* status_str;
  int status_code;
  double time;
  unsigned states;
  unsigned edges;
  unsigned transitions;
  unsigned acc;
  unsigned scc;
  unsigned nonacc_scc;
  unsigned terminal_scc;
  unsigned weak_scc;
  unsigned strong_scc;
  unsigned nondetstates;
  bool nondeterministic;
  bool terminal_aut;
  bool weak_aut;
  bool strong_aut;
  std::vector<double> product_states;
  std::vector<double> product_transitions;
  std::vector<double> product_scc;
  bool ambiguous;
  bool complete;
  std::string hoa_str;

  static void
  fields(std::ostream& os, bool show_exit)
  {
    if (show_exit)
      os << "\"exit_status\",\"exit_code\",";
    os << ("\"time\","
	   "\"states\","
	   "\"edges\","
	   "\"transitions\","
	   "\"acc\","
	   "\"scc\","
	   "\"nonacc_scc\","
	   "\"terminal_scc\","
	   "\"weak_scc\","
	   "\"strong_scc\","
	   "\"nondet_states\","
	   "\"nondet_aut\","
	   "\"terminal_aut\","
	   "\"weak_aut\","
	   "\"strong_aut\","
	   "\"ambiguous_aut\","
	   "\"complete_aut\"");
    size_t m = products_avg ? 1U : products;
    for (size_t i = 0; i < m; ++i)
      os << ",\"product_states\",\"product_transitions\",\"product_scc\"";
    if (opt_automata)
      os << ",\"automaton\"";
  }

  void
  to_csv(std::ostream& os, bool show_exit, const char* na = "",
	 bool csv_escape = true)
  {
    if (show_exit)
      os << '"' << status_str << "\"," << status_code << ',';
    os << time << ',';
    if (ok)
      {
	os << states << ','
	   << edges << ','
	   << transitions << ','
	   << acc << ','
	   << scc << ','
	   << nonacc_scc << ','
	   << terminal_scc << ','
	   << weak_scc << ','
	   << strong_scc << ','
	   << nondetstates << ','
	   << nondeterministic << ','
	   << terminal_aut << ','
	   << weak_aut << ','
	   << strong_aut << ','
	   << ambiguous << ','
	   << complete;
	if (!products_avg)
	  {
	    for (size_t i = 0; i < products; ++i)
	      os << ',' << product_states[i]
		 << ',' << product_transitions[i]
		 << ',' << product_scc[i];
	  }
	else
	  {
	    double st = 0.0;
	    double tr = 0.0;
	    double sc = 0.0;
	    for (size_t i = 0; i < products; ++i)
	      {
		st += product_states[i];
		tr += product_transitions[i];
		sc += product_scc[i];
	      }
	    os << ',' << (st / products)
	       << ',' << (tr / products)
	       << ',' << (sc / products);
	  }
      }
    else
      {
	size_t m = products_avg ? 1U : products;
	m *= 3;
	m += 15;
	os << na;
	for (size_t i = 0; i < m; ++i)
	  os << ',' << na;
      }
    if (opt_automata)
      {
	os << ',';
	if (hoa_str.empty())
	  os << na;
	else if (csv_escape)
	  spot::escape_rfc4180(os << '"', hoa_str) << '"';
	else
	  spot::escape_str(os << '"', hoa_str) << '"';
      }
  }
};

typedef std::vector<statistics> statistics_formula;
typedef std::vector<statistics_formula> statistics_vector;
statistics_vector vstats;
std::vector<std::string> formulas;

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case ARGP_KEY_ARG:
      translators.push_back(arg);
      break;
    case OPT_AUTOMATA:
      opt_automata = true;
      break;
    case OPT_BOGUS:
      {
	bogus_output = new output_file(arg);
	bogus_output_filename = arg;
	break;
      }
    case OPT_COLOR:
      {
	if (arg)
	  color_opt = XARGMATCH("--color", arg, color_args, color_types);
	else
	  color_opt = color_always;
	break;
      }
    case OPT_CSV:
      want_stats = true;
      csv_output = arg ? arg : "-";
      break;
    case OPT_DENSITY:
      density = to_probability(arg);
      break;
    case OPT_DUPS:
      allow_dups = true;
      break;
    case OPT_GRIND:
      grind_output = new output_file(arg);
      break;
    case OPT_IGNORE_EXEC_FAIL:
      ignore_exec_fail = true;
      break;
    case OPT_JSON:
      want_stats = true;
      json_output = arg ? arg : "-";
      break;
    case OPT_PRODUCTS:
      if (*arg == '+')
	{
	  products_avg = false;
	  ++arg;
	}
      products = to_pos_int(arg);
      break;
    case OPT_NOCHECKS:
      no_checks = true;
      no_complement = true;
      break;
    case OPT_NOCOMP:
      no_complement = true;
      break;
    case OPT_OMIT:
      opt_omit = true;
      break;
    case OPT_SEED:
      seed = to_pos_int(arg);
      break;
    case OPT_STATES:
      states = to_pos_int(arg);
      break;
    case OPT_STOP_ERR:
      stop_on_error = true;
      break;
    case OPT_VERBOSE:
      verbose = true;
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

namespace
{
  class xtranslator_runner: public translator_runner
  {
  public:
    xtranslator_runner(spot::bdd_dict_ptr dict)
      : translator_runner(dict)
    {
    }

    spot::twa_graph_ptr
    translate(unsigned int translator_num, char l, statistics_formula* fstats,
	      bool& problem)
    {
      output.reset(translator_num);

      std::ostringstream command;
      format(command, translators[translator_num].cmd);

      std::string cmd = command.str();
      std::cerr << "Running [" << l << translator_num << "]: "
		<< cmd << std::endl;
      spot::stopwatch sw;
      sw.start();
      int es = exec_with_timeout(cmd.c_str());
      double duration = sw.stop();

      const char* status_str = 0;

      spot::twa_graph_ptr res = 0;
      if (timed_out)
	{
	  // This is not considered to be a global error.
	  std::cerr << "warning: timeout during execution of command\n";
	  ++timeout_count;
	  status_str = "timeout";
	  problem = false;	// A timeout is not a sign of a bug
	  es = -1;
	}
      else if (WIFSIGNALED(es))
	{
	  status_str = "signal";
	  problem = true;
	  es = WTERMSIG(es);
	  global_error() << "error: execution terminated by signal "
			 << es << ".\n";
	  end_error();
	}
      else if (WIFEXITED(es) && WEXITSTATUS(es) != 0)
	{
	  es = WEXITSTATUS(es);
	  status_str = "exit code";
	  if (!ignore_exec_fail)
	    {
	      problem = true;
	      global_error() << "error: execution returned exit code "
			     << es << ".\n";
	      end_error();
	    }
	  else
	    {
	      problem = false;
	      std::cerr << "warning: execution returned exit code "
			<< es << ".\n";
	      ++ignored_exec_fail;
	    }
	}
      else
	{
	  status_str = "ok";
	  problem = false;
	  es = 0;

	  spot::parse_aut_error_list pel;
	  std::string filename = output.val()->name();
	  auto aut = spot::parse_aut(filename, pel, dict);
	  if (!pel.empty())
	    {
	      status_str = "parse error";
	      problem = true;
	      es = -1;
	      std::ostream& err = global_error();
	      err << "error: failed to parse the produced automaton.\n";
	      spot::format_parse_aut_errors(err, filename, pel);
	      end_error();
	      res = nullptr;
	    }
	  else if (!aut)
	    {
	      status_str = "empty output";
	      problem = true;
	      es = -1;
	      global_error() << "error: empty output.\n";
	      end_error();
	      res = nullptr;
	    }
	  else if (aut->aborted)
	    {
	      status_str = "aborted";
	      problem = true;
	      es = -1;
	      global_error()  << "error: aborted HOA file.\n";
	      end_error();
	      res = nullptr;
	    }
	  else
	    {
	      res = aut->aut;
	    }
	}

      if (want_stats)
	{
	  statistics* st = &(*fstats)[translator_num];
	  st->status_str = status_str;
	  st->status_code = es;
	  st->time = duration;

	  // Compute statistics.
	  if (res)
	    {
	      if (verbose)
		std::cerr << "info: getting statistics\n";
	      st->ok = true;
	      spot::tgba_sub_statistics s = sub_stats_reachable(res);
	      st->states = s.states;
	      st->edges = s.transitions;
	      st->transitions = s.sub_transitions;
	      st->acc = res->acc().num_sets();
	      spot::scc_info m(res);
	      unsigned c = m.scc_count();
	      st->scc = c;
	      st->nondetstates = spot::count_nondet_states(res);
	      st->nondeterministic = st->nondetstates != 0;
	      for (unsigned n = 0; n < c; ++n)
		{
		  if (m.is_rejecting_scc(n))
		    ++st->nonacc_scc;
		  else if (is_terminal_scc(m, n))
		    ++st->terminal_scc;
		  else if (is_weak_scc(m, n))
		    ++st->weak_scc;
		  else
		    ++st->strong_scc;
		}
	      if (st->strong_scc)
		st->strong_aut = true;
	      else if (st->weak_scc)
		st->weak_aut = true;
	      else
		st->terminal_aut = true;
	      st->ambiguous = !spot::is_unambiguous(res);
	      st->complete = spot::is_complete(res);

	      if (opt_automata)
		{
		  std::ostringstream os;
		  spot::print_hoa(os, res, "l");
		  st->hoa_str = os.str();
		}
	    }
	}
      output.cleanup();
      return res;
    }
  };

  static bool
  check_empty_prod(const spot::const_twa_graph_ptr& aut_i,
		   const spot::const_twa_graph_ptr& aut_j,
		   size_t i, size_t j, bool icomp, bool jcomp)
  {
    if (aut_i->num_sets() + aut_j->num_sets()
	> 8 * sizeof(spot::acc_cond::mark_t::value_t))
      {
	// Report the skipped test if both automata are not
	// complemented, or the --verbose option is used,
	if (!verbose && (icomp || jcomp))
	  return false;
	std::cerr << "info: building ";
	if (icomp)
	  std::cerr << "Comp(N" << i << ')';
	else
	  std::cerr << 'P' << i;
	if (jcomp)
	  std::cerr << "*Comp(P" << j << ')';
	else
	  std::cerr << "*N" << j;
	std::cerr << " requires more acceptance sets than supported\n";
	return false;
      }

    auto prod = spot::product(aut_i, aut_j);

    if (verbose)
      {
	std::cerr << "info: check_empty ";
	if (icomp)
	  std::cerr << "Comp(N" << i << ')';
	else
	  std::cerr << 'P' << i;
	if (jcomp)
	  std::cerr << "*Comp(P" << j << ')';
	else
	  std::cerr << "*N" << j;
	std::cerr << '\n';
      }

    auto res = spot::couvreur99(prod)->check();
    if (res)
      {
	std::ostream& err = global_error();
	err << "error: ";
	if (icomp)
	  err << "Comp(N" << i << ')';
	else
	  err << 'P' << i;
	if (jcomp)
	  err << "*Comp(P" << j << ')';
	else
	  err << "*N" << j;
	err << " is nonempty";

	auto run = res->accepting_run();
	if (run)
	  {
	    run = reduce_run(prod, run);
	    std::cerr << "; both automata accept the infinite word\n"
		      << "       ";
	    spot::tgba_word w(run);
	    w.simplify();
	    w.print(example(), prod->get_dict()) << '\n';
	  }
	else
	  {
	    std::cerr << '\n';
	  }
	end_error();
      }
    return !!res;
  }

  static bool
  cross_check(const std::vector<spot::scc_info*>& maps, char l, unsigned p)
  {
    size_t m = maps.size();
    if (verbose)
      {
	std::cerr << "info: cross_check {";
	bool first = true;
	for (size_t i = 0; i < m; ++i)
	  if (maps[i])
	    {
	      if (first)
		first = false;
	      else
		std::cerr << ',';
	      std::cerr << l << i;
	    }
	std::cerr << "}, state-space #" << p << '/' << products << '\n';
      }

    std::vector<bool> res(m);
    unsigned verified = 0;
    unsigned violated = 0;
    for (size_t i = 0; i < m; ++i)
      if (spot::scc_info* m = maps[i])
	{
	  // r == true iff the automaton i is accepting.
	  bool r = false;
	  for (auto& scc: *m)
	    if (scc.is_accepting())
	      {
		r = true;
		break;
	      }
	  res[i] = r;
	  if (r)
	    ++verified;
	  else
	    ++violated;
	}
    if (verified != 0 && violated != 0)
      {
	std::ostream& err = global_error();
	err << "error: {";
	bool first = true;
	for (size_t i = 0; i < m; ++i)
	  if (maps[i] && res[i])
	    {
	      if (first)
		first = false;
	      else
		err << ',';
	      err << l << i;
	    }
	err << "} disagree with {";
	first = true;
	for (size_t i = 0; i < m; ++i)
	  if (maps[i] && !res[i])
	    {
	      if (first)
		first = false;
	      else
		err << ',';
	      err << l << i;
	    }
	err << "} when evaluating ";
	if (products > 1)
	  err << "state-space #" << p << '/' << products << '\n';
	else
	  err << "the state-space\n";
	end_error();
	return true;
      }
    return false;
  }

  typedef std::set<unsigned> state_set;

  // Collect all the states of SSPACE that appear in the accepting SCCs
  // of PROD.  (Trivial SCCs are considered accepting.)
  static void
  states_in_acc(const spot::scc_info* m, state_set& s)
  {
    auto aut = m->get_aut();
    auto ps = aut->get_named_prop<const spot::product_states>("product-states");
    for (auto& scc: *m)
      if (scc.is_accepting() || scc.is_trivial())
	for (auto i: scc.states())
	  // Get the projection on sspace.
	  s.insert((*ps)[i].second);
  }

  static bool
  consistency_check(const spot::scc_info* pos, const spot::scc_info* neg)
  {
    // the states of SSPACE should appear in the accepting SCC of at
    // least one of POS or NEG.  Maybe both.
    state_set s;
    states_in_acc(pos, s);
    states_in_acc(neg, s);
    return s.size() == states;
  }

  typedef
  std::unordered_set<const spot::ltl::formula*,
		     const spot::ptr_hash<const spot::ltl::formula> > fset_t;


  class processor: public job_processor
  {
    spot::bdd_dict_ptr dict = spot::make_bdd_dict();
    xtranslator_runner runner;
    fset_t unique_set;
  public:
    processor():
      runner(dict)
    {
    }

    ~processor()
    {
      fset_t::iterator i = unique_set.begin();
      while (i != unique_set.end())
	(*i++)->destroy();
    }

    int
    process_string(const std::string& input,
		   const char* filename,
		   int linenum)
    {
      spot::ltl::parse_error_list pel;
      const spot::ltl::formula* f = parse_formula(input, pel);

      if (!f || !pel.empty())
	{
	  if (filename)
	    error_at_line(0, 0, filename, linenum, "parse error:");
	  spot::ltl::format_parse_errors(std::cerr, input, pel);
	  if (f)
	    f->destroy();
	  return 1;
	}

      f->clone();
      int res = process_formula(f, filename, linenum);

      if (res && bogus_output)
	bogus_output->ostream() << input << std::endl;
      if (res && grind_output)
	{
	  std::string bogus = input;
	  std::vector<const spot::ltl::formula*> mutations;
	  unsigned mutation_count;
	  unsigned mutation_max;
	  while	(res)
	    {
	      std::cerr << "Trying to find a bogus mutation of ";
	      if (color_opt)
		std::cerr << bright_blue;
	      std::cerr << bogus;
	      if (color_opt)
		std::cerr << reset_color;
	      std::cerr << "...\n";

	      mutations = mutate(f);
	      mutation_count = 1;
	      mutation_max = mutations.size();
	      res = 0;
	      for (auto g: mutations)
		{
		  std::cerr << "Mutation " << mutation_count << '/'
			    << mutation_max << ": ";
		  f->destroy();
		  f = g->clone();
		  res = process_formula(g->clone());
		  if (res)
		    break;
		  ++mutation_count;
		}
	      for (auto g: mutations)
		g->destroy();
	      if (res)
		{
		  if (lbt_input)
		    bogus = spot::ltl::str_lbt_ltl(f);
		  else
		    bogus = spot::ltl::str_psl(f);
		  if (bogus_output)
		    bogus_output->ostream() << bogus << std::endl;
		}
	    }
	  std::cerr << "Smallest bogus mutation found for ";
	  if (color_opt)
	    std::cerr << bright_blue;
	  std::cerr << input;
	  if (color_opt)
	    std::cerr << reset_color;
	  std::cerr << " is ";
	  if (color_opt)
	    std::cerr << bright_blue;
	  std::cerr << bogus;
	  if (color_opt)
	    std::cerr << reset_color;
	  std::cerr << ".\n\n";
	  grind_output->ostream() << bogus << std::endl;
	}
      f->destroy();

      return 0;
    }

    void product_stats(statistics_formula* stats, unsigned i,
			spot::scc_info* sm)
    {
      if (verbose && sm)
	std::cerr << "info:               " << sm->scc_count()
		  << " SCCs\n";
      // Statistics
      if (want_stats)
	{
	  if (sm)
	    {
	      (*stats)[i].product_scc.push_back(sm->scc_count());
	      spot::tgba_statistics s = spot::stats_reachable(sm->get_aut());
	      (*stats)[i].product_states.push_back(s.states);
	      (*stats)[i].product_transitions.push_back(s.transitions);
	    }
	  else
	    {
	      double n = nan("");
	      (*stats)[i].product_scc.push_back(n);
	      (*stats)[i].product_states.push_back(n);
	      (*stats)[i].product_transitions.push_back(n);
	    }
	}
    }

    int
    process_formula(const spot::ltl::formula* f,
		    const char* filename = 0, int linenum = 0)
    {
      static unsigned round = 0;

      // If we need LBT atomic proposition in any of the input or
      // output, relabel the formula.
      if (!f->has_lbt_atomic_props() &&
	  (runner.has('l') || runner.has('L') || runner.has('T')))
	{
	  const spot::ltl::formula* g = spot::ltl::relabel(f, spot::ltl::Pnn);
	  f->destroy();
	  f = g;
	}

      // ---------- Positive Formula ----------

      runner.round_formula(f, round);

      // Call formula() before printing anything else, in case it
      // complains.
      std::string fstr = runner.formula();
      if (filename)
	std::cerr << filename << ':';
      if (linenum)
	std::cerr << linenum << ':';
      if (filename || linenum)
	std::cerr << ' ';
      if (color_opt)
	std::cerr << bright_blue;
      std::cerr << fstr << '\n';
      if (color_opt)
	std::cerr << reset_color;

      // Make sure we do not translate the same formula twice.
      if (!allow_dups)
	{
	  if (unique_set.insert(f).second)
	    {
	      f->clone();
	    }
	  else
	    {
	      std::cerr
		<< ("warning: This formula or its negation has already"
		    " been checked.\n         Use --allow-dups if it "
		    "should not be ignored.\n")
		<< std::endl;
	      f->destroy();
	      return 0;
	    }
	}


      int problems = 0;

      // These store the result of the translation of the positive and
      // negative formulas.
      size_t m = translators.size();
      std::vector<spot::twa_graph_ptr> pos(m);
      std::vector<spot::twa_graph_ptr> neg(m);
      // These store the complement of the above results, when we can
      // compute it easily.
      std::vector<spot::twa_graph_ptr> comp_pos(m);
      std::vector<spot::twa_graph_ptr> comp_neg(m);


      unsigned n = vstats.size();
      vstats.resize(n + (no_checks ? 1 : 2));
      statistics_formula* pstats = &vstats[n];
      statistics_formula* nstats = 0;
      pstats->resize(m);
      formulas.push_back(fstr);

      for (size_t n = 0; n < m; ++n)
	{
	  bool prob;
	  pos[n] = runner.translate(n, 'P', pstats, prob);
	  problems += prob;

	  // If the automaton is deterministic, compute its complement
	  // as well.  Note that if we have computed statistics
	  // already, there is no need to call is_deterministic()
	  // again.
	  if (!no_complement && pos[n]
	      && ((want_stats && !(*pstats)[n].nondeterministic)
		  || (!want_stats && is_deterministic(pos[n]))))
	    comp_pos[n] = dtgba_complement(pos[n]);
	}

      // ---------- Negative Formula ----------

      // The negative formula is only needed when checks are
      // activated.
      if (!no_checks)
	{
	  nstats = &vstats[n + 1];
	  nstats->resize(m);

	  const spot::ltl::formula* nf =
	    spot::ltl::unop::instance(spot::ltl::unop::Not, f->clone());

	  if (!allow_dups)
	    {
	      bool res = unique_set.insert(nf->clone()).second;
	      // It is not possible to discover that nf has already been
	      // translated, otherwise that would mean that f had been
	      // translated too and we would have caught it before.
	      assert(res);
	      (void) res;
	    }

	  runner.round_formula(nf, round);
	  formulas.push_back(runner.formula());

	  for (size_t n = 0; n < m; ++n)
	    {
	      bool prob;
	      neg[n] = runner.translate(n, 'N', nstats, prob);
	      problems += prob;

	      // If the automaton is deterministic, compute its
	      // complement as well.  Note that if we have computed
	      // statistics already, there is no need to call
	      // is_deterministic() again.
	      if (!no_complement && neg[n]
		  && ((want_stats && !(*nstats)[n].nondeterministic)
		      || (!want_stats && is_deterministic(neg[n]))))
		comp_neg[n] = dtgba_complement(neg[n]);
	    }
	  nf->destroy();
	}

      spot::cleanup_tmpfiles();
      ++round;

      if (!no_checks)
	{
	  std::cerr << "Performing sanity checks and gathering statistics..."
		    << std::endl;

	  if (verbose)
	    std::cerr << "info: getting rid of any Inf acceptance...\n";
	  for (unsigned i = 0; i < m; ++i)
	    {
#define DO(x, prefix, suffix) if (x[i])					\
		{							\
		  cleanup_acceptance_here(x[i]);			\
		  if (x[i]->acc().uses_fin_acceptance())		\
		    {							\
	              auto st = x[i]->num_states();			\
	              auto tr = x[i]->num_edges();		\
	              auto ac = x[i]->acc().num_sets();			\
		      x[i] = remove_fin(x[i]);				\
		      if (verbose)					\
			std::cerr << "info:\t" prefix << i		\
				  << suffix << "\t("			\
				  << st << " st., "			\
				  << tr << " ed., "			\
				  << ac << " sets) -> ("		\
				  << x[i]->num_states() << " st., "	\
				  << x[i]->num_edges() << " ed., " \
				  << x[i]->acc().num_sets() << " sets)\n"; \
		    }							\
		}
	      DO(pos, "     P", " ");
	      DO(neg, "     N", " ");
	      DO(comp_pos, "Comp(P", ")");
	      DO(comp_neg, "Comp(N", ")");
#undef DO
	    }

	  // intersection test
	  for (size_t i = 0; i < m; ++i)
	    if (pos[i])
	      for (size_t j = 0; j < m; ++j)
		if (neg[j])
		  {
		    problems +=
		      check_empty_prod(pos[i], neg[j], i, j, false, false);

		    // Deal with the extra complemented automata if we
		    // have some.

		    // If comp_pos[j] and comp_neg[j] exist for the
		    // same j, it means pos[j] and neg[j] were both
		    // deterministic.  In that case, we will want to
		    // make sure that comp_pos[j]*comp_neg[j] is empty
		    // to assert the complementary of pos[j] and
		    // neg[j].  However using comp_pos[j] and
		    // comp_neg[j] against other translator will not
		    // give us any more insight than pos[j] and
		    // neg[j].  So we only do intersection checks with
		    // a complement automata when one of the two
		    // translation was not deterministic.

		    if (i != j && comp_pos[j] && !comp_neg[j])
		      problems +=
			check_empty_prod(pos[i], comp_pos[j],
					 i, j, false, true);
		    if (i != j && comp_neg[i] && !comp_pos[i])
		      problems +=
			check_empty_prod(comp_neg[i], neg[j],
					 i, j, true, false);
		    if (comp_pos[i] && comp_neg[j] &&
			(i == j || (!comp_neg[i] && !comp_pos[j])))
		      problems +=
			check_empty_prod(comp_pos[i], comp_neg[j],
					 i, j, true, true);
		  }
	}
      else
	{
	  std::cerr << "Gathering statistics..." << std::endl;
	}

      spot::ltl::atomic_prop_set* ap = spot::ltl::atomic_prop_collect(f);
      f->destroy();

      if (want_stats)
	for (size_t i = 0; i < m; ++i)
	  {
	    (*pstats)[i].product_states.reserve(products);
	    (*pstats)[i].product_transitions.reserve(products);
	    (*pstats)[i].product_scc.reserve(products);
	    if (neg[i])
	      {
		(*nstats)[i].product_states.reserve(products);
		(*nstats)[i].product_transitions.reserve(products);
		(*nstats)[i].product_scc.reserve(products);
	      }
	  }
      for (unsigned p = 0; p < products; ++p)
	{
	  // build a random state-space.
	  spot::srand(seed);

	  if (verbose)
	    std::cerr << "info: building state-space #" << p << '/' << products
		      << " of " << states  << " states with seed " << seed
		      << '\n';

	  auto statespace = spot::random_graph(states, density, ap, dict);

	  if (verbose)
	    std::cerr << "info: state-space has "
		      << statespace->num_edges()
		      << " edges\n";

	  // Associated SCC maps.
	  std::vector<spot::scc_info*> pos_map(m);
	  std::vector<spot::scc_info*> neg_map(m);
	  for (size_t i = 0; i < m; ++i)
	    if (pos[i])
	      {
		if (verbose)
		  std::cerr << ("info: building product between state-space and"
				" P") << i
			    << " (" << pos[i]->num_states() << " st., "
			    << pos[i]->num_edges() << " ed.)\n";

		spot::scc_info* sm = nullptr;
		try
		  {
		    auto p = spot::product(pos[i], statespace);
		    if (verbose)
		      std::cerr << "info:   product has " << p->num_states()
				<< " st., " << p->num_edges()
				<< " ed.\n";
		    sm = new spot::scc_info(p);
		  }
		catch (std::bad_alloc&)
		  {
		    std::cerr << ("warning: not enough memory to build "
				  "product of P") << i << " with state-space";
		    if (products > 1)
		      std::cerr << " #" << p << '/' << products << '\n';
		    std::cerr << '\n';
		    ++oom_count;
		  }
		pos_map[i] = sm;
		product_stats(pstats, i, sm);
	      }

	  if (!no_checks)
	    for (size_t i = 0; i < m; ++i)
	      if (neg[i])
		{
		  if (verbose)
		    std::cerr << ("info: building product between state-space"
				  " and N") << i
			      << " (" << neg[i]->num_states() << " st., "
			      << neg[i]->num_edges() << " ed.)\n";

		  spot::scc_info* sm = nullptr;
		  try
		    {
		      auto p = spot::product(neg[i], statespace);
		      if (verbose)
			std::cerr << "info:   product has " << p->num_states()
				  << " st., " << p->num_edges()
				  << " ed.\n";
		      sm = new spot::scc_info(p);
		    }
		  catch (std::bad_alloc&)
		    {
		      std::cerr << ("warning: not enough memory to build "
				    "product of N") << i << " with state-space";
		      if (products > 1)
			std::cerr << " #" << p << '/' << products << '\n';
		      std::cerr << '\n';
		      ++oom_count;
		    }

		  neg_map[i] = sm;
		  product_stats(nstats, i, sm);
		}

	  if (!no_checks)
	    {
	      // cross-comparison test
	      problems += cross_check(pos_map, 'P', p);
	      problems += cross_check(neg_map, 'N', p);

	      // consistency check
	      for (size_t i = 0; i < m; ++i)
		if (pos_map[i] && neg_map[i])
		  {
		    if (verbose)
		      std::cerr << "info: consistency_check (P" << i
				<< ",N" << i << "), state-space #"
				<< p << '/' << products << '\n';
		    if (!(consistency_check(pos_map[i], neg_map[i])))
		      {
			++problems;

			std::ostream& err = global_error();
			err << "error: inconsistency between P" << i
			    << " and N" << i;
			if (products > 1)
			  err << " for state-space #" << p
			      << '/' << products << '\n';
			else
			  err << '\n';
			end_error();
		      }
		  }
	    }

	  // Cleanup.
	  if (!no_checks)
	    for (size_t i = 0; i < m; ++i)
	      delete neg_map[i];
	  for (size_t i = 0; i < m; ++i)
	    delete pos_map[i];
	  ++seed;
	}
      std::cerr << std::endl;
      delete ap;

      // Shall we stop processing formulas now?
      abort_run = global_error_flag && stop_on_error;
      return problems;
    }
  };
}

// Output an RFC4180-compatible CSV file.
static void
print_stats_csv(const char* filename)
{
  if (verbose)
    std::cerr << "info: writing CSV to " << filename << '\n';

  output_file outf(filename);
  std::ostream& out = outf.ostream();

  unsigned ntrans = translators.size();
  unsigned rounds = vstats.size();
  assert(rounds == formulas.size());

  if (!outf.append())
    {
      // Do not output the header line if we append to a file.
      // (Even if that file was empty initially.)
      out << "\"formula\",\"tool\",";
      statistics::fields(out, !opt_omit);
      out << '\n';
    }
  for (unsigned r = 0; r < rounds; ++r)
    for (unsigned t = 0; t < ntrans; ++t)
      if (!opt_omit || vstats[r][t].ok)
	{
	  out << '"';
	  spot::escape_rfc4180(out, formulas[r]);
	  out << "\",\"";
	  spot::escape_rfc4180(out, translators[t].name);
	  out << "\",";
	  vstats[r][t].to_csv(out, !opt_omit);
	  out << '\n';
	}
}

static void
print_stats_json(const char* filename)
{
  if (verbose)
    std::cerr << "info: writing JSON to " << filename << '\n';

  output_file outf(filename);
  std::ostream& out = outf.ostream();

  unsigned ntrans = translators.size();
  unsigned rounds = vstats.size();
  assert(rounds == formulas.size());

  out << "{\n  \"tool\": [\n    \"";
  spot::escape_str(out, translators[0].name);
  for (unsigned t = 1; t < ntrans; ++t)
    {
      out << "\",\n    \"";
      spot::escape_str(out, translators[t].name);
    }
  out << "\"\n  ],\n  \"formula\": [\n    \"";
  spot::escape_str(out, formulas[0]);
  for (unsigned r = 1; r < rounds; ++r)
    {
      out << "\",\n    \"";
      spot::escape_str(out, formulas[r]);
    }
  out << ("\"\n  ],\n  \"fields\":  [\n  \"formula\",\"tool\",");
  statistics::fields(out, !opt_omit);
  out << "\n  ],\n  \"inputs\":  [ 0, 1 ],";
  out << "\n  \"results\": [";
  bool notfirst = false;
  for (unsigned r = 0; r < rounds; ++r)
    for (unsigned t = 0; t < ntrans; ++t)
      if (!opt_omit || vstats[r][t].ok)
	{
	  if (notfirst)
	    out << ',';
	  notfirst = true;
	  out << "\n    [ " << r << ',' << t << ',';
	  vstats[r][t].to_csv(out, !opt_omit, "null", false);
	  out << " ]";
	}
  out << "\n  ]\n}\n";
}

int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, parse_opt, "[COMMANDFMT...]",
		    argp_program_doc, children, 0, 0 };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, 0, 0))
    exit(err);

  if (jobs.empty())
    jobs.emplace_back("-", 1);

  if (translators.empty())
    error(2, 0, "No translator to run?  Run '%s --help' for usage.",
	  program_name);

  if (color_opt == color_if_tty)
    color_opt = isatty(STDERR_FILENO) ? color_always : color_never;

  setup_sig_handler();

  processor p;
  if (p.run())
    return 2;

  if (formulas.empty())
    {
      error(2, 0, "no formula to translate");
    }
  else
    {
      if (global_error_flag)
	{
	  std::ostream& err = global_error();
	  if (bogus_output)
	    err << ("error: some error was detected during the above runs.\n"
		    "       Check file ")
		<< bogus_output_filename
		<< " for problematic formulas.";
	  else
	    err << ("error: some error was detected during the above runs,\n"
		    "       please search for 'error:' messages in the above"
		    " trace.");
	  err << std::endl;
	  end_error();
	}
      else if (timeout_count == 0 && ignored_exec_fail == 0 && oom_count == 0)
	{
	  std::cerr << "No problem detected." << std::endl;
	}
      else
	{
	  std::cerr << "No major problem detected." << std::endl;
	}

      unsigned additional_errors = 0U;
      additional_errors += timeout_count > 0;
      additional_errors += ignored_exec_fail > 0;
      additional_errors += oom_count > 0;
      if (additional_errors)
	{
	  std::cerr << (global_error_flag ? "Additionally, " : "However, ");
	  if (timeout_count)
	    {
	      if (additional_errors > 1)
		std::cerr << "\n  - ";
	      if (timeout_count == 1)
		std::cerr << "1 timeout occurred";
	      else
		std::cerr << timeout_count << " timeouts occurred";
	    }

	  if (oom_count)
	    {
	      if (additional_errors > 1)
		std::cerr << "\n  - ";
	      if (oom_count == 1)
		std::cerr << "1 state-space product was";
	      else
		std::cerr << oom_count << "state-space products were";
	      std::cerr << " skipped by lack of memory";
	    }

	  if (ignored_exec_fail)
	    {
	      if (additional_errors > 1)
		std::cerr << "\n  - ";
	      if (ignored_exec_fail == 1)
		std::cerr << "1 non-zero exit status was ignored";
	      else
		std::cerr << ignored_exec_fail
			  << " non-zero exit statuses were ignored";
	    }
	  if (additional_errors == 1)
	    std::cerr << '.';
	  std::cerr << std::endl;
	}
    }

  delete bogus_output;
  delete grind_output;

  if (json_output)
    print_stats_json(json_output);
  if (csv_output)
    print_stats_csv(csv_output);

  return global_error_flag;
}
