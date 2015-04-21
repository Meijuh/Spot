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
#include <memory>

#include <argp.h>
#include "error.h"

#include "common_setup.hh"
#include "common_finput.hh"
#include "common_cout.hh"
#include "common_post.hh"
#include "common_file.hh"

#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/lbtt.hh"
#include "tgbaalgos/hoa.hh"
#include "tgbaalgos/neverclaim.hh"
#include "tgbaalgos/stats.hh"
#include "tgba/bddprint.hh"
#include "misc/optionmap.hh"
#include "misc/timer.hh"
#include "dstarparse/public.hh"
#include "tgbaalgos/sccinfo.hh"

static const char argp_program_doc[] ="\
Convert Rabin and Streett automata into Büchi automata.\n\n\
This reads the output format of ltl2dstar and will output a \n\
Transition-based Generalized Büchi Automata in GraphViz's format by default.\n\
If multiple files are supplied (one automaton per file), several automata\n\
will be output.";

enum {
  OPT_DOT = 1,
  OPT_LBTT,
  OPT_NAME,
  OPT_STATS,
  OPT_TGBA,
};

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
    { "dot", OPT_DOT, "a|b|c|f(FONT)|h|n|N|r|R|s|t|v", OPTION_ARG_OPTIONAL,
      "GraphViz's format (default).  Add letters for "
      "(a) acceptance display, (b) acceptance sets as bullets,"
      "(c) circular nodes, (f(FONT)) use FONT, (h) horizontal layout, "
      "(v) vertical layout, (n) with name, (N) without name, "
      "(o) ordered transitions, "
      "(r) rainbow colors for acceptance sets, "
      "(R) color acceptance sets by Inf/Fin, (s) with SCCs, "
      "(t) force transition-based acceptance.", 0 },
    { "hoaf", 'H', "i|s|t|m|l", OPTION_ARG_OPTIONAL,
      "Output the automaton in HOA format.  Add letters to select "
      "(i) use implicit labels for complete deterministic automata, "
      "(s) prefer state-based acceptance when possible [default], "
      "(t) force transition-based acceptance, "
      "(m) mix state and transition-based acceptance, "
      "(l) single-line output", 0 },
    { "lbtt", OPT_LBTT, "t", OPTION_ARG_OPTIONAL,
      "LBTT's format (add =t to force transition-based acceptance even"
      " on Büchi automata)", 0 },
    { "name", OPT_NAME, "FORMAT", 0,
      "set the name of the output automaton", 0 },
    { "output", 'o', "FORMAT", 0,
      "send output to a file named FORMAT instead of standard output.  The"
      " first automaton sent to a file truncates it unless FORMAT starts"
      " with '>>'.", 0 },
    { "spin", 's', "6|c", OPTION_ARG_OPTIONAL, "Spin neverclaim (implies --ba)."
      "  Add letters to select (6) Spin's 6.2.4 style, (c) comments on states",
      0 },
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
      "conversion time (including post-processings, but not parsing)"
      " in seconds", 0 },
    { "%%", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "a single %", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { "extra-options", 'x', "OPTS", 0,
      "fine-tuning options (see spot-x (7))", 0 },
    { 0, 0, 0, 0, 0, 0 }
  };

static const struct argp_child children[] =
  {
    { &post_argp, 0, 0, 20 },
    { &misc_argp, 0, 0, -1 },
    { 0, 0, 0, 0 }
  };

enum output_format { Dot, Lbtt, Lbtt_t, Spin, Stats, Hoa };
static output_format format = Dot;
static const char* opt_dot = nullptr;
static const char* stats = "";
static const char* hoa_opt = nullptr;
static const char* opt_never = nullptr;
static const char* opt_name = nullptr;
static const char* opt_output = nullptr;
static spot::option_map extra_options;

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
    case 'o':
      opt_output = arg;
      break;
    case 's':
      format = Spin;
      if (type != spot::postprocessor::Monitor)
	type = spot::postprocessor::BA;
      if (arg)
	opt_never = arg;
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
    case OPT_NAME:
      opt_name = arg;
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
  class dstar_stat_printer: protected spot::stat_printer
  {
  public:
    dstar_stat_printer(std::ostream& os, const char* format)
      : spot::stat_printer(os, format)
    {
      declare('A', &daut_acc_);
      declare('C', &daut_scc_);
      declare('E', &daut_edges_);
      declare('F', &filename_);
      declare('f', &filename_);	// Override the formula printer.
      declare('S', &daut_states_);
      declare('T', &daut_trans_);
      declare('m', &aut_name_);
    }

    using spot::formater::set_output;

    /// \brief print the configured statistics.
    ///
    /// The \a f argument is not needed if the Formula does not need
    /// to be output.
    std::ostream&
    print(const spot::const_dstar_aut_ptr& daut,
	  const spot::const_twa_graph_ptr& aut,
	  const char* filename, double run_time)
    {
      filename_ = filename;

      if (has('T'))
	{
	  spot::tgba_sub_statistics s = sub_stats_reachable(daut->aut);
	  daut_states_ = s.states;
	  daut_edges_ = s.transitions;
	  daut_trans_ = s.sub_transitions;
	}
      else if (has('E'))
	{
	  spot::tgba_sub_statistics s = sub_stats_reachable(daut->aut);
	  daut_states_ = s.states;
	  daut_edges_ = s.transitions;
	}
      else if (has('S'))
	{
	  daut_states_ = daut->aut->num_states();
	}

      if (has('A'))
	daut_acc_ = daut->accpair_count;

      if (has('C'))
	daut_scc_ = spot::scc_info(daut->aut).scc_count();

      if (has('m'))
	{
	  auto n = aut->get_named_prop<std::string>("automaton-name");
	  if (n)
	    aut_name_ = *n;
	  else
	    aut_name_.val().clear();
	}

      return this->spot::stat_printer::print(aut, 0, run_time);
    }

  private:
    spot::printable_value<const char*> filename_;
    spot::printable_value<unsigned> daut_states_;
    spot::printable_value<unsigned> daut_edges_;
    spot::printable_value<unsigned> daut_trans_;
    spot::printable_value<unsigned> daut_acc_;
    spot::printable_value<unsigned> daut_scc_;
    spot::printable_value<std::string> aut_name_;
  };


  class dstar_processor: public job_processor
  {
  public:
    spot::postprocessor& post;
    dstar_stat_printer statistics;
    std::ostringstream name;
    dstar_stat_printer namer;
    std::ostringstream outputname;
    dstar_stat_printer outputnamer;
    std::map<std::string, std::unique_ptr<output_file>> outputfiles;

    dstar_processor(spot::postprocessor& post)
      : post(post), statistics(std::cout, stats),
	namer(name, opt_name),
	outputnamer(outputname, opt_output)
    {
    }

    int
    process_formula(const spot::ltl::formula*, const char*, int)
    {
      SPOT_UNREACHABLE();
    }


    int
    process_file(const char* filename)
    {
      spot::dstar_parse_error_list pel;
      auto daut = spot::dstar_parse(filename, pel, spot::make_bdd_dict());
      if (spot::format_dstar_parse_errors(std::cerr, filename, pel))
	return 2;
      if (!daut)
	error(2, 0, "failed to read automaton from %s", filename);

      spot::stopwatch sw;
      sw.start();
      auto nba = spot::dstar_to_tgba(daut);
      auto aut = post.run(nba, 0);
      const double conversion_time = sw.stop();

      // Name the output automaton.
      if (opt_name)
	{
	  name.str("");
	  namer.print(daut, aut, filename, conversion_time);
	  aut->set_named_prop("automaton-name", new std::string(name.str()));
	}

      std::ostream* out = &std::cout;
      if (opt_output)
	{
	  outputname.str("");
	  outputnamer.print(daut, aut, filename, conversion_time);
	  std::string fname = outputname.str();
	  auto p = outputfiles.emplace(fname, nullptr);
	  if (p.second)
	    p.first->second.reset(new output_file(fname.c_str()));
	  out = &p.first->second->ostream();
	}

      switch (format)
	{
	case Dot:
	  spot::dotty_reachable(*out, aut, opt_dot);
	  break;
	case Lbtt:
	  spot::lbtt_reachable(*out, aut, type == spot::postprocessor::BA);
	  break;
	case Lbtt_t:
	  spot::lbtt_reachable(*out, aut, false);
	  break;
	case Hoa:
	  spot::hoa_reachable(*out, aut, hoa_opt) << '\n';
	  break;
	case Spin:
	  spot::never_claim_reachable(*out, aut, opt_never);
	  break;
	case Stats:
	  statistics.set_output(*out);
	  statistics.print(daut, aut, filename, conversion_time) << '\n';
	  break;
	}
      flush_cout();
      return 0;
    }
  };
}

int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, parse_opt, "[FILENAMES...]",
		    argp_program_doc, children, 0, 0 };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, 0, 0))
    exit(err);

  if (jobs.empty())
    jobs.emplace_back("-", true);

  spot::postprocessor post(&extra_options);
  post.set_pref(pref | comp);
  post.set_type(type);
  post.set_level(level);

  try
    {
      dstar_processor processor(post);
      if (processor.run())
	return 2;
    }
  catch (const std::runtime_error& e)
    {
      error(2, 0, "%s", e.what());
    }
  return 0;
}
