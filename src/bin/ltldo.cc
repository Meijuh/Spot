// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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
#include <fstream>
#include <sys/wait.h>

#include "error.h"

#include "common_setup.hh"
#include "common_cout.hh"
#include "common_conv.hh"
#include "common_finput.hh"
#include "common_aoutput.hh"
#include "common_post.hh"
#include "common_trans.hh"
#include "common_hoaread.hh"

#include "tl/relabel.hh"
#include "misc/bareword.hh"
#include "misc/timer.hh"
#include "twaalgos/lbtt.hh"
#include "twaalgos/relabel.hh"
#include "twaalgos/totgba.hh"
#include "parseaut/public.hh"

const char argp_program_doc[] ="\
Run LTL/PSL formulas through another program, performing conversion\n\
of input and output as required.";

static const argp_option options[] =
  {
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };


static const argp_option more_o_format[] =
  {
    { "%R", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "serial number of the formula translated", 0 },
    { "%T", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "tool used for translation", 0 },
    { "%f", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "formula translated", 0 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

// This is not very elegant, but we need to add the above %-escape
// sequences to those of aoutput_o_fromat_argp for the --help output.
// So far I've failed to instruct argp to merge those two lists into a
// single block.
static const struct argp*
build_percent_list()
{
  const argp_option* iter = aoutput_o_format_argp.options;
  unsigned count = 0;
  while (iter->name || iter->doc)
    {
      ++count;
      ++iter;
    }

  unsigned s = count * sizeof(argp_option);
  argp_option* d =
    static_cast<argp_option*>(malloc(sizeof(more_o_format) + s));
  memcpy(d, aoutput_o_format_argp.options, s);
  memcpy(d + count, more_o_format, sizeof(more_o_format));

  static const struct argp more_o_format_argp =
    { d, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr };
  return &more_o_format_argp;
}

const struct argp_child children[] =
  {
    { &hoaread_argp, 0, "Parsing of automata:", 3 },
    { &finput_argp, 0, nullptr, 1 },
    { &trans_argp, 0, nullptr, 3 },
    { &aoutput_argp, 0, nullptr, 4 },
    { build_percent_list(), 0, nullptr, 5 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  switch (key)
    {
    case ARGP_KEY_ARG:
      translators.push_back(arg);
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
      : translator_runner(dict, true)
    {
    }

    spot::twa_graph_ptr
    translate(unsigned int translator_num, bool& problem, double& duration)
    {
      output.reset(translator_num);

      std::ostringstream command;
      format(command, translators[translator_num].cmd);

      std::string cmd = command.str();
      //std::cerr << "Running [" << l << translator_num << "]: "
      // << cmd << std::endl;
      spot::stopwatch sw;
      sw.start();
      int es = exec_with_timeout(cmd.c_str());
      duration = sw.stop();

      spot::twa_graph_ptr res = nullptr;
      if (timed_out)
	{
	  problem = false;	// A timeout is considered benign
	  std::cerr << "warning: timeout during execution of command \""
		    << cmd << "\"\n";
	  ++timeout_count;
	}
      else if (WIFSIGNALED(es))
	{
	  problem = true;
	  es = WTERMSIG(es);
	  std::cerr << "error: execution of command \"" << cmd
		    << "\" terminated by signal " << es << ".\n";
	}
      else if (WIFEXITED(es) && WEXITSTATUS(es) != 0)
	{
	  problem = true;
	  es = WEXITSTATUS(es);
	  std::cerr << "error: execution of command \"" << cmd
		    << "\" returned exit code " << es << ".\n";
	}
      else if (output.val())
	{
	  problem = false;
	  auto aut = spot::parse_aut(output.val()->name(), dict,
				     spot::default_environment::instance(),
				     opt_parse);
	  if (!aut->errors.empty())
	    {
	      problem = true;
	      std::cerr << "error: failed to parse the automaton "
		"produced by \"" << cmd << "\".\n";
	      aut->format_errors(std::cerr);
	      res = nullptr;
	    }
	  else if (aut->aborted)
	    {
	      problem = true;
	      std::cerr << "error: command \"" << cmd
			<< "\" aborted its output.\n";
	      res = nullptr;
	    }
	  else
	    {
	      res = aut->aut;
	    }
	}
      else			// No automaton output
	{
	  problem = false;
	  res = nullptr;
	}

      output.cleanup();
      return res;
    }
  };


  class processor: public job_processor
  {
    spot::bdd_dict_ptr dict = spot::make_bdd_dict();
    xtranslator_runner runner;
    automaton_printer printer;
    spot::postprocessor& post;
    spot::printable_value<std::string> cmdname;
    spot::printable_value<unsigned> roundval;
    spot::printable_value<std::string> inputf;

  public:
    processor(spot::postprocessor& post)
      : runner(dict), post(post)
    {
      printer.add_stat('T', &cmdname);
      printer.add_stat('R', &roundval);
      printer.add_stat('f', &inputf);
    }

    ~processor()
    {
    }

    int
    process_string(const std::string& input,
		   const char* filename,
		   int linenum)
    {
      spot::parse_error_list pel;
      spot::formula f = parse_formula(input, pel);

      if (!f || !pel.empty())
	{
	  if (filename)
	    error_at_line(0, 0, filename, linenum, "parse error:");
	  spot::format_parse_errors(std::cerr, input, pel);
	  return 1;
	}

      inputf = input;
      process_formula(f, filename, linenum);
      return 0;
    }


    int
    process_formula(spot::formula f,
		    const char* filename = nullptr, int linenum = 0)
    {
      std::unique_ptr<spot::relabeling_map> relmap;

      // If atomic propositions are incompatible with one of the
      // output, relabel the formula.
      if ((!f.has_lbt_atomic_props() &&
	   (runner.has('l') || runner.has('L') || runner.has('T')))
	  || (!f.has_spin_atomic_props() &&
	      (runner.has('s') || runner.has('S'))))
	{
	  relmap.reset(new spot::relabeling_map);
	  f = spot::relabel(f, spot::Pnn, relmap.get());
	}

      static unsigned round = 1;
      runner.round_formula(f, round);

      unsigned ts = translators.size();
      for (unsigned t = 0; t < ts; ++t)
	{
	  bool problem;
	  double translation_time;
	  auto aut = runner.translate(t, problem, translation_time);
	  if (problem)
	    error_at_line(2, 0, filename, linenum, "aborting here");
	  if (aut)
	    {
	      if (relmap)
		relabel_here(aut, relmap.get());
	      aut = post.run(aut, f);
	      cmdname = translators[t].name;
	      roundval = round;
	      printer.print(aut, f, filename, linenum, translation_time,
			    nullptr);
	    };
	}
      spot::cleanup_tmpfiles();
      ++round;
      return 0;
    }
  };
}

int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, parse_opt, "[COMMANDFMT...]",
		    argp_program_doc, children, nullptr, nullptr };

  // Disable post-processing as much as possible by default.
  level = spot::postprocessor::Low;
  pref = spot::postprocessor::Any;
  type = spot::postprocessor::Generic;
  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
    exit(err);

  if (jobs.empty())
    jobs.emplace_back("-", 1);

  if (translators.empty())
    error(2, 0, "No translator to run?  Run '%s --help' for usage.",
	  program_name);

  setup_sig_handler();

  spot::postprocessor post;
  post.set_pref(pref | comp | sbacc);
  post.set_type(type);
  post.set_level(level);

  try
    {
      processor p(post);
      if (p.run())
	return 2;
    }
  catch (const std::runtime_error& e)
    {
      error(2, 0, "%s", e.what());
    }
  return 0;
}
