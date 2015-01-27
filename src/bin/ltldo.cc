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

#include "error.h"

#include "common_setup.hh"
#include "common_cout.hh"
#include "common_conv.hh"
#include "common_finput.hh"
#include "common_aoutput.hh"
#include "common_post.hh"
#include "common_trans.hh"

#include "ltlvisit/tostring.hh"
#include "ltlvisit/relabel.hh"
#include "misc/bareword.hh"
#include "misc/timer.hh"
#include "tgbaalgos/lbtt.hh"
#include "tgbaalgos/relabel.hh"
#include "hoaparse/public.hh"
#include "dstarparse/public.hh"

const char argp_program_doc[] ="\
Run LTL/PSL formulas through another program, performing conversion\n\
of input and output as required.";

static const argp_option options[] =
  {
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { 0, 0, 0, 0, 0, 0 }
  };


static const argp_option more_o_format[] =
  {
    { "%R", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "serial number of the formula translated", 0 },
    { "%T", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "tool used for translation", 0 },
    { "%f", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "formula translated", 0 },
    { 0, 0, 0, 0, 0, 0 }
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
    { d, 0, 0, 0, 0, 0, 0 };
  return &more_o_format_argp;
}

const struct argp_child children[] =
  {
    { &finput_argp, 0, 0, 1 },
    { &trans_argp, 0, 0, 3 },
    { &aoutput_argp, 0, 0, 4 },
    { build_percent_list(), 0, 0, 5 },
    { &misc_argp, 0, 0, -1 },
    { 0, 0, 0, 0 }
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

    spot::tgba_digraph_ptr
    translate(unsigned int translator_num, bool& problem, double& duration)
    {
      output.reset(translator_num);

      std::ostringstream command;
      format(command, translators[translator_num].cmd);

      //assert(output.format != printable_result_filename::None);

      std::string cmd = command.str();
      //std::cerr << "Running [" << l << translator_num << "]: "
      // << cmd << std::endl;
      spot::stopwatch sw;
      sw.start();
      int es = exec_with_timeout(cmd.c_str());
      duration = sw.stop();

      spot::tgba_digraph_ptr res = nullptr;
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
      else
	{
	  problem = false;
	  switch (output.format)
	    {
	    case printable_result_filename::Lbtt:
	      {
		std::string error;
		std::ifstream f(output.val()->name());
		if (!f)
		  {
		    problem = true;
		    std::cerr << "error: could not open " << output.val()
			      << " after running \"" << cmd << "\".\n";
		  }
		else
		  {
		    res = spot::lbtt_parse(f, error, dict);
		    if (!res)
		      {
			problem = true;
			std::cerr << "error: failed to parse output of \""
				  << cmd << "\" in LBTT format:\n"
				  << "error:   " << error << '\n';
		      }
		  }
		break;
	      }
	    case printable_result_filename::Dstar:
	      {
		spot::dstar_parse_error_list pel;
		std::string filename = output.val()->name();
		auto aut = spot::dstar_parse(filename, pel, dict);
		if (!pel.empty())
		  {
		    problem = true;
		    std::cerr << "error: failed to parse the output of \""
			      << cmd << "\" as a DSTAR automaton.\n";
		    spot::format_dstar_parse_errors(std::cerr, filename, pel);
		    res = nullptr;
		  }
		else
		  {
		    res = dstar_to_tgba(aut);
		  }
		break;
	      }
	    case printable_result_filename::Hoa: // Will also read neverclaims
	      {
		spot::hoa_parse_error_list pel;
		std::string filename = output.val()->name();
		auto aut = spot::hoa_parse(filename, pel, dict);
		if (!pel.empty())
		  {
		    problem = true;
		    std::cerr << "error: failed to parse the automaton "
		      "produced by \"" << cmd << "\".\n";
		    spot::format_hoa_parse_errors(std::cerr, filename, pel);
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
	      break;
	    case printable_result_filename::None:
	      problem = false;
	      res = nullptr;
	      break;
	    }
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

      inputf = input;
      process_formula(f, filename, linenum);
      return 0;
    }


    int
    process_formula(const spot::ltl::formula* f,
		    const char* filename = 0, int linenum = 0)
    {
      std::unique_ptr<spot::ltl::relabeling_map> relmap;

      // If atomic propositions are incompatible with one of the
      // output, relabel the formula.
      if ((!f->has_lbt_atomic_props() &&
	   (runner.has('l') || runner.has('L') || runner.has('T')))
	  || (!f->has_spin_atomic_props() &&
	      (runner.has('s') || runner.has('S'))))
	{
	  relmap.reset(new spot::ltl::relabeling_map);
	  auto g = spot::ltl::relabel(f, spot::ltl::Pnn, relmap.get());
	  f->destroy();
	  f = g;
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
      f->destroy();
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
		    argp_program_doc, children, 0, 0 };

  // Disable post-processing as much as possible by default.
  level = spot::postprocessor::Low;
  pref = spot::postprocessor::Any;
  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, 0, 0))
    exit(err);

  if (jobs.empty())
    jobs.emplace_back("-", 1);

  if (translators.empty())
    error(2, 0, "No translator to run?  Run '%s --help' for usage.",
	  program_name);

  setup_sig_handler();

  spot::postprocessor post;
  post.set_pref(pref | comp);
  post.set_type(type);
  post.set_level(level);

  processor p(post);
  if (p.run())
    return 2;

  return 0;
}
