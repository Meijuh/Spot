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
#include "common_aoutput.hh"
#include "common_post.hh"
#include "common_file.hh"

#include "twaalgos/dot.hh"
#include "twaalgos/lbtt.hh"
#include "twaalgos/hoa.hh"
#include "twaalgos/neverclaim.hh"
#include "twaalgos/stats.hh"
#include "twaalgos/totgba.hh"
#include "twa/bddprint.hh"
#include "misc/optionmap.hh"
#include "misc/timer.hh"
#include "parseaut/public.hh"
#include "twaalgos/sccinfo.hh"

static const char argp_program_doc[] ="\
Convert Rabin and Streett automata into Büchi automata.\n\n\
This reads the output format of ltl2dstar and will output a\n\
Transition-based Generalized Büchi Automata in GraphViz's format by default.\n\
If multiple files are supplied (one automaton per file), several automata\n\
will be output.";

enum {
  OPT_TGBA = 1,
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
    { "ba", 'B', 0, 0, "Büchi Automaton (with state-based acceptance)", 0 },
    { "monitor", 'M', 0, 0, "Monitor (accepts all finite prefixes "
      "of the given property)", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { "extra-options", 'x', "OPTS", 0,
      "fine-tuning options (see spot-x (7))", 0 },
    { 0, 0, 0, 0, 0, 0 }
  };

static const struct argp_child children[] =
  {
    { &aoutput_argp, 0, 0, 0 },
    { &aoutput_io_format_argp, 0, 0, 4 },
    { &post_argp, 0, 0, 20 },
    { &misc_argp, 0, 0, -1 },
    { 0, 0, 0, 0 }
  };

static spot::option_map extra_options;

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case 'B':
      type = spot::postprocessor::BA;
      break;
    case 'F':
      jobs.emplace_back(arg, true);
      break;
    case 'M':
      type = spot::postprocessor::Monitor;
      break;
    case 'x':
      {
	const char* opt = extra_options.parse_options(arg);
	if (opt)
	  error(2, 0, "failed to parse --options near '%s'", opt);
      }
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
  class dstar_processor: public job_processor
  {
  public:
    spot::postprocessor& post;
    automaton_printer printer;

    dstar_processor(spot::postprocessor& post)
      : post(post), printer(aut_input)
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
      spot::parse_aut_error_list pel;
      auto daut = spot::parse_aut(filename, pel, spot::make_bdd_dict());
      if (spot::format_parse_aut_errors(std::cerr, filename, pel))
	return 2;
      if (!daut)
	error(2, 0, "failed to read automaton from %s", filename);

      spot::stopwatch sw;
      sw.start();
      auto nba = spot::to_generalized_buchi(daut->aut);
      auto aut = post.run(nba, 0);
      const double conversion_time = sw.stop();

      printer.print(aut, nullptr, filename, -1, conversion_time, daut);
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
  post.set_pref(pref | comp | sbacc);
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
