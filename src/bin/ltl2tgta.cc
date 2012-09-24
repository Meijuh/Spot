// -*- coding: utf-8 -*-
// Copyright (C) 2012 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#include "common_sys.hh"

#include <vector>
#include <string>
#include <iostream>
#include <fstream>

#include <argp.h>
#include "progname.h"
#include "error.h"

#include "common_r.hh"
#include "common_cout.hh"
#include "common_finput.hh"
#include "common_post.hh"

#include "misc/_config.h"
#include "ltlparse/public.hh"
#include "ltlvisit/simplify.hh"
#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/ltl2tgba_fm.hh"
#include "tgbaalgos/postproc.hh"
#include "tgba/bddprint.hh"

#include "taalgos/tgba2ta.hh"
#include "taalgos/dotty.hh"
#include "taalgos/minimize.hh"

const char* argp_program_version = "\
ltl2tgta (" SPOT_PACKAGE_STRING ")\n\
\n\
Copyright (C) 2012  Laboratoire de Recherche et Développement de l'Epita.\n\
This is free software; see the source for copying conditions.  There is NO\n\
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE,\n\
to the extent permitted by law.";

const char* argp_program_bug_address = "<" SPOT_PACKAGE_BUGREPORT ">";

const char argp_program_doc[] ="\
Translate linear-time formulas (LTL/PSL) into Testing Automata.\n\n\
By default it outputs a transition-based generalized Testing Automaton \
the smallest Transition-based Generalized Büchi Automata, \
in GraphViz's format.  The input formula is assumed to be \
stuttering-insensitive.";

#define OPT_TGTA 1
#define OPT_TA 2
#define OPT_GTA 3
#define OPT_SPLV 4
#define OPT_SPNO 5
#define OPT_INIT 6

static const argp_option options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Automaton type:", 1 },
    { "tgta", OPT_TGTA, 0, 0,
      "Transition-based Generalized Testing Automaton (default)", 0 },
    { "ta", OPT_TA, 0, 0, "Testing Automaton", 0 },
    { "gta", OPT_GTA, 0, 0, "Generalized Testing Automaton", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Options for TA and GTA creation:", 3 },
    { "single-pass-lv", OPT_SPLV, 0, 0,
      "add an artificial livelock state to obtain a single-pass (G)TA", 0 },
    { "single-pass", OPT_SPNO, 0, 0,
      "create a single-pass (G)TA without artificial livelock state", 0 },
    { "multiple-init", OPT_INIT, 0, 0,
      "do not create the fake initial state", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Output options:", 4 },
    { "utf8", '8', 0, 0, "enable UTF-8 characters in output", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp_child children[] =
  {
    { &finput_argp, 0, 0, 1 },
    { &post_argp, 0, 0, 20 },
    { 0, 0, 0, 0 }
  };

enum ta_types { TGTA, GTA, TA };
ta_types ta_type = TGTA;

bool utf8 = false;
const char* stats = "";
bool opt_with_artificial_initial_state = true;
bool opt_single_pass_emptiness_check = false;
bool opt_with_artificial_livelock = false;

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
    case 'f':
      jobs.push_back(job(arg, false));
      break;
    case 'F':
      jobs.push_back(job(arg, true));
      break;
    case OPT_TGTA:
      ta_type = TGTA;
      type = spot::postprocessor::TGBA;
      break;
    case OPT_GTA:
      ta_type = GTA;
      type = spot::postprocessor::TGBA;
      break;
    case OPT_TA:
      ta_type = TA;
      type = spot::postprocessor::BA;
      break;
    case OPT_INIT:
      opt_with_artificial_initial_state = false;
      break;
    case OPT_SPLV:
      opt_with_artificial_livelock = true;
      break;
    case OPT_SPNO:
      opt_single_pass_emptiness_check = true;
      break;
    case ARGP_KEY_ARG:
      // FIXME: use stat() to distinguish filename from string?
      jobs.push_back(job(arg, false));
      break;

    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}


namespace
{
  class trans_processor
  {
  public:
    spot::ltl::ltl_simplifier& simpl;
    spot::postprocessor& post;

    trans_processor(spot::ltl::ltl_simplifier& simpl,
		    spot::postprocessor& post)
      : simpl(simpl), post(post)
    {
    }

    int
    process_formula(const std::string& input,
		    const char* filename = 0, int linenum = 0)
    {
      spot::ltl::parse_error_list pel;
      const spot::ltl::formula* f = parse_formula(input, pel);

      if (!f || pel.size() > 0)
	  {
	    if (filename)
	      error_at_line(0, 0, filename, linenum, "parse error:");
	    spot::ltl::format_parse_errors(std::cerr, input, pel);
	    if (f)
	      f->destroy();
	    return 1;
	  }

      const spot::ltl::formula* res = simpl.simplify(f);
      f->destroy();
      f = res;

      // This helps ltl_to_tgba_fm() to order BDD variables in a more
      // natural way (improving the degeneralization).
      simpl.clear_as_bdd_cache();

      bool exprop = level == spot::postprocessor::High;
      const spot::tgba* aut = ltl_to_tgba_fm(f, simpl.get_dict(), exprop);
      aut = post.run(aut, f);

      if (utf8)
	{
	  spot::tgba* a = const_cast<spot::tgba*>(aut);
	  if (spot::tgba_explicit_formula* tef =
	      dynamic_cast<spot::tgba_explicit_formula*>(a))
	    tef->enable_utf8();
	  else if (spot::sba_explicit_formula* sef =
		   dynamic_cast<spot::sba_explicit_formula*>(a))
	    sef->enable_utf8();
	}

      bdd ap_set = atomic_prop_collect_as_bdd(f, aut);

      if (ta_type != TGTA)
	{
	  spot::ta* testing_automaton = 0;
	  testing_automaton = tgba_to_ta(aut, ap_set,
					 type == spot::postprocessor::BA,
					 opt_with_artificial_initial_state,
					 opt_single_pass_emptiness_check,
					 opt_with_artificial_livelock);
	  if (level != spot::postprocessor::Low)
	    {
	      spot::ta* testing_automaton_nm = testing_automaton;
	      testing_automaton = spot::minimize_ta(testing_automaton);
	      delete testing_automaton_nm;
	    }
	  spot::dotty_reachable(std::cout, testing_automaton);
	  delete testing_automaton;
	}
      else
	{
	  spot::tgta_explicit* tgta = tgba_to_tgta(aut, ap_set);
	  if (level != spot::postprocessor::Low)
	    {
	      spot::tgta_explicit* a = spot::minimize_tgta(tgta);
	      delete tgta;
	      tgta = a;
	    }
	  spot::dotty_reachable(std::cout,
				dynamic_cast<spot::tgta_explicit*>(tgta)
				->get_ta());
	  delete tgta;
	}

      delete aut;
      flush_cout();
      return 0;
    }

    int
    process_stream(std::istream& is, const char* filename)
    {
      int error = 0;
      int linenum = 0;
      std::string line;
      while (std::getline(is, line))
	error |= process_formula(line, filename, ++linenum);
      return error;
    }

    int
    process_file(const char* filename)
    {
      // Special case for stdin.
      if (filename[0] == '-' && filename[1] == 0)
	return process_stream(std::cin, filename);

      errno = 0;
      std::ifstream input(filename);
      if (!input)
	error(2, errno, "cannot open '%s'", filename);
      return process_stream(input, filename);
    }
  };
}

static int
run_jobs()
{
  spot::ltl::ltl_simplifier simpl(simplifier_options());

  spot::postprocessor postproc;
  postproc.set_pref(pref);
  postproc.set_type(type);
  postproc.set_level(level);

  trans_processor processor(simpl, postproc);

  int error = 0;
  jobs_t::const_iterator i;
  for (i = jobs.begin(); i != jobs.end(); ++i)
    {
      if (!i->file_p)
	error |= processor.process_formula(i->str);
      else
	error |= processor.process_file(i->str);
    }
  if (error)
    return 2;
  return 0;
}

int
main(int argc, char** argv)
{
  set_program_name(argv[0]);
  // Simplify the program name, because argp() uses it to report errors
  // and display help text.
  argv[0] = const_cast<char*>(program_name);

  const argp ap = { options, parse_opt, "[FORMULA...]",
		    argp_program_doc, children, 0, 0 };

  if (int err = argp_parse(&ap, argc, argv, 0, 0, 0))
    exit(err);

  if (jobs.empty())
    error(2, 0, "No formula to translate?  Run '%s --help' for usage.",
	  program_name);

  return run_jobs();
}
