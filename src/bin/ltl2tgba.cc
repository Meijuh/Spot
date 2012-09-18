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

#include "misc/_config.h"
#include "ltlparse/public.hh"
#include "ltlvisit/simplify.hh"
#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/lbtt.hh"
#include "tgbaalgos/ltl2tgba_fm.hh"
#include "tgbaalgos/neverclaim.hh"
#include "tgbaalgos/postproc.hh"
#include "tgbaalgos/save.hh"
#include "tgba/bddprint.hh"

const char* argp_program_version = "\
ltl2tgba (" SPOT_PACKAGE_STRING ")\n\
\n\
Copyright (C) 2012  Laboratoire de Recherche et Développement de l'Epita.\n\
This is free software; see the source for copying conditions.  There is NO\n\
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE,\n\
to the extent permitted by law.";

const char* argp_program_bug_address = "<" SPOT_PACKAGE_BUGREPORT ">";

const char argp_program_doc[] ="\
Translate linear formulas (LTL/PSL) into Büchi automata.\n\n\
The default is to take the time to apply all available optimization \
to output the smallest Transition-based Generalized Büchi Automata, \
in GraphViz's format.\n\
If multiple formulas are supplied, several automata will be output.";

#define OPT_TGBA 1
#define OPT_SMALL 2
#define OPT_LOW 3
#define OPT_MEDIUM 4
#define OPT_HIGH 5
#define OPT_DOT 6
#define OPT_LBTT 7
#define OPT_SPOT 8

static const argp_option options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Automaton type:", 2 },
    { "tgba", OPT_TGBA, 0, 0,
      "Transition-based Generalized Büchi Automaton (default)", 0 },
    { "ba", 'B', 0, 0, "Büchi Automaton", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Output format:", 3 },
    { "dot", OPT_DOT, 0, 0, "GraphViz's format (default)", 0 },
    { "lbtt", OPT_LBTT, 0, 0, "LBTT's format", 0 },
    { "spin", 's', 0, 0, "Spin neverclaim (implies --ba)", 0 },
    { "spot", OPT_SPOT, 0, 0, "SPOT's format", 0 },
    { "utf8", '8', 0, 0, "enable UTF-8 characters in output "
      "(works only with --spot or --dot)", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Translation intent:", 4 },
    { "small", OPT_SMALL, 0, 0, "prefer small automata (default)", 0 },
    { "deterministic", 'D', 0, 0, "prefer deterministic automata", 0 },
    { "any", 'a', 0, 0, "no preference", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Optimization level:", 5 },
    { "low", OPT_LOW, 0, 0, "minimal optimizations (fast)", 0 },
    { "medium", OPT_MEDIUM, 0, 0, "moderate optimizations", 0 },
    { "high", OPT_HIGH, 0, 0,
      "all available optimizations (slow, default)", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp_child children[] =
  {
    { &finput_argp, 0, 0, 1 },
    { 0, 0, 0, 0 }
  };

spot::postprocessor::output_type type = spot::postprocessor::TGBA;
spot::postprocessor::output_pref pref = spot::postprocessor::Small;
spot::postprocessor::optimization_level level = spot::postprocessor::High;
enum output_format { Dot, Lbtt, Spin, Spot } format = Dot;
bool utf8 = false;

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case '8':
      spot::enable_utf8();
      break;
    case 'a':
      pref = spot::postprocessor::Any;
      break;
    case 'B':
      type = spot::postprocessor::BA;
      break;
    case 'D':
      pref = spot::postprocessor::Deterministic;
      break;
    case 'f':
      jobs.push_back(job(arg, false));
      break;
    case 'F':
      jobs.push_back(job(arg, true));
      break;
    case 's':
      format = Spin;
      type = spot::postprocessor::BA;
      break;
    case OPT_HIGH:
      level = spot::postprocessor::High;
      simplification_level = 3;
      break;
    case OPT_DOT:
      format = Dot;
      break;
    case OPT_LBTT:
      format = Lbtt;
      break;
    case OPT_LOW:
      level = spot::postprocessor::Low;
      simplification_level = 1;
      break;
    case OPT_MEDIUM:
      level = spot::postprocessor::Medium;
      simplification_level = 2;
      break;
    case OPT_SMALL:
      pref = spot::postprocessor::Small;
      break;
    case OPT_SPOT:
      format = Spot;
      break;
    case OPT_TGBA:
      if (format == Spin)
	error(2, 0, "--spin and --tgba are incompatible");
      type = spot::postprocessor::TGBA;
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

      switch (format)
	{
	case Dot:
	  spot::dotty_reachable(std::cout, aut,
				type == spot::postprocessor::BA);
	  break;
	case Lbtt:
	  spot::lbtt_reachable(std::cout, aut);
	  break;
	case Spot:
	  spot::tgba_save_reachable(std::cout, aut);
	  break;
	case Spin:
	  spot::never_claim_reachable(std::cout, aut, f);
	  break;
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
