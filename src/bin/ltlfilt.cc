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

#ifdef HAVE_CONFIG_H
# include "config.h"
#endif

#include <cstdlib>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <argp.h>
#include "progname.h"
#include "error.h"

#include "misc/_config.h"
#include "misc/hash.hh"
#include "ltlparse/public.hh"
#include "ltlvisit/tostring.hh"
#include "ltlvisit/simplify.hh"
#include "ltlvisit/length.hh"
#include "ltlast/unop.hh"
#include "ltlast/multop.hh"
#include "tgbaalgos/ltl2tgba_fm.hh"
#include "tgbaalgos/minimize.hh"
#include "tgbaalgos/safety.hh"

const char* argp_program_version = "\
ltlfilter (" SPOT_PACKAGE_STRING ")\n\
\n\
Copyright (C) 2012  Laboratoire de Recherche et Développement de l'Epita.\n\
This is free software; see the source for copying conditions.  There is NO\n\
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE,\n\
to the extent permitted by law.";

const char* argp_program_bug_address = "<" SPOT_PACKAGE_BUGREPORT ">";

const char argp_program_doc[] ="\
Read a list of formulas and output them back after some optional processing.\v\
Exit status:\n\
  0  if some formulas were output (skipped syntax errors do not count)\n\
  1  if no formula were output (no match)\n\
  2  if any error has been reported";

#define OPT_SPOT 1
#define OPT_SKIP_ERRORS 2
#define OPT_DROP_ERRORS 3
#define OPT_NNF 4
#define OPT_LTL 5
#define OPT_PSL 6
#define OPT_NOX 7
#define OPT_BOOLEAN 8
#define OPT_EVENTUAL 9
#define OPT_UNIVERSAL 10
#define OPT_SYNTACTIC_SAFETY 11
#define OPT_SYNTACTIC_GUARANTEE 12
#define OPT_SYNTACTIC_OBLIGATION 13
#define OPT_SYNTACTIC_RECURRENCE 14
#define OPT_SYNTACTIC_PERSISTENCE 15
#define OPT_SAFETY 16
#define OPT_GUARANTEE 17
#define OPT_OBLIGATION 18
#define OPT_SIZE_MIN 19
#define OPT_SIZE_MAX 20
#define OPT_BSIZE_MIN 21
#define OPT_BSIZE_MAX 22
#define OPT_IMPLIED_BY 23
#define OPT_IMPLY 24
#define OPT_EQUIVALENT_TO 25

static const argp_option options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Input options:", 1 },
    { "formula", 'f', "STRING", 0, "process the formula STRING", 0 },
    { "file", 'F', "FILENAME", 0,
      "process each line of FILENAME as a formula", 0 },
    { 0, 0, 0, 0, "Error handling:", 2 },
    { "skip-errors", OPT_SKIP_ERRORS, 0, 0,
      "output erroneous lines as-is without processing", 0 },
    { "drop-errors", OPT_DROP_ERRORS, 0, 0,
      "discard erroneous lines (default)", 0 },
    { "quiet", 'q', 0, 0, "do not report syntax errors", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Transformation options:", 3 },
    { "negate", 'n', 0, 0, "negate each formula", 0 },
    { "nnf", OPT_NNF, 0, 0, "rewrite formulas in negative normal form", 0 },
    { "simplify", 'r', "LEVEL", OPTION_ARG_OPTIONAL,
      "simplify formulas according to LEVEL (see below)", 0 },
    { 0, 0, 0, 0, "  The simplification LEVEL might be one of:", 4 },
    { "  0", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "No rewriting", 0 },
    { "  1", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "basic rewritings and eventual/universal rules", 0 },
    { "  2", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "additional syntactic implication rules", 0 },
    { "  3", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "better implications using containment (default)", 0 },
    /**************************************************/
    { 0, 0, 0, 0,
      "Filtering options (matching is done after transformation):", 5 },
    { "ltl", OPT_LTL, 0, 0, "match LTL formulas", 0 },
    { "psl", OPT_PSL, 0, 0, "match PSL formulas", 0 },
    { "nox", OPT_NOX, 0, 0, "match X-free formulas", 0 },
    { "boolean", OPT_BOOLEAN, 0, 0, "match Boolean formulas", 0 },
    { "eventual", OPT_EVENTUAL, 0, 0, "match pure eventualities", 0 },
    { "universal", OPT_UNIVERSAL, 0, 0, "match purely universal formulas", 0 },
    { "syntactic-safety", OPT_SYNTACTIC_SAFETY, 0, 0,
      "match syntactic-safety formulas", 0 },
    { "syntactic-guarantee", OPT_SYNTACTIC_GUARANTEE, 0, 0,
      "match syntactic-guarantee formulas", 0 },
    { "syntactic-obligation", OPT_SYNTACTIC_OBLIGATION, 0, 0,
      "match syntactic-obligation formulas", 0 },
    { "syntactic-recurrence", OPT_SYNTACTIC_RECURRENCE, 0, 0,
      "match syntactic-recurrence formulas", 0 },
    { "syntactic-persistence", OPT_SYNTACTIC_PERSISTENCE, 0, 0,
      "match syntactic-persistence formulas", 0 },
    { "safety", OPT_SAFETY, 0, 0,
      "match safety formulas (even pathological)", 0 },
    { "guarantee", OPT_GUARANTEE, 0, 0,
      "match guarantee formulas (even pathological)", 0 },
    { "obligation", OPT_OBLIGATION, 0, 0,
      "match obligation formulas (even pathological)", 0 },
    { "size-max", OPT_SIZE_MAX, "INT", 0,
      "match formulas with size <= INT", 0 },
    { "size-min", OPT_SIZE_MIN, "INT", 0,
      "match formulas with size >= INT", 0 },
    { "bsize-max", OPT_BSIZE_MAX, "INT", 0,
      "match formulas with Boolean size <= INT", 0 },
    { "bsize-min", OPT_BSIZE_MIN, "INT", 0,
      "match formulas with Boolean size >= INT", 0 },
    { "implied-by", OPT_IMPLIED_BY, "FORMULA", 0,
      "match formulas implied by FORMULA", 0 },
    { "imply", OPT_IMPLY, "FORMULA", 0,
      "match formulas implying FORMULA", 0 },
    { "equivalent-to", OPT_EQUIVALENT_TO, "FORMULA", 0,
      "match formulas equivalent to FORMULA", 0 },
    { "invert-match", 'v', 0, 0, "Select non-matching formulas", 0},
    /**************************************************/
    { 0, 0, 0, 0, "Output options:", 6 },
    { "full-parentheses", 'p', 0, 0,
      "output fully-parenthesized formulas", 0 },
    { "spin", 's', 0, 0, "output in Spin's syntax", 0 },
    { "spot", OPT_SPOT, 0, 0, "output in Spot's syntax (default)", 0 },
    { "utf8", '8', 0, 0, "output using UTF-8 characters", 0 },
    { "unique", 'u', 0, 0, "drop formulas that have already been outpout", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { 0, 0, 0, 0, 0, 0 }
  };

struct job
{
  const char* str;
  bool file_p;	// true if str is a filename, false if it is a formula

  job(const char* str, bool file_p)
    : str(str), file_p(file_p)
  {
  }
};

typedef std::vector<job> jobs_t;
static jobs_t jobs;

static bool one_match = false;

enum error_style_t { drop_errors, skip_errors };
static error_style_t error_style = drop_errors;
static bool quiet = false;
enum output_format_t { spot_output, spin_output, utf8_output };
static output_format_t output_format = spot_output;
static bool full_parenth = false;
static bool nnf = false;
static bool negate = false;
static int level = 0;
static bool unique = false;
static bool psl = false;
static bool ltl = false;
static bool nox = false;
static bool invert = false;
static bool boolean = false;
static bool universal = false;
static bool eventual = false;
static bool syntactic_safety = false;
static bool syntactic_guarantee = false;
static bool syntactic_obligation = false;
static bool syntactic_recurrence = false;
static bool syntactic_persistence = false;
static bool safety = false;
static bool guarantee = false;
static bool obligation = false;
static int size_min = -1;
static int size_max = -1;
static int bsize_min = -1;
static int bsize_max = -1;

static const spot::ltl::formula* implied_by = 0;
static const spot::ltl::formula* imply = 0;
static const spot::ltl::formula* equivalent_to = 0;

static int
to_int(const char* s)
{
  char* endptr;
  int res = strtol(s, &endptr, 10);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as an integer.", s);
  return res;
}


static const spot::ltl::formula*
parse_formula_arg(const std::string& input)
{
  spot::ltl::parse_error_list pel;
  const spot::ltl::formula* f = spot::ltl::parse(input, pel);
  if (spot::ltl::format_parse_errors(std::cerr, input, pel))
    error(2, 0, "parse error when parsing an argument");
  return f;
}



static int
parse_opt(int key, char* arg, struct argp_state* state)
{
  (void) state;
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case '8':
      output_format = utf8_output;
      break;
    case 'f':
      jobs.push_back(job(arg, false));
      break;
    case 'F':
      jobs.push_back(job(arg, true));
      break;
    case 'n':
      negate = true;
      break;
    case 'p':
      full_parenth = true;
      break;
    case 'q':
      quiet = true;
      break;
    case 'r':
      if (!arg)
	{
	  level = 3;
	  break;
	}
      else
	{
	  if (arg[1] == 0)
	    switch (arg[0])
	      {
	      case '0':
	      case '1':
	      case '2':
	      case '3':
		level = arg[0] = '0';
		return 0;
	      }
	  error(2, 0, "invalid simplification level '%s'",  arg);
	}
      break;
    case 's':
      output_format = spin_output;
      break;
    case 'u':
      unique = true;
      break;
    case 'v':
      invert = true;
      break;
    case ARGP_KEY_ARG:
      // FIXME: use stat() to distinguish filename from string?
      jobs.push_back(job(arg, true));
      break;
    case OPT_BOOLEAN:
      boolean = true;
      break;
    case OPT_BSIZE_MIN:
      bsize_min = to_int(arg);
      break;
    case OPT_BSIZE_MAX:
      bsize_max = to_int(arg);
      break;
    case OPT_DROP_ERRORS:
      error_style = drop_errors;
      break;
    case OPT_GUARANTEE:
      guarantee = obligation = true;
      break;
    case OPT_LTL:
      ltl = true;
      break;
    case OPT_NNF:
      nnf = true;
      break;
    case OPT_NOX:
      nox = true;
      break;
    case OPT_OBLIGATION:
      obligation = true;
      break;
    case OPT_PSL:
      psl = true;
      break;
    case OPT_SAFETY:
      safety = obligation = true;
      break;
    case OPT_SIZE_MIN:
      size_min = to_int(arg);
      break;
    case OPT_SIZE_MAX:
      size_max = to_int(arg);
      break;
    case OPT_SKIP_ERRORS:
      error_style = skip_errors;
      break;
    case OPT_SPOT:
      output_format = spot_output;
      break;
    case OPT_SYNTACTIC_SAFETY:
      syntactic_safety = true;
      break;
    case OPT_SYNTACTIC_GUARANTEE:
      syntactic_guarantee = true;
      break;
    case OPT_SYNTACTIC_OBLIGATION:
      syntactic_obligation = true;
      break;
    case OPT_SYNTACTIC_RECURRENCE:
      syntactic_recurrence = true;
      break;
    case OPT_SYNTACTIC_PERSISTENCE:
      syntactic_persistence = true;
      break;
    case OPT_IMPLIED_BY:
      {
	const spot::ltl::formula* i = parse_formula_arg(arg);
	// a→c∧b→c ≡ (a∨b)→c
	implied_by =
	  spot::ltl::multop::instance(spot::ltl::multop::Or, implied_by, i);
	break;
      }
    case OPT_IMPLY:
      {
	// a→b∧a→c ≡ a→(b∧c)
	const spot::ltl::formula* i = parse_formula_arg(arg);
	imply =
	  spot::ltl::multop::instance(spot::ltl::multop::And, imply, i);
	break;
      }
    case OPT_EQUIVALENT_TO:
      {
	if (equivalent_to)
	  error(2, 0, "only one --equivalent-to option can be given");
	equivalent_to = parse_formula_arg(arg);
	break;
      }
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

typedef Sgi::hash_set<const spot::ltl::formula*,
		      const spot::ptr_hash<const spot::ltl::formula> > fset_t;

namespace
{
  class ltl_processor
  {
  public:
    spot::ltl::ltl_simplifier& simpl;
    fset_t unique_set;

    ltl_processor(spot::ltl::ltl_simplifier& simpl)
    : simpl(simpl)
    {
    }

    int
    process_formula(const std::string& input,
		    const char* filename = 0, int linenum = 0)
    {
      spot::ltl::parse_error_list pel;
      const spot::ltl::formula* f = spot::ltl::parse(input, pel);

      if (!f || pel.size() > 0)
	  {
	    if (!quiet)
	      {
		if (filename)
		  error_at_line(0, 0, filename, linenum, "parse error:");
		spot::ltl::format_parse_errors(std::cerr, input, pel);
	      }

	    if (f)
	      f->destroy();

	    if (error_style == skip_errors)
	      std::cout << input << std::endl;
	    else
	      assert(error_style == drop_errors);
	    return !quiet;
	  }

      if (negate)
	f = spot::ltl::unop::instance(spot::ltl::unop::Not, f);

      if (level)
	{
	  const spot::ltl::formula* res = simpl.simplify(f);
	  f->destroy();
	  f = res;
	}

      if (nnf)
	{
	  const spot::ltl::formula* res = simpl.negative_normal_form(f);
	  f->destroy();
	  f = res;
	}

      bool matched = true;

      matched &= !ltl || f->is_ltl_formula();
      matched &= !psl || f->is_psl_formula();
      matched &= !nox || f->is_X_free();
      matched &= !boolean || f->is_boolean();
      matched &= !universal || f->is_universal();
      matched &= !eventual || f->is_eventual();
      matched &= !syntactic_safety || f->is_syntactic_safety();
      matched &= !syntactic_guarantee || f->is_syntactic_guarantee();
      matched &= !syntactic_obligation || f->is_syntactic_obligation();
      matched &= !syntactic_recurrence || f->is_syntactic_recurrence();
      matched &= !syntactic_persistence || f->is_syntactic_persistence();

      if (matched && (size_min > 0 || size_max >= 0))
	{
	  int l = spot::ltl::length(f);
	  matched &= (size_min <= 0) || (l >= size_min);
	  matched &= (size_max < 0) || (l <= size_max);
	}

      if (matched && (bsize_min > 0 || bsize_max >= 0))
	{
	  int l = spot::ltl::length_boolone(f);
	  matched &= (bsize_min <= 0) || (l >= bsize_min);
	  matched &= (bsize_max < 0) || (l <= bsize_max);
	}

      matched &= !implied_by || simpl.implication(implied_by, f);
      matched &= !imply || simpl.implication(f, imply);
      matched &= !equivalent_to || simpl.are_equivalent(f, equivalent_to);

      // Match obligations and subclasses using WDBA minimization.
      // Because this is costly, we compute it later, so that we don't
      // have to compute it on formulas that have been discarded for
      // other reasons.
      if (matched && obligation)
	{
	  spot::tgba* aut = ltl_to_tgba_fm(f, simpl.get_dict());
	  spot::tgba* min = minimize_obligation(aut, f);
	  assert(min);
	  if (aut == min)
	    {
	      // Not an obligation
	      matched = false;
	    }
	  else
	    {
	      matched &= !guarantee || is_guarantee_automaton(min);
	      matched &= !safety || is_safety_mwdba(min);
	      delete min;
	    }
	  delete aut;
	}

      matched ^= invert;

      if (unique)
	{
	  if (unique_set.insert(f).second)
	    f->clone();
	  else
	    matched = false;
	}

      if (matched)
	{
	  one_match = true;
	  switch (output_format)
	    {
	    case spot_output:
	    spot::ltl::to_string(f, std::cout, full_parenth);
	    break;
	    case spin_output:
	      spot::ltl::to_spin_string(f, std::cout, full_parenth);
	      break;
	    case utf8_output:
	      spot::ltl::to_utf8_string(f, std::cout, full_parenth);
	      break;
	    }
	  std::cout << "\n";
	}

      f->destroy();
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
  spot::ltl::ltl_simplifier_options options;

  switch (level)
    {
    case 3:
      options.containment_checks = true;
      options.containment_checks_stronger = true;
      // fall through
    case 2:
      options.synt_impl = true;
      // fall through
    case 1:
      options.reduce_basics = true;
      options.event_univ = true;
      // fall through
    default:
      break;
    }

  spot::ltl::ltl_simplifier simpl(options);
  ltl_processor processor(simpl);

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
  return one_match ? 0 : 1;
}

int
main(int argc, char** argv)
{
  set_program_name(argv[0]);
  // Simplify the program name, because argp() uses it to report errors
  // and display help text.
  argv[0] = const_cast<char*>(program_name);

  const argp ap = { options, parse_opt, "[FILENAME...]",
		    argp_program_doc, 0, 0, 0 };

  if (int err = argp_parse(&ap, argc, argv, 0, 0, 0))
    exit(err);

  if (jobs.empty())
    jobs.push_back(job("-", 1));

  return run_jobs();
}
