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

#include <cstdlib>
#include <string>
#include <iostream>
#include <fstream>
#include <argp.h>
#include <cstring>
#include "error.h"

#include "common_setup.hh"
#include "common_finput.hh"
#include "common_output.hh"
#include "common_cout.hh"
#include "common_conv.hh"
#include "common_r.hh"

#include "misc/hash.hh"
#include "ltlvisit/simplify.hh"
#include "ltlvisit/length.hh"
#include "ltlvisit/relabel.hh"
#include "ltlvisit/unabbrev.hh"
#include "ltlvisit/remove_x.hh"
#include "ltlvisit/apcollect.hh"
#include "ltlvisit/exclusive.hh"
#include "ltlvisit/print.hh"
#include "twaalgos/ltl2tgba_fm.hh"
#include "twaalgos/minimize.hh"
#include "twaalgos/safety.hh"
#include "twaalgos/stutter.hh"

const char argp_program_doc[] ="\
Read a list of formulas and output them back after some optional processing.\v\
Exit status:\n\
  0  if some formulas were output (skipped syntax errors do not count)\n\
  1  if no formulas were output (no match)\n\
  2  if any error has been reported";

enum {
  OPT_AP_N = 256,
  OPT_BOOLEAN,
  OPT_BOOLEAN_TO_ISOP,
  OPT_BSIZE_MAX,
  OPT_BSIZE_MIN,
  OPT_DEFINE,
  OPT_DROP_ERRORS,
  OPT_EQUIVALENT_TO,
  OPT_EXCLUSIVE_AP,
  OPT_EVENTUAL,
  OPT_GUARANTEE,
  OPT_IGNORE_ERRORS,
  OPT_IMPLIED_BY,
  OPT_IMPLY,
  OPT_LTL,
  OPT_NEGATE,
  OPT_NNF,
  OPT_OBLIGATION,
  OPT_RELABEL,
  OPT_RELABEL_BOOL,
  OPT_REMOVE_WM,
  OPT_REMOVE_X,
  OPT_SAFETY,
  OPT_SIZE_MAX,
  OPT_SIZE_MIN,
  OPT_SKIP_ERRORS,
  OPT_STUTTER_INSENSITIVE,
  OPT_SYNTACTIC_GUARANTEE,
  OPT_SYNTACTIC_OBLIGATION,
  OPT_SYNTACTIC_PERSISTENCE,
  OPT_SYNTACTIC_RECURRENCE,
  OPT_SYNTACTIC_SAFETY,
  OPT_SYNTACTIC_SI,
  OPT_UNABBREVIATE,
  OPT_UNIVERSAL,
};

static const argp_option options[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Error handling:", 2 },
    { "skip-errors", OPT_SKIP_ERRORS, nullptr, 0,
      "output erroneous lines as-is without processing", 0 },
    { "drop-errors", OPT_DROP_ERRORS, nullptr, 0,
      "discard erroneous lines (default)", 0 },
    { "ignore-errors", OPT_IGNORE_ERRORS, nullptr, 0,
      "do not report syntax errors", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Transformation options:", 3 },
    { "negate", OPT_NEGATE, nullptr, 0, "negate each formula", 0 },
    { "nnf", OPT_NNF, nullptr, 0,
      "rewrite formulas in negative normal form", 0 },
    { "relabel", OPT_RELABEL, "abc|pnn", OPTION_ARG_OPTIONAL,
      "relabel all atomic propositions, alphabetically unless " \
      "specified otherwise", 0 },
    { "relabel-bool", OPT_RELABEL_BOOL, "abc|pnn", OPTION_ARG_OPTIONAL,
      "relabel Boolean subexpressions, alphabetically unless " \
      "specified otherwise", 0 },
    { "define", OPT_DEFINE, "FILENAME", OPTION_ARG_OPTIONAL,
      "when used with --relabel or --relabel-bool, output the relabeling map "
      "using #define statements", 0 },
    { "remove-wm", OPT_REMOVE_WM, nullptr, 0,
      "rewrite operators W and M using U and R (this is an alias for "
      "--unabbreviate=WM)", 0 },
    { "boolean-to-isop", OPT_BOOLEAN_TO_ISOP, nullptr, 0,
      "rewrite Boolean subformulas as irredundant sum of products "
      "(implies at least -r1)", 0 },
    { "remove-x", OPT_REMOVE_X, nullptr, 0,
      "remove X operators (valid only for stutter-insensitive properties)",
      0 },
    { "unabbreviate", OPT_UNABBREVIATE, "STR", OPTION_ARG_OPTIONAL,
      "remove all occurrences of the operators specified by STR, which "
      "must be a substring of \"eFGiMRW^\", where 'e', 'i', and '^' stand "
      "respectively for <->, ->, and xor.  If no argument is passed, "
      "the subset \"eFGiMW^\" is used.", 0 },
    { "exclusive-ap", OPT_EXCLUSIVE_AP, "AP,AP,...", 0,
      "if any of those APs occur in the formula, add a term ensuring "
      "two of them may not be true at the same time.  Use this option "
      "multiple times to declare independent groups of exclusive "
      "propositions.", 0 },
    DECLARE_OPT_R,
    LEVEL_DOC(4),
    /**************************************************/
    { nullptr, 0, nullptr, 0,
      "Filtering options (matching is done after transformation):", 5 },
    { "ltl", OPT_LTL, nullptr, 0,
      "match only LTL formulas (no PSL operator)", 0 },
    { "boolean", OPT_BOOLEAN, nullptr, 0, "match Boolean formulas", 0 },
    { "eventual", OPT_EVENTUAL, nullptr, 0, "match pure eventualities", 0 },
    { "universal", OPT_UNIVERSAL, nullptr, 0,
      "match purely universal formulas", 0 },
    { "syntactic-safety", OPT_SYNTACTIC_SAFETY, nullptr, 0,
      "match syntactic-safety formulas", 0 },
    { "syntactic-guarantee", OPT_SYNTACTIC_GUARANTEE, nullptr, 0,
      "match syntactic-guarantee formulas", 0 },
    { "syntactic-obligation", OPT_SYNTACTIC_OBLIGATION, nullptr, 0,
      "match syntactic-obligation formulas", 0 },
    { "syntactic-recurrence", OPT_SYNTACTIC_RECURRENCE, nullptr, 0,
      "match syntactic-recurrence formulas", 0 },
    { "syntactic-persistence", OPT_SYNTACTIC_PERSISTENCE, nullptr, 0,
      "match syntactic-persistence formulas", 0 },
    { "syntactic-stutter-invariant", OPT_SYNTACTIC_SI, nullptr, 0,
      "match stutter-invariant formulas syntactically (LTL-X or siPSL)", 0 },
    { "nox", 0, nullptr, OPTION_ALIAS, nullptr, 0 },
    { "safety", OPT_SAFETY, nullptr, 0,
      "match safety formulas (even pathological)", 0 },
    { "guarantee", OPT_GUARANTEE, nullptr, 0,
      "match guarantee formulas (even pathological)", 0 },
    { "obligation", OPT_OBLIGATION, nullptr, 0,
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
    { "stutter-insensitive", OPT_STUTTER_INSENSITIVE, nullptr, 0,
      "match stutter-insensitive LTL formulas", 0 },
    { "stutter-invariant", 0, nullptr, OPTION_ALIAS, nullptr, 0 },
    { "ap", OPT_AP_N, "N", 0,
      "match formulas which use exactly N atomic propositions", 0 },
    { "invert-match", 'v', nullptr, 0, "select non-matching formulas", 0},
    { "unique", 'u', nullptr, 0,
      "drop formulas that have already been output (not affected by -v)", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", -20 },
    { "count", 'c', nullptr, 0, "print only a count of matched formulas", 0 },
    { "quiet", 'q', nullptr, 0, "suppress all normal output", 0 },
    { "max-count", 'n', "NUM", 0, "output at most NUM formulas", 0 },
    { nullptr, 0, nullptr, 0, "The FORMAT string passed to --format may use "\
      "the following interpreted sequences:", -19 },
    { "%f", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the formula (in the selected syntax)", 0 },
    { "%F", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the name of the input file", 0 },
    { "%L", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the original line number in the input file", 0 },
    { "%<", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the part of the line before the formula if it "
      "comes from a column extracted from a CSV file", 0 },
    { "%>", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the part of the line after the formula if it "
      "comes from a column extracted from a CSV file", 0 },
    { "%%", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "a single %", 0 },
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

const struct argp_child children[] =
  {
    { &finput_argp, 0, nullptr, 1 },
    { &output_argp, 0, nullptr, -20 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

static bool one_match = false;

enum error_style_t { drop_errors, skip_errors };
static error_style_t error_style = drop_errors;
static bool ignore_errors = false;
static bool nnf = false;
static bool negate = false;
static bool boolean_to_isop = false;
static bool unique = false;
static bool psl = false;
static bool ltl = false;
static bool invert = false;
static bool boolean = false;
static bool universal = false;
static bool eventual = false;
static bool syntactic_safety = false;
static bool syntactic_guarantee = false;
static bool syntactic_obligation = false;
static bool syntactic_recurrence = false;
static bool syntactic_persistence = false;
static bool syntactic_si = false;
static bool safety = false;
static bool guarantee = false;
static bool obligation = false;
static int size_min = -1;
static int size_max = -1;
static int bsize_min = -1;
static int bsize_max = -1;
enum relabeling_mode { NoRelabeling = 0, ApRelabeling, BseRelabeling };
static relabeling_mode relabeling = NoRelabeling;
static spot::ltl::relabeling_style style = spot::ltl::Abc;
static bool remove_x = false;
static bool stutter_insensitive = false;
static bool ap = false;
static unsigned ap_n = 0;
static int opt_max_count = -1;
static long int match_count = 0;
static spot::exclusive_ap excl_ap;
static std::unique_ptr<output_file> output_define = nullptr;
static std::string unabbreviate;

static spot::ltl::formula implied_by = nullptr;
static spot::ltl::formula imply = nullptr;
static spot::ltl::formula equivalent_to = nullptr;

static spot::ltl::formula
parse_formula_arg(const std::string& input)
{
  spot::ltl::parse_error_list pel;
  spot::ltl::formula f = parse_formula(input, pel);
  if (spot::ltl::format_parse_errors(std::cerr, input, pel))
    error(2, 0, "parse error when parsing an argument");
  return f;
}

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case 'c':
      output_format = count_output;
      break;
    case 'n':
      opt_max_count = to_pos_int(arg);
      break;
    case 'q':
      output_format = quiet_output;
      break;
    case OPT_R:
      parse_r(arg);
      break;
    case 'u':
      unique = true;
      break;
    case 'v':
      invert = true;
      break;
    case ARGP_KEY_ARG:
      // FIXME: use stat() to distinguish filename from string?
      jobs.emplace_back(arg, true);
      break;
    case OPT_BOOLEAN:
      boolean = true;
      break;
    case OPT_BOOLEAN_TO_ISOP:
      boolean_to_isop = true;
      break;
    case OPT_BSIZE_MIN:
      bsize_min = to_int(arg);
      break;
    case OPT_BSIZE_MAX:
      bsize_max = to_int(arg);
      break;
    case OPT_DEFINE:
      output_define.reset(new output_file(arg ? arg : "-"));
      break;
    case OPT_DROP_ERRORS:
      error_style = drop_errors;
      break;
    case OPT_EVENTUAL:
      eventual = true;
      break;
    case OPT_EQUIVALENT_TO:
      {
	if (equivalent_to)
	  error(2, 0, "only one --equivalent-to option can be given");
	equivalent_to = parse_formula_arg(arg);
	break;
      }
    case OPT_EXCLUSIVE_AP:
      excl_ap.add_group(arg);
      break;
    case OPT_GUARANTEE:
      guarantee = obligation = true;
      break;
    case OPT_IGNORE_ERRORS:
      ignore_errors = true;
      break;
    case OPT_IMPLIED_BY:
      {
	spot::ltl::formula i = parse_formula_arg(arg);
	// a→c∧b→c ≡ (a∨b)→c
	implied_by = spot::ltl::formula::Or({implied_by, i});
	break;
      }
    case OPT_IMPLY:
      {
	// a→b∧a→c ≡ a→(b∧c)
	spot::ltl::formula i = parse_formula_arg(arg);
	imply = spot::ltl::formula::And({imply, i});
	break;
      }
    case OPT_LTL:
      ltl = true;
      break;
    case OPT_NEGATE:
      negate = true;
      break;
    case OPT_NNF:
      nnf = true;
      break;
    case OPT_OBLIGATION:
      obligation = true;
      break;
    case OPT_RELABEL:
    case OPT_RELABEL_BOOL:
      relabeling = (key == OPT_RELABEL_BOOL ? BseRelabeling : ApRelabeling);
      if (!arg || !strncasecmp(arg, "abc", 6))
	style = spot::ltl::Abc;
      else if (!strncasecmp(arg, "pnn", 4))
	style = spot::ltl::Pnn;
      else
	error(2, 0, "invalid argument for --relabel%s: '%s'",
	      (key == OPT_RELABEL_BOOL ? "-bool" : ""),
	      arg);
      break;
    case OPT_REMOVE_WM:
      unabbreviate += "MW";
      break;
    case OPT_REMOVE_X:
      remove_x = true;
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
    case OPT_STUTTER_INSENSITIVE:
      stutter_insensitive = true;
      break;
    case OPT_UNABBREVIATE:
      if (arg)
	unabbreviate += arg;
      else
	unabbreviate += spot::ltl::default_unabbrev_string;
      break;
    case OPT_AP_N:
      ap = true;
      ap_n = to_int(arg);
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
    case OPT_SYNTACTIC_SI:
      syntactic_si = true;
      break;
    case OPT_UNIVERSAL:
      universal = true;
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

typedef
std::unordered_set<spot::ltl::formula> fset_t;

namespace
{
  class ltl_processor: public job_processor
  {
  public:
    spot::ltl::ltl_simplifier& simpl;
    fset_t unique_set;
    spot::ltl::relabeling_map relmap;

    ltl_processor(spot::ltl::ltl_simplifier& simpl)
      : simpl(simpl)
    {
    }

    int
    process_string(const std::string& input,
		    const char* filename = nullptr, int linenum = 0)
    {
      spot::ltl::parse_error_list pel;
      spot::ltl::formula f = parse_formula(input, pel);

      if (!f || pel.size() > 0)
	  {
	    if (!ignore_errors)
	      {
		if (filename)
		  error_at_line(0, 0, filename, linenum, "parse error:");
		spot::ltl::format_parse_errors(std::cerr, input, pel);
	      }

	    if (error_style == skip_errors)
	      std::cout << input << std::endl;
	    else
	      assert(error_style == drop_errors);
	    check_cout();
	    return !ignore_errors;
	  }
      try
	{
	  return process_formula(f, filename, linenum);
	}
      catch (const std::runtime_error& e)
	{
	  error_at_line(2, 0, filename, linenum, "%s", e.what());
	  SPOT_UNREACHABLE();
	}
    }

    int
    process_formula(spot::ltl::formula f,
		    const char* filename = nullptr, int linenum = 0)
    {
      if (opt_max_count >= 0 && match_count >= opt_max_count)
	{
	  abort_run = true;
	  return 0;
	}

      if (negate)
	f = spot::ltl::formula::Not(f);

      if (remove_x)
	{
	  // If simplification are enabled, we do them before and after.
	  if (simplification_level)
	    f = simpl.simplify(f);
	  f = spot::ltl::remove_x(f);
	}

      if (simplification_level || boolean_to_isop)
	f = simpl.simplify(f);

      if (nnf)
	f = simpl.negative_normal_form(f);

      switch (relabeling)
	{
	case ApRelabeling:
	  {
	    relmap.clear();
	    f = spot::ltl::relabel(f, style, &relmap);
	    break;
	  }
	case BseRelabeling:
	  {
	    relmap.clear();
	    f = spot::ltl::relabel_bse(f, style, &relmap);
	    break;
	  }
	case NoRelabeling:
	  break;
	}

      if (!unabbreviate.empty())
	f = spot::ltl::unabbreviate(f, unabbreviate.c_str());

      if (!excl_ap.empty())
	f = excl_ap.constrain(f);

      bool matched = true;

      matched &= !ltl || f.is_ltl_formula();
      matched &= !psl || f.is_psl_formula();
      matched &= !boolean || f.is_boolean();
      matched &= !universal || f.is_universal();
      matched &= !eventual || f.is_eventual();
      matched &= !syntactic_safety || f.is_syntactic_safety();
      matched &= !syntactic_guarantee || f.is_syntactic_guarantee();
      matched &= !syntactic_obligation || f.is_syntactic_obligation();
      matched &= !syntactic_recurrence || f.is_syntactic_recurrence();
      matched &= !syntactic_persistence || f.is_syntactic_persistence();
      matched &= !syntactic_si || f.is_syntactic_stutter_invariant();
      matched &= !ap || atomic_prop_collect(f)->size() == ap_n;

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
      matched &= !stutter_insensitive || spot::is_stutter_invariant(f);

      // Match obligations and subclasses using WDBA minimization.
      // Because this is costly, we compute it later, so that we don't
      // have to compute it on formulas that have been discarded for
      // other reasons.
      if (matched && obligation)
	{
	  auto aut = ltl_to_tgba_fm(f, simpl.get_dict());
	  auto min = minimize_obligation(aut, f);
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
	    }
	}

      matched ^= invert;

      if (unique && !unique_set.insert(f).second)
	matched = false;

      if (matched)
	{
	  if (output_define
	      && output_format != count_output
	      && output_format != quiet_output)
	    {
	      // Sort the formulas alphabetically.
	      std::map<std::string, spot::ltl::formula> m;
	      for (auto& p: relmap)
		m.emplace(str_psl(p.first), p.second);
	      for (auto& p: m)
		stream_formula(output_define->ostream()
			       << "#define " << p.first << " (",
			       p.second, filename, linenum) << ")\n";
	    }
	  one_match = true;
	  output_formula_checked(f, filename, linenum, prefix, suffix);
	  ++match_count;
	}
      return 0;
    }
  };
}

int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, parse_opt, "[FILENAME[/COL]...]",
		    argp_program_doc, children, nullptr, nullptr };

  try
    {
      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
	exit(err);

      if (jobs.empty())
	jobs.emplace_back("-", 1);

      if (boolean_to_isop && simplification_level == 0)
	simplification_level = 1;
      spot::ltl::ltl_simplifier_options opt(simplification_level);
      opt.boolean_to_isop = boolean_to_isop;
      spot::ltl::ltl_simplifier simpl(opt);

      ltl_processor processor(simpl);
      if (processor.run())
	return 2;
    }
  catch (const std::runtime_error& e)
    {
      error(2, 0, "%s", e.what());
    }
  catch (const std::invalid_argument& e)
    {
      error(2, 0, "%s", e.what());
    }

  if (output_format == count_output)
    std::cout << match_count << std::endl;

  return one_match ? 0 : 1;
}
