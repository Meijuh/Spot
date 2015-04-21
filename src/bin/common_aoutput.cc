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
#include "error.h"

#include "common_aoutput.hh"
#include "common_post.hh"
#include "common_cout.hh"
#include "common_post.hh"

#include "tgba/bddprint.hh"

#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/lbtt.hh"
#include "tgbaalgos/hoa.hh"
#include "tgbaalgos/neverclaim.hh"

automaton_format_t automaton_format = Dot;
static const char* opt_dot = nullptr;
static const char* opt_never = nullptr;
static const char* hoa_opt = nullptr;
const char* opt_name = nullptr;
static const char* opt_output = nullptr;
static const char* stats = "";

enum {
  OPT_DOT = 1,
  OPT_LBTT,
  OPT_NAME,
  OPT_STATS,
};

static const argp_option options[] =
  {
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
    { "quiet", 'q', 0, 0, "suppress all normal output", 0 },
    { "spin", 's', "6|c", OPTION_ARG_OPTIONAL, "Spin neverclaim (implies --ba)."
      "  Add letters to select (6) Spin's 6.2.4 style, (c) comments on states",
      0 },
    { "utf8", '8', 0, 0, "enable UTF-8 characters in output "
      "(ignored with --lbtt or --spin)", 0 },
    { "stats", OPT_STATS, "FORMAT", 0,
      "output statistics about the automaton", 0 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp aoutput_argp = { options, parse_opt_aoutput, 0, 0, 0, 0, 0 };

// Those can be overridden by individual tools. E.g. randaut has no
// notion of input file, so %F and %L represent something else.
char F_doc[32] = "name of the input file";
char L_doc[32] = "location in the input file";

static const argp_option io_options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Any FORMAT string may use "\
      "the following interpreted sequences (capitals for input,"
      " minuscules for output):", 4 },
    { "%F", 0, 0, OPTION_DOC | OPTION_NO_USAGE, F_doc, 0 },
    { "%L", 0, 0, OPTION_DOC | OPTION_NO_USAGE, L_doc, 0 },
    { "%M, %m", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "name of the automaton", 0 },
    { "%S, %s", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "number of states", 0 },
    { "%E, %e", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "number of edges", 0 },
    { "%T, %t", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of transitions", 0 },
    { "%A, %a", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of acceptance sets", 0 },
    { "%G, %g", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "acceptance condition (in HOA syntax)", 0 },
    { "%C, %c", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "number of SCCs", 0 },
    { "%n", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of nondeterministic states in output", 0 },
    { "%d", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "1 if the output is deterministic, 0 otherwise", 0 },
    { "%p", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "1 if the output is complete, 0 otherwise", 0 },
    { "%r", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "processing time (excluding parsing) in seconds", 0 },
    { "%w", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "one word accepted by the output automaton", 0 },
    { "%%", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "a single %", 0 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp aoutput_io_format_argp = { io_options, 0, 0, 0, 0, 0, 0 };

static const argp_option o_options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Any FORMAT string may use "\
      "the following interpreted sequences:", 4 },
    { "%F", 0, 0, OPTION_DOC | OPTION_NO_USAGE, F_doc, 0 },
    { "%L", 0, 0, OPTION_DOC | OPTION_NO_USAGE, L_doc, 0 },
    { "%m", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "name of the automaton", 0 },
    { "%s", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "number of states", 0 },
    { "%e", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "number of edges", 0 },
    { "%t", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "number of transitions", 0 },
    { "%a", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of acceptance sets", 0 },
    { "%g", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "acceptance condition (in HOA syntax)", 0 },
    { "%c", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "number of SCCs", 0 },
    { "%n", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "number of nondeterministic states in output", 0 },
    { "%d", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "1 if the output is deterministic, 0 otherwise", 0 },
    { "%p", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "1 if the output is complete, 0 otherwise", 0 },
    { "%r", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "processing time (excluding parsing) in seconds", 0 },
    { "%w", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "one word accepted by the output automaton", 0 },
    { "%%", 0, 0, OPTION_DOC | OPTION_NO_USAGE, "a single %", 0 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp aoutput_o_format_argp = { o_options, 0, 0, 0, 0, 0, 0 };

int parse_opt_aoutput(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case '8':
      spot::enable_utf8();
      break;
    case 'H':
      automaton_format = Hoa;
      hoa_opt = arg;
      break;
    case 'q':
      automaton_format = Quiet;
      break;
    case 's':
      automaton_format = Spin;
      if (type != spot::postprocessor::Monitor)
	type = spot::postprocessor::BA;
      if (arg)
	opt_never = arg;
      break;
    case 'o':
      opt_output = arg;
      break;
    case OPT_DOT:
      automaton_format = Dot;
      opt_dot = arg;
      break;
    case OPT_LBTT:
      if (arg)
	{
	  if (arg[0] == 't' && arg[1] == 0)
	    automaton_format = Lbtt_t;
	  else
	    error(2, 0, "unknown argument for --lbtt: '%s'", arg);
	}
      else
	{
	  automaton_format = Lbtt;
	}
      break;
    case OPT_NAME:
      opt_name = arg;
      break;
    case OPT_STATS:
      if (!*arg)
	error(2, 0, "empty format string for --stats");
      stats = arg;
      automaton_format = Stats;
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}



automaton_printer::automaton_printer(stat_style input)
  : statistics(std::cout, stats, input),
    namer(name, opt_name, input),
    outputnamer(outputname, opt_output, input)
{
  if (automaton_format == Count && opt_output)
    throw std::runtime_error
      ("options --output and --count are incompatible");
}

void
automaton_printer::print(const spot::twa_graph_ptr& aut,
			 const spot::ltl::formula* f,
			 // Input location for errors and statistics.
			 const char* filename,
			 int loc,
			 // Time and input automaton for statistics
			 double time,
			 const spot::const_hoa_aut_ptr& haut)
{
  // Name the output automaton.
  if (opt_name)
    {
      name.str("");
      namer.print(haut, aut, f, filename, loc, time);
      aut->set_named_prop("automaton-name", new std::string(name.str()));
    }

  std::ostream* out = &std::cout;
  if (opt_output)
    {
      outputname.str("");
      outputnamer.print(haut, aut, f, filename, loc, time);
      std::string fname = outputname.str();
      auto p = outputfiles.emplace(fname, nullptr);
      if (p.second)
	p.first->second.reset(new output_file(fname.c_str()));
      out = &p.first->second->ostream();
    }

  // Output it.
  switch (automaton_format)
    {
    case Count:
    case Quiet:
      // Do not output anything.
      break;
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
      statistics.print(haut, aut, f, filename, loc, time) << '\n';
      break;
    }
  flush_cout();
}

void automaton_printer::add_stat(char c, const spot::printable* p)
{
  namer.declare(c, p);
  statistics.declare(c, p);
  outputnamer.declare(c, p);
}
