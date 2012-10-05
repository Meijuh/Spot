// -*- coding: utf-8 -*-
// Copyright (C) 2012 Laboratoire de Recherche et Développement de
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
#include <cstdlib>
#include <cstdio>
#include <argp.h>
#include "error.h"
#include <sstream>

#include "common_setup.hh"
#include "common_cout.hh"
#include "common_finput.hh"
#include "neverparse/public.hh"
#include "ltlast/unop.hh"
#include "ltlvisit/tostring.hh"
#include "ltlvisit/apcollect.hh"
#include "ltlvisit/lbt.hh"
#include "tgbaalgos/lbtt.hh"
#include "tgba/tgbaproduct.hh"
#include "tgbaalgos/gtec/gtec.hh"
#include "tgbaalgos/randomgraph.hh"
#include "tgbaalgos/scc.hh"
#include "tgbaalgos/dotty.hh"
#include "misc/formater.hh"

const char argp_program_doc[] ="\
Call several LTL/PSL translators and cross-compare their output to detect \
bugs, or to gather statistics.  The list of formula to use should be \
supplied on standard input, or using the -f or -F options.\v\
Examples:\n\
\n\
  Compare neverclaim produced by ltl2tgba and spin for some random formulas:\n\
  % randltl --tree-size 20..30 a b c | \\\n\
    ltlcheck 'ltl2tgba -s %f > %N' 'spin -f %s > %N'\n\
";


#define OPT_STATES 1
#define OPT_DENSITY 2

static const argp_option options[] =
  {
    /**************************************************/
    { 0, 0, 0, 0, "Specifying translator to call:", 2 },
    { "translator", 't', "COMMANDFMT", 0,
      "register one translators to call", 0 },
    /**************************************************/
    { 0, 0, 0, 0,
      "COMMANDFMT should specify input and output arguments using the "
      "following character sequences:", 3 },
    { "%f,%s,%l", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "the formula as a (quoted) string in Spot, Spin, or LBT's syntax", 0 },
    { "%F,%S,%L", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "the formula as a file in Spot, Spin, or LBT's syntax", 0 },
    { "%N,%T", 0, 0, OPTION_DOC | OPTION_NO_USAGE,
      "the output automaton as a Never claim, or in LBTT's format", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "State-space generation:", 4 },
    { "states", OPT_STATES, "INT", 0,
      "number of the states in the state-spaces (200 by default)", 0 },
    { "density", OPT_DENSITY, "FLOAT", 0,
      "probability, between 0.0 and 1.0, to add a transition between "
      "two states (0.1 by default)", 0 },
    /**************************************************/
    { 0, 0, 0, 0, "Miscellaneous options:", -1 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp_child children[] =
  {
    { &finput_argp, 0, 0, 1 },
    { 0, 0, 0, 0 }
  };

spot::bdd_dict dict;
unsigned states = 200;
float density = 0.1;

std::vector<char*> translators;

static int
to_int(const char* s)
{
  char* endptr;
  int res = strtol(s, &endptr, 10);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as an integer.", s);
  return res;
}

static int
to_pos_int(const char* s)
{
  int res = to_int(s);
  if (res < 0)
    error(2, 0, "%d is not positive", res);
  return res;
}

static float
to_float(const char* s)
{
  char* endptr;
  // Do not use strtof(), it does not exist on Solaris 9.
  float res = strtod(s, &endptr);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as a float.", s);
  return res;
}

static float
to_probability(const char* s)
{
  float res = to_float(s);
  if (res < 0.0 || res > 1.0)
    error(2, 0, "%f is not between 0 and 1.", res);
  return res;
}


static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case 't':
    case ARGP_KEY_ARG:
      translators.push_back(arg);
      break;
    case OPT_DENSITY:
      density = to_probability(arg);
      break;
    case OPT_STATES:
      states = to_pos_int(arg);
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

static int
create_tmpfile(char c, unsigned int n, std::string& name)
{
  char tmpname[30];
  snprintf(tmpname, sizeof tmpname, "lck-%c%u-XXXXXX", c, n);
  int fd = mkstemp(tmpname);
  if (fd == -1)
    error(2, errno, "failed to create a temporary file");
  name = tmpname;
  return fd;
}

namespace
{
  struct quoted_string: public spot::printable_value<std::string>
  {
    using spot::printable_value<std::string>::operator=;

    void
    print(std::ostream& os, const char* pos) const
    {
      os << '\'';
      this->spot::printable_value<std::string>::print(os, pos);
      os << '\'';
    }
  };

  struct printable_result_filename: public spot::printable_value<std::string>
  {
    unsigned translator_num;
    enum output_format { None, Spin, Lbtt };
    mutable output_format format;

    void reset(unsigned n)
    {
      val_.clear();
      translator_num = n;
      format = None;
    }

    void
    print(std::ostream& os, const char* pos) const
    {
      if (*pos == 'N')
	format = Spin;
      else
	format = Lbtt;
      if (!val_.empty())
	error(2, 0, "you may have only one %%N or %%T specifier: %s",
	      translators[translator_num]);
      close(create_tmpfile('o', translator_num,
			   const_cast<std::string&>(val_)));
      os << '\'' << val_ << '\'';
    }
  };

  class translator_runner: protected spot::formater
  {
  private:
    // Round-specific variables
    quoted_string string_ltl_spot;
    quoted_string string_ltl_spin;
    quoted_string string_ltl_lbt;
    quoted_string filename_ltl_spot;
    quoted_string filename_ltl_spin;
    quoted_string filename_ltl_lbt;
    std::list<std::string> toclean;
    // Run-specific variables
    printable_result_filename output;
  public:
    translator_runner()
    {
      declare('f', &string_ltl_spot);
      declare('s', &string_ltl_spin);
      declare('l', &string_ltl_lbt);
      declare('F', &filename_ltl_spot);
      declare('S', &filename_ltl_spin);
      declare('L', &filename_ltl_lbt);
      declare('N', &output);
      declare('T', &output);

      size_t s = translators.size();
      assert(s);
      for (size_t n = 0; n < s; ++n)
	prime(translators[n]);

    }

    // Cleanup temporary files.
    void round_cleanup()
    {
      for (std::list<std::string>::const_iterator i = toclean.begin();
	   i != toclean.end(); ++i)
	unlink(i->c_str());
      toclean.clear();
    }

    void
    string_to_tmp(std::string& str, unsigned n, std::string& tmpname)
    {
      int fd = create_tmpfile('i', n, tmpname);
      write(fd, str.c_str(), str.size());
      write(fd, "\n", 1);
      close(fd);
      toclean.push_back(tmpname);
    }

    const std::string& formula() const
    {
      // Pick the most readable format we have...
      if (!string_ltl_spot.val().empty())
	return string_ltl_spot;
      if (!string_ltl_spin.val().empty())
	return string_ltl_spin;
      if (!string_ltl_lbt.val().empty())
	return string_ltl_lbt;
      error(2, 0, "None of the translators need the input formula?");
      return string_ltl_spot;
    }

    void round_formula(const spot::ltl::formula* f, unsigned serial)
    {
      if (has('f') || has('F'))
	string_ltl_spot = spot::ltl::to_string(f, true);
      if (has('s') || has('S'))
	string_ltl_spin = spot::ltl::to_spin_string(f, true);
      if (has('l') || has('L'))
	string_ltl_lbt = spot::ltl::to_lbt_string(f);
      if (has('F'))
	string_to_tmp(string_ltl_spot, serial, filename_ltl_spot);
      if (has('S'))
	string_to_tmp(string_ltl_spin, serial, filename_ltl_spin);
      if (has('L'))
	string_to_tmp(string_ltl_lbt, serial, filename_ltl_lbt);
    }

    const spot::tgba* translate(unsigned int translator_num, char l)
    {
      output.reset(translator_num);

      std::ostringstream command;
      format(command, translators[translator_num]);
      toclean.push_back(output.val());
      std::string cmd = command.str();
      std::cerr << "Running [" << l << translator_num << "]: "
		<< cmd << std::endl;
      int es = system(cmd.c_str());

      const spot::tgba* res = 0;
      if (es)
	{
	  std::cerr << "Execution of: " << cmd << "\n"
		    << "  returned exit code " << WEXITSTATUS(es)
		    << ".\n";
	}
      else
	{
	  switch (output.format)
	    {
	    case printable_result_filename::Spin:
	      {
		spot::neverclaim_parse_error_list pel;
		res = spot::neverclaim_parse(output, pel, &dict);
		if (!pel.empty())
		  {
		    std::cerr << "Failed to parse the produced neverclaim.\n";
		    spot::format_neverclaim_parse_errors(std::cerr,
							 output, pel);
		    delete res;
		    res = 0;
		  }
		break;
	      }
	    case printable_result_filename::Lbtt:
	      {
		std::string error;
		std::fstream f(output.val().c_str());
		if (!f)
		  {
		    std::cerr << "Cannot open " << output.val() << std::endl;
		  }
		else
		  {
		    res = spot::lbtt_parse(f, output.val(), &dict);
		if (!res)
		  std::cerr << "Failed error to parse output in LBTT format: "
			    << error << std::endl;
		  }
		break;
	      }
	    case printable_result_filename::None:
	      assert(!"unreachable code");
	    }
	}
      return res;
    }
  };

  static bool
  is_empty(const spot::tgba* aut)
  {
    spot::emptiness_check* ec = spot::couvreur99(aut);
    spot::emptiness_check_result* res = ec->check();
    delete res;
    delete ec;
    return !res;
  }

  static void
  cross_check(const std::vector<spot::scc_map*>& maps, char l)
  {
    size_t m = maps.size();

    std::vector<bool> res(m);
    unsigned verified = 0;
    unsigned violated = 0;
    for (size_t i = 0; i < m; ++i)
      if (spot::scc_map* m = maps[i])
	{
	  // r == true iff the automaton i is accepting.
	  bool r = false;
	  unsigned c = m->scc_count();
	  for (unsigned j = 0; (j < c) && !r; ++j)
	    r |= m->accepting(j);
	  res[i] = r;
	  if (r)
	    ++verified;
	  else
	    ++violated;
	}
    if (verified != 0 && violated != 0)
      {
	std::cerr << "error: {";
	bool first = true;
	for (size_t i = 0; i < m; ++i)
	  if (maps[i] && res[i])
	    {
	      if (first)
		first = false;
	      else
		std::cerr << ",";
	      std::cerr << l << i;
	    }
	std::cerr << "} disagree with {";
	first = true;
	for (size_t i = 0; i < m; ++i)
	  if (maps[i] && !res[i])
	    {
	      if (first)
		first = false;
	      else
		std::cerr << ",";
	      std::cerr << l << i;
	    }
	std::cerr << "} when evaluating the state-space\n";
      }
  }

  typedef std::set<spot::state*, spot::state_ptr_less_than> state_set;

  // Collect all the states of SSPACE that appear in the accepting SCCs
  // of PROD.
  static void
  states_in_acc(const spot::scc_map* m, const spot::tgba* sspace,
		state_set& s)
  {
    const spot::tgba* aut = m->get_aut();
    unsigned c = m->scc_count();
    for (unsigned n = 0; n < c; ++n)
      if (m->accepting(n))
	{
	  const std::list<const spot::state*>& l = m->states_of(n);
	  for (std::list<const spot::state*>::const_iterator i = l.begin();
	       i != l.end(); ++i)
	    {
	      spot::state* x = aut->project_state(*i, sspace);
	      if (!s.insert(x).second)
		x->destroy();
	    }
	}
  }

  static bool
  consistency_check(const spot::scc_map* pos, const spot::scc_map* neg,
		    const spot::tgba* sspace)
  {
    // the states of SSPACE should appear in the accepting SCC of at
    // least one of POS or NEG.  Maybe both.
    state_set s;
    states_in_acc(pos, sspace, s);
    states_in_acc(neg, sspace, s);
    bool res = s.size() == states;
    state_set::iterator it;
    for (it = s.begin(); it != s.end(); it++)
      (*it)->destroy();
    return res;
  }

  class processor: public job_processor
  {
    translator_runner runner;

  public:
    int
    process_formula(const spot::ltl::formula* f,
		    const char* filename = 0, int linenum = 0)
    {
      (void) filename;
      (void) linenum;
      static unsigned round = 0;

      size_t m = translators.size();

      std::vector<const spot::tgba*> pos(m);
      std::vector<const spot::tgba*> neg(m);

      runner.round_formula(f, round);
      // Call formula() before printing anything else, in case it
      // complains.
      std::string fstr = runner.formula();
      if (filename)
	std::cerr << filename << ":";
      if (linenum)
	std::cerr << linenum << ":";
      if (filename || linenum)
	std::cerr << " ";
      std::cerr << fstr << "\n";

      for (size_t n = 0; n < m; ++n)
	pos[n] = runner.translate(n, 'P');

      const spot::ltl::formula* nf =
	spot::ltl::unop::instance(spot::ltl::unop::Not, f->clone());
      runner.round_formula(nf, round);
      for (size_t n = 0; n < m; ++n)
	neg[n] = runner.translate(n, 'N');

      ++round;
      runner.round_cleanup();

      spot::ltl::atomic_prop_set* ap = spot::ltl::atomic_prop_collect(f);

      // intersection test
      for (size_t i = 0; i < m; ++i)
	if (pos[i])
	  for (size_t j = 0; j < m; ++j)
	    if (neg[j])
	      {
		spot::tgba_product* prod =
		  new spot::tgba_product(pos[i], neg[j]);
		if (!is_empty(prod))
		  std::cerr << "error: P" << i << "*N" << j << " is nonempty\n";
		delete prod;
	      }

      // build products with a random state-space.
      spot::tgba* statespace = spot::random_graph(states, density, ap, &dict);

      std::vector<spot::tgba*> pos_prod(m);
      std::vector<spot::tgba*> neg_prod(m);
      std::vector<spot::scc_map*> pos_map(m);
      std::vector<spot::scc_map*> neg_map(m);
      for (size_t i = 0; i < m; ++i)
	if (pos[i])
	  {
	    spot::tgba* p = new spot::tgba_product(pos[i], statespace);
	    pos_prod[i] = p;
	    spot::scc_map* sm = new spot::scc_map(p);
	    sm->build_map();
	    pos_map[i] = sm;
	  }
      for (size_t i = 0; i < m; ++i)
	if (neg[i])
	  {
	    spot::tgba* p = new spot::tgba_product(neg[i], statespace);
	    neg_prod[i] = p;
	    spot::scc_map* sm = new spot::scc_map(p);
	    sm->build_map();
	    neg_map[i] = sm;
	  }

      // cross-comparison test
      cross_check(pos_map, 'P');
      cross_check(neg_map, 'N');

      // consistency check
      for (size_t i = 0; i < m; ++i)
	if (pos_map[i] && neg_map[i] &&
	    !(consistency_check(pos_map[i], neg_map[i], statespace)))
	  {
	    std::cerr << "error: inconsistency between P" << i
		      << " and N" << i << "\n";
	  }

      // Cleanup.
      delete ap;
      nf->destroy();
      f->destroy();

      for (size_t n = 0; n < m; ++n)
	{
	  delete neg_map[n];
	  delete neg_prod[n];
	  delete pos_map[n];
	  delete pos_prod[n];
	}

      delete statespace;

      for (size_t n = 0; n < m; ++n)
	{
	  delete neg[n];
	  delete pos[n];
	}

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

  if (int err = argp_parse(&ap, argc, argv, 0, 0, 0))
    exit(err);

  if (jobs.empty())
    jobs.push_back(job("-", 1));

  if (translators.empty())
    error(2, 0, "No translator to run?  Run '%s --help' for usage.",
	  program_name);

  processor p;
  if (p.run())
    return 2;
  return 0;
}
