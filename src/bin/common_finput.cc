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

#include "common_finput.hh"
#include "error.h"
#include "ltlparse/public.hh"

#include <fstream>

#define OPT_LBT 1

jobs_t jobs;
bool lbt_input = false;

static const argp_option options[] =
  {
    { 0, 0, 0, 0, "Input options:", 1 },
    { "formula", 'f', "STRING", 0, "process the formula STRING", 0 },
    { "file", 'F', "FILENAME", 0,
      "process each line of FILENAME as a formula", 0 },
    { "lbt-input", OPT_LBT, 0, 0,
      "read all formulas using LBT's prefix syntax", 0 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp finput_argp = { options, parse_opt_finput, 0, 0, 0, 0, 0 };

int
parse_opt_finput(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case 'f':
      jobs.push_back(job(arg, false));
      break;
    case 'F':
      jobs.push_back(job(arg, true));
      break;
    case OPT_LBT:
      lbt_input = true;
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

const spot::ltl::formula*
parse_formula(const std::string& s, spot::ltl::parse_error_list& pel)
{
  if (lbt_input)
    return spot::ltl::parse_lbt(s, pel);
  else
    return spot::ltl::parse(s, pel);
}


int
job_processor::process_string(const std::string& input,
			      const char* filename,
			      int linenum)
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
  return process_formula(f, filename, linenum);
}

int
job_processor::process_stream(std::istream& is,
			      const char* filename)
{
  int error = 0;
  int linenum = 0;
  std::string line;
  while (std::getline(is, line))
    error |= process_string(line, filename, ++linenum);
  return error;
}

int
job_processor::process_file(const char* filename)
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

int
job_processor::run()
{
  int error = 0;
  jobs_t::const_iterator i;
  for (i = jobs.begin(); i != jobs.end(); ++i)
    {
      if (!i->file_p)
	error |= process_string(i->str);
      else
	error |= process_file(i->str);
    }
  return error;
}
