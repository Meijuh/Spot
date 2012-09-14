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

#include "common_output.hh"
#include <iostream>
#include "ltlvisit/tostring.hh"
#include "common_cout.hh"

#define OPT_SPOT 1

output_format_t output_format = spot_output;
bool full_parenth = false;

static const argp_option options[] =
  {
    { "full-parentheses", 'p', 0, 0,
      "output fully-parenthesized formulas", -20 },
    { "spin", 's', 0, 0, "output in Spin's syntax", -20 },
    { "spot", OPT_SPOT, 0, 0, "output in Spot's syntax (default)", -20 },
    { "utf8", '8', 0, 0, "output using UTF-8 characters", -20 },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp output_argp = { options, parse_opt_output, 0, 0, 0, 0, 0 };

int
parse_opt_output(int key, char*, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case '8':
      output_format = utf8_output;
      break;
    case 'p':
      full_parenth = true;
      break;
    case 's':
      output_format = spin_output;
      break;
    case OPT_SPOT:
      output_format = spot_output;
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

void
output_formula(const spot::ltl::formula* f)
{
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
  // Make sure we abort if we can't write to std::cout anymore
  // (like disk full or broken pipe with SIGPIPE ignored).
  std::cout << std::endl;
  check_cout();
}
