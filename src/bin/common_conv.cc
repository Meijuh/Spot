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

#include "common_conv.hh"
#include <cstdlib>
#include "error.h"
#include "hoaparse/public.hh"

int
to_int(const char* s)
{
  char* endptr;
  int res = strtol(s, &endptr, 10);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as an integer.", s);
  return res;
}

int
to_pos_int(const char* s)
{
  int res = to_int(s);
  if (res < 0)
    error(2, 0, "%d is not positive", res);
  return res;
}

unsigned
to_unsigned (const char *s)
{
  char* endptr;
  unsigned res = strtoul(s, &endptr, 10);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as an unsigned integer.", s);
  return res;
}

float
to_float(const char* s)
{
  char* endptr;
  float res = strtof(s, &endptr);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as a float.", s);
  return res;
}

float
to_probability(const char* s)
{
  float res = to_float(s);
  if (res < 0.0 || res > 1.0)
    error(2, 0, "%f is not between 0 and 1.", res);
  return res;
}

spot::tgba_digraph_ptr
read_automaton(const char* filename, spot::bdd_dict_ptr& dict)
{
  spot::hoa_parse_error_list pel;
  auto p = spot::hoa_parse(filename, pel, dict);
  if (spot::format_hoa_parse_errors(std::cerr, filename, pel)
      || !p || p->aborted)
    error(2, 0, "failed to read automaton from %s", filename);
  return std::move(p->aut);
}

std::vector<long>
to_longs(const char* arg)
{
  std::vector<long> res;
  while (*arg)
    {
      char* endptr;
      long value = strtol(arg, &endptr, 10);
      if (endptr == arg)
        error(2, 0, "failed to parse '%s' as an integer.", arg);
      res.push_back(value);
      while (*endptr == ' ' || *endptr == ',')
        ++endptr;
      arg = endptr;
    }
  return res;
}
