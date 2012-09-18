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

#ifndef SPOT_BIN_COMMON_FINPUT_HH
#define SPOT_BIN_COMMON_FINPUT_HH

#include "common_sys.hh"

#include <argp.h>
#include <vector>
#include "ltlparse/public.hh"

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
extern jobs_t jobs;
extern bool lbt_input;

extern const struct argp finput_argp;

int parse_opt_finput(int key, char* arg, struct argp_state* state);

const spot::ltl::formula*
parse_formula(const std::string& s, spot::ltl::parse_error_list& error_list);


#endif // SPOT_BIN_COMMON_FINPUT_HH
