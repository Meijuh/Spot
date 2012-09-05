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

#ifndef SPOT_BIN_COMMON_OUTPUT_HH
#define SPOT_BIN_COMMON_OUTPUT_HH

#ifdef HAVE_CONFIG_H
# include "config.h"
#endif

#include <argp.h>
#include "ltlast/formula.hh"

enum output_format_t { spot_output, spin_output, utf8_output };
extern output_format_t output_format;
extern bool full_parenth;

extern const struct argp output_argp;

int parse_opt_output(int key, char* arg, struct argp_state* state);
void output_formula(const spot::ltl::formula* f);

#endif // SPOT_BIN_COMMON_OUTPUT_HH
