// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014, 2015, 2016, 2017 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
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

#pragma once

#include "common_sys.hh"

#include <argp.h>
#include <map>
#include <memory>
#include <spot/tl/formula.hh>
#include <spot/twaalgos/stats.hh>
#include <spot/misc/timer.hh>
#include "common_output.hh"
#include "common_file.hh"

enum output_format_t { spot_output, spin_output, utf8_output,
                       lbt_output, wring_output, latex_output,
                       quiet_output, count_output };
extern output_format_t output_format;
extern bool full_parenth;
extern bool escape_csv;

#define COMMON_X_OUTPUT_SPECS(where)                                    \
      "number of atomic propositions " #where "; "      \
      " add LETTERS to list atomic propositions with "                  \
      "(n) no quoting, "                                                \
      "(s) occasional double-quotes with C-style escape, "              \
      "(d) double-quotes with C-style escape, "                         \
      "(c) double-quotes with CSV-style escape, "                       \
      "(p) between parentheses, "                                       \
      "any extra non-alphanumeric character will be used to "           \
      "separate propositions"

#define COMMON_LTL_OUTPUT_SPECS                                         \
    { "%s", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,                   \
        "the length (or size) of the formula", 0 },                     \
    { "%b", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,                   \
        "the Boolean-length of the formula (i.e., all Boolean "         \
        "subformulas count as 1)", 0 },                                 \
    { "%h, %[vw]h", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,           \
        "the class of the formula is the Manna-Pnueli hierarchy "       \
        "([v] replaces abbreviations by class names, [w] for all "      \
        "compatible classes)", 0 },                                     \
    { "%x, %[LETTERS]X, %[LETTERS]x", 0, nullptr,                       \
        OPTION_DOC | OPTION_NO_USAGE,                                   \
        COMMON_X_OUTPUT_SPECS(used in the formula), 0 }

extern const struct argp output_argp;

int parse_opt_output(int key, char* arg, struct argp_state* state);

// Low-level output
std::ostream&
stream_formula(std::ostream& out,
               spot::formula f, const char* filename, int linenum);

void output_formula_checked(spot::formula f,
                            spot::process_timer* ptimer = nullptr,
                            const char* filename = nullptr, int linenum = 0,
                            const char* prefix = nullptr,
                            const char* suffix = nullptr);


class printable_formula:
  public spot::printable_value<spot::formula>
{
public:
  printable_formula&
  operator=(spot::formula new_val)
  {
    val_ = new_val;
    return *this;
  }

  virtual void
  print(std::ostream& os, const char*) const override;
};

class aut_stat_printer: protected spot::stat_printer
{
public:
  aut_stat_printer(std::ostream& os, const char* format)
    : spot::stat_printer(os, format)
  {
    declare('f', &formula_);        // Override the formula printer.
  }

  using spot::formater::set_output;

  std::ostream&
  print(const spot::const_twa_graph_ptr& aut,
        spot::formula f = nullptr)
  {
    formula_ = f;
    return this->spot::stat_printer::print(aut, f);
  }

  printable_formula formula_;
};
