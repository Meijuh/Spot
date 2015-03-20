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

#pragma once

#include "common_sys.hh"
#include <vector>
#include <argp.h>

#include "misc/formater.hh"
#include "misc/tmpfile.hh"
#include "tgba/tgbagraph.hh"


extern const struct argp trans_argp;

struct translator_spec
{
  // The translator command, as specified on the command-line.
  // If this has the form of
  //    {name}cmd
  // then it is split in two components.
  // Otherwise, spec=cmd=name.
  const char* spec;
  // actual shell command (or spec)
  const char* cmd;
  // name of the translator (or spec)
  const char* name;

  translator_spec(const char* spec);
  translator_spec(const translator_spec& other);
  ~translator_spec();
};

extern std::vector<translator_spec> translators;

struct quoted_string final: public spot::printable_value<std::string>
{
  using spot::printable_value<std::string>::operator=;
  void print(std::ostream& os, const char* pos) const override;
};

struct printable_result_filename final:
  public spot::printable_value<spot::temporary_file*>
{
  unsigned translator_num;
  enum output_format { None, Dstar, Hoa };
  mutable output_format format;

  printable_result_filename();
  ~printable_result_filename();
  void reset(unsigned n);
  void cleanup();

  void print(std::ostream& os, const char* pos) const override;
};


class translator_runner: protected spot::formater
{
protected:
  spot::bdd_dict_ptr dict;
  // Round-specific variables
  quoted_string string_ltl_spot;
  quoted_string string_ltl_spin;
  quoted_string string_ltl_lbt;
  quoted_string string_ltl_wring;
  quoted_string filename_ltl_spot;
  quoted_string filename_ltl_spin;
  quoted_string filename_ltl_lbt;
  quoted_string filename_ltl_wring;
  // Run-specific variables
  printable_result_filename output;
public:
  using spot::formater::has;

  translator_runner(spot::bdd_dict_ptr dict,
		    // whether we accept the absence of output
		    // specifier
		    bool no_output_allowed = false);
  void string_to_tmp(std::string& str, unsigned n, std::string& tmpname);
  const std::string& formula() const;
  void round_formula(const spot::ltl::formula* f, unsigned serial);
};


// Disable handling of timeout on systems that miss kill() or alarm().
// For instance MinGW.
#if HAVE_KILL && HAVE_ALARM
# define ENABLE_TIMEOUT 1
#else
# define ENABLE_TIMEOUT 0
#endif

extern volatile bool timed_out;
extern unsigned timeout_count;
#if ENABLE_TIMEOUT
void setup_sig_handler();
int exec_with_timeout(const char* cmd);
#else // !ENABLE_TIMEOUT
#define exec_with_timeout(cmd) system(cmd)
#define setup_sig_handler() while (0);
#endif // !ENABLE_TIMEOUT
