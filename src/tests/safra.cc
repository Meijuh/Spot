// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include <iostream>
#include <cstring>

#include "twa/twagraph.hh"
#include "twaalgos/safra.hh"
#include "twaalgos/translate.hh"
#include "hoaparse/public.hh"
#include "ltlparse/public.hh"
#include "twaalgos/dotty.hh"
#include "twaalgos/hoa.hh"
#include "twaalgos/degen.hh"


int help()
{
  std::cerr << "safra [OPTIONS]\n";
  std::cerr << "\t-f ltl_formula\tinput string is an ltl formulae\n";
  std::cerr << "\t--hoa file.hoa\tinput file has hoa format\n";
  std::cerr << "\t-p\tpretty print states\n";
  std::cerr << "\t-H\toutput hoa format\n";
  return 1;
}

int main(int argc, char* argv[])
{
  bool sim = false;
  bool in_hoa = false;
  bool in_ltl = false;
  bool out_dot = true;
  bool out_hoa = false;
  bool pretty_print = false;

  char* input = nullptr;
  if (argc <= 2)
    return help();
  for (int i = 1; i < argc; ++i)
    {
      if (!strncmp(argv[i], "--hoa", 5))
        {
          in_hoa = true;
          if (i + 1 >= argc)
            return help();
          input = argv[++i];
        }
      else if (!strncmp(argv[i], "-f", 2))
        {
          in_ltl = true;
          if (i + 1 >= argc)
            return help();
          input = argv[++i];
        }
      else if (!strncmp(argv[i], "-H", 2))
        {
          out_dot = false;
          out_hoa = true;
        }
      else if (!strncmp(argv[i], "-p", 2))
        pretty_print = true;
      else if (!strncmp(argv[i], "-b", 2))
        sim = true;
    }

  if (!input)
    help();

  auto dict = spot::make_bdd_dict();
  spot::twa_graph_ptr res;
  if (in_ltl)
    {
      spot::ltl::parse_error_list pel;
      const spot::ltl::formula* f =
      spot::ltl::parse(input, pel, spot::ltl::default_environment::instance(),
                       false);
      if (spot::ltl::format_parse_errors(std::cerr, input, pel))
        return 2;
      spot::translator trans(dict);
      trans.set_pref(spot::postprocessor::Deterministic);
      auto tmp = trans.run(f);
      res = spot::tgba_determinisation(tmp, sim, pretty_print);
      f->destroy();
    }
  else if (in_hoa)
    {
      spot::hoa_parse_error_list pel;
      auto aut = spot::hoa_parse(input, pel, dict);
      if (spot::format_hoa_parse_errors(std::cerr, input, pel))
        return 2;
      res = tgba_determinisation(aut->aut, sim, pretty_print);
    }
  res->merge_transitions();

  if (out_hoa)
    {
      spot::hoa_reachable(std::cout, res, "t");
      std::cout << std::endl;
    }
  else if (out_dot)
    spot::dotty_reachable(std::cout, res);
  else
    assert(false);
}
