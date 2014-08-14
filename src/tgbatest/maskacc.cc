// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement
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
#include <cassert>
#include <cstdlib>
#include "tgbaparse/public.hh"
#include "tgbaalgos/save.hh"
#include "tgba/tgbamask.hh"
#include "ltlast/allnodes.hh"

void
syntax(char* prog)
{
  std::cerr << prog << " file" << std::endl;
  exit(2);
}

int
main(int argc, char** argv)
{
  int exit_code = 0;

  if (argc != 2)
    syntax(argv[0]);

  {
    auto dict = spot::make_bdd_dict();

    spot::ltl::environment& env(spot::ltl::default_environment::instance());
    spot::tgba_parse_error_list pel;
    auto aut = spot::tgba_parse(argv[1], pel, dict, env);
    if (spot::format_tgba_parse_errors(std::cerr, argv[1], pel))
      return 2;

    bdd allneg = aut->neg_acceptance_conditions();

    for (bdd cur = allneg; cur != bddtrue; cur = bdd_low(cur))
      {
	int i = bdd_var(cur);
	bdd one = bdd_compose(allneg, bdd_nithvar(i), i);
	auto masked = spot::build_tgba_mask_acc_ignore(aut, one);
	spot::tgba_save_reachable(std::cout, masked);
      }
  }

  assert(spot::ltl::unop::instance_count() == 0);
  assert(spot::ltl::binop::instance_count() == 0);
  assert(spot::ltl::multop::instance_count() == 0);
  assert(spot::ltl::atomic_prop::instance_count() != 0);
  assert(spot::ltl::atomic_prop::instance_count() == 0);
  return exit_code;
}
