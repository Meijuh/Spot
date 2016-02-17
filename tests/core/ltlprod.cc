// -*- coding: utf-8 -*-
// Copyright (C) 2008, 2009, 2012, 2014, 2015, 2016 Laboratoire de
// Recherche et Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004 Laboratoire d'Informatique de
// Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
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
#include <spot/tl/parse.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/dot.hh>

static void
syntax(char* prog)
{
  std::cerr << prog << " formula1 formula2" << std::endl;
  exit(2);
}

int
main(int argc, char** argv)
{
  int exit_code = 0;

  if (argc != 3)
    syntax(argv[0]);

  {
    spot::environment& env(spot::default_environment::instance());

    auto pf1 = spot::parse_infix_psl(argv[1], env);
    if (pf1.format_errors(std::cerr))
      return 2;
    auto f1 = pf1.f;

    auto pf2 = spot::parse_infix_psl(argv[2], env);
    if (pf2.format_errors(std::cerr))
      return 2;
    auto f2 = pf2.f;

    auto dict = spot::make_bdd_dict();
    {
      auto a1 = spot::ltl_to_tgba_fm(f1, dict);
      auto a2 = spot::ltl_to_tgba_fm(f2, dict);
      spot::print_dot(std::cout, product(a1, a2));
    }
  }
  assert(spot::fnode::instances_check());
  return exit_code;
}
