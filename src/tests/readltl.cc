// -*- coding: utf-8 -*-
// Copyright (C) 2008, 2009, 2012, 2015 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2003 Laboratoire d'Informatique de Paris 6
// (LIP6), département Systèmes Répartis Coopératifs (SRC), Université
// Pierre et Marie Curie.
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
#include <cstring>
#include "ltlparse/public.hh"
#include "tl/dot.hh"

void
syntax(char* prog)
{
  std::cerr << prog << " [-d] formula" << std::endl;
  exit(2);
}

int
main(int argc, char** argv)
{
  int exit_code = 0;

  if (argc < 2)
    syntax(argv[0]);

  bool debug = false;
  int formula_index = 1;

  if (!strcmp(argv[1], "-d"))
    {
      debug = true;
      if (argc < 3)
	syntax(argv[0]);
      formula_index = 2;
    }

  {
    spot::ltl::environment& env(spot::ltl::default_environment::instance());
    spot::ltl::parse_error_list pel;
    auto f = spot::ltl::parse_infix_psl(argv[formula_index], pel, env, debug);

    exit_code =
      spot::ltl::format_parse_errors(std::cerr, argv[formula_index], pel);


    if (f)
      {
#ifdef DOTTY
	spot::ltl::print_dot_psl(std::cout, f);
#else
	f.dump(std::cout) << std::endl;
#endif
      }
    else
      {
	exit_code = 1;
      }

  }
  assert(spot::ltl::fnode::instances_check());
  return exit_code;
}
