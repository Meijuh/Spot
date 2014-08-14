// Copyright (C) 2011, 2014 Laboratoire de Recherche et Developpement
// de l'Epita (LRDE)
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


#include "kripkeparse/public.hh"
#include "kripke/kripkeprint.hh"
#include "ltlast/allnodes.hh"


using namespace spot;

int main(int argc, char** argv)
{
  int return_value = 0;
  kripke_parse_error_list pel;

  {
    auto k = kripke_parse(argv[1], pel, make_bdd_dict());
    if (!pel.empty())
      {
	format_kripke_parse_errors(std::cerr, argv[1], pel);
	return_value = 1;
      }

    if (!return_value)
      kripke_save_reachable(std::cout, k);
  }

  assert(ltl::atomic_prop::instance_count() == 0);
  assert(ltl::unop::instance_count() == 0);
  assert(ltl::binop::instance_count() == 0);
  assert(ltl::multop::instance_count() == 0);
  return return_value;
}
