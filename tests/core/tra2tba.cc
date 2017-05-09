// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement
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
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/tra2tba.hh>
#include <spot/twaalgos/hoa.hh>

int main(int, char* argv[])
{
  char* input = argv[1];
  if (!input)
    return 1;
  auto pa = parse_aut(input, spot::make_bdd_dict());
  if (pa->format_errors(std::cerr))
    return 1;
  if (pa->aborted)
    {
      std::cerr << "--ABORT-- read\n";
      return 1;
    }
  auto tba = spot::tra_to_tba(pa->aut);
  spot::print_hoa(std::cout, tba) << '\n';
  return 0;
}
