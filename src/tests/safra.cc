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

#include "twaalgos/safra.hh"
#include "hoaparse/public.hh"
#include "twaalgos/dotty.hh"


int main(int argc, char* argv[])
{
  if (argc <= 1)
    return 1;
  char* input = argv[1];
  spot::hoa_parse_error_list pel;
  auto dict = spot::make_bdd_dict();
  auto aut = spot::hoa_parse(input, pel, dict);
  if (spot::format_hoa_parse_errors(std::cerr, input, pel))
    return 2;
  auto res = tgba_determinisation(aut->aut);

  spot::dotty_reachable(std::cout, res);
}
