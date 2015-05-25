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


int main(int argc, char* argv[])
{
  if (argc <= 2)
    return 1;
  char* input = argv[2];
  auto dict = spot::make_bdd_dict();
  spot::twa_graph_ptr res;
  if (!strncmp(argv[1], "-f", 2))
    {
      spot::ltl::parse_error_list pel;
      const spot::ltl::formula* f =
      spot::ltl::parse(input, pel, spot::ltl::default_environment::instance(),
                       false);
      spot::translator trans(dict);
      trans.set_pref(spot::postprocessor::Deterministic);
      auto tmp = trans.run(f);
      res = spot::tgba_determinisation(tmp);
      f->destroy();
    }
  else if (!strncmp(argv[1], "--hoa", 5))
    {
      spot::hoa_parse_error_list pel;
      auto aut = spot::hoa_parse(input, pel, dict);
      if (spot::format_hoa_parse_errors(std::cerr, input, pel))
        return 2;
      res = tgba_determinisation(aut->aut);
    }

  spot::dotty_reachable(std::cout, res);
}
