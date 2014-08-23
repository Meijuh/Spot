// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement de
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

#include <iostream>
#include <fstream>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include "ltlparse/public.hh"
#include "ltlast/allnodes.hh"
#include "tgba/futurecondcol.hh"
#include "tgbaalgos/ltl2tgba_fm.hh"
#include "tgbaalgos/ltl2taa.hh"
#include "tgbaalgos/sccfilter.hh"
#include "tgba/tgbaproduct.hh"
#include "tgbaalgos/dotty.hh"
#include "tgbaalgos/dupexp.hh"

void
syntax(char* prog)
{
  std::cerr << prog << " file" << std::endl;
  exit(2);
}

int
main(int argc, char** argv)
{
  if (argc != 2)
    syntax(argv[0]);
  std::ifstream input(argv[1]);
  if (!input)
    {
      std::cerr << "failed to open " << argv[1] << '\n';
      return 2;
    }


  auto d = spot::make_bdd_dict();

  std::string s;
  unsigned line = 0;
  while (std::getline(input, s))
    {
      ++line;
      std::cerr << line << ": " << s << '\n';
      if (s.empty() || s[0] == '#') // Skip comments
	continue;

      spot::ltl::parse_error_list pe;
      auto fpos = spot::ltl::parse(s, pe);

      if (spot::ltl::format_parse_errors(std::cerr, s, pe))
	return 2;

      auto fneg =
	spot::ltl::unop::instance(spot::ltl::unop::Not, fpos->clone());

      {
	auto apos = scc_filter(ltl_to_tgba_fm(fpos, d));
	auto aneg = scc_filter(ltl_to_tgba_fm(fneg, d));
	if (!spot::product(apos, aneg)->is_empty())
	  {
	    std::cerr << "non-empty intersection between pos and neg (FM)\n";
	    exit(2);
	  }

	// Run make_future_conditions_collector, without testing the output.
	auto fc = spot::make_future_conditions_collector(apos, true);
	spot::dotty_reachable(std::cout, fc);
      }

      {
	auto apos = scc_filter(ltl_to_tgba_fm(fpos, d, true));
	auto aneg = scc_filter(ltl_to_tgba_fm(fneg, d, true));
	if (!spot::product(apos, aneg)->is_empty())
	  {
	    std::cerr << "non-empty intersection between pos and neg (FM -x)\n";
	    exit(2);
	  }
      }

      if (fpos->is_ltl_formula())
	{
	  auto apos = scc_filter(spot::tgba_dupexp_dfs(ltl_to_taa(fpos, d)));
	  auto aneg = scc_filter(spot::tgba_dupexp_dfs(ltl_to_taa(fneg, d)));
	  if (!spot::product(apos, aneg)->is_empty())
	    {
	      std::cerr << "non-empty intersection between pos and neg (TAA)\n";
	      exit(2);
	    }
	}
      fpos->destroy();
      fneg->destroy();
    }

  spot::ltl::atomic_prop::dump_instances(std::cerr);
  spot::ltl::unop::dump_instances(std::cerr);
  spot::ltl::binop::dump_instances(std::cerr);
  spot::ltl::multop::dump_instances(std::cerr);
  assert(spot::ltl::atomic_prop::instance_count() == 0);
  assert(spot::ltl::unop::instance_count() == 0);
  assert(spot::ltl::binop::instance_count() == 0);
  assert(spot::ltl::multop::instance_count() == 0);
  return 0;
}
