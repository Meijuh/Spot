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
#include <iomanip>
#include <fstream>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include "ltlparse/public.hh"
#include "ltlast/allnodes.hh"
#include "tgbaalgos/ltl2tgba_fm.hh"
#include "tgbaalgos/sccfilter.hh"
#include "tgbaalgos/degen.hh"
#include "tgbaalgos/stats.hh"
#include "taalgos/minimize.hh"
#include "taalgos/tgba2ta.hh"
#include "taalgos/dotty.hh"
#include "taalgos/stats.hh"

void
syntax(char* prog)
{
  std::cerr << prog << " file" << std::endl;
  exit(2);
}

void stats(std::string title, const spot::ta_ptr& ta)
{
  auto s = stats_reachable(ta);

  std::cout << std::left << std::setw(20) << title << " | "
	    << std::right << std::setw(6) << s.states << " | "
	    << std::setw(6) << s.transitions << " | "
	    << std::setw(6) << s.acceptance_states << '\n';
}

void stats(std::string title, const spot::tgba_ptr& tg)
{
  auto s = stats_reachable(tg);

  std::cout << std::left << std::setw(20) << title << " | "
	    << std::right << std::setw(6) << s.states << " | "
	    << std::setw(6) << s.transitions << " | "
	    << std::setw(6) << "XXX" << '\n';
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
  while (std::getline(input, s))
    {
      std::cout << "in: " << s << '\n';
      if (s.empty() || s[0] == '#') // Skip comments
	continue;

      spot::ltl::parse_error_list pe;
      auto f = spot::ltl::parse(s, pe);

      if (spot::ltl::format_parse_errors(std::cerr, s, pe))
	return 2;


      {
	auto a = ltl_to_tgba_fm(f, d);
	bdd ap_set = atomic_prop_collect_as_bdd(f, a);

	// run 0 ../ltl2tgba -TGTA -ks "$1"
	// run 0 ../ltl2tgba -TGTA -RT -ks "$1"
	{
	  auto t = spot::tgba_to_tgta(a, ap_set);
	  stats("-TGTA", t);
	  stats("-TGTA -RT", minimize_tgta(t));
	}

	{
	  // run 0 ../ltl2tgba -TA -ks "$1"
	  // run 0 ../ltl2tgba -TA -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    false, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    false, // single_pass (-sp),
				    false); // artificial_livelock (-lv)
	  stats("-TA", t);
	  stats("-TA -RT", minimize_ta(t));
	}

	{
	  // run 0 ../ltl2tgba -TA -lv -ks "$1"
	  // run 0 ../ltl2tgba -TA -lv -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    false, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    false, // single_pass (-sp),
				    true); // artificial_livelock (-lv)
	  stats("-TA -lv", t);
	  stats("-TA -lv -RT", minimize_ta(t));
	}

	{
	  // run 0 ../ltl2tgba -TA -sp -ks "$1"
	  // run 0 ../ltl2tgba -TA -sp -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    false, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    true, // single_pass (-sp),
				    false); // artificial_livelock (-lv)
	  stats("-TA -sp", t);
	  stats("-TA -sp -RT", minimize_ta(t));
	}

	{
	  // run 0 ../ltl2tgba -TA -lv -sp -ks "$1"
	  // run 0 ../ltl2tgba -TA -lv -sp -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    false, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    true, // single_pass (-sp),
				    true); // artificial_livelock (-lv)
	  stats("-TA -lv -sp", t);
	  stats("-TA -lv -sp -RT", minimize_ta(t));
	}

	a = spot::degeneralize(a);

	{
	  // run 0 ../ltl2tgba -TA -DS -ks "$1"
	  // run 0 ../ltl2tgba -TA -DS -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    true, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    false, // single_pass (-sp),
				    false); // artificial_livelock (-lv)
	  stats("-TA -DS", t);
	  stats("-TA -DS -RT", minimize_ta(t));
	}

	{
	  // run 0 ../ltl2tgba -TA -DS -lv -ks "$1"
	  // run 0 ../ltl2tgba -TA -DS -lv -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    true, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    false, // single_pass (-sp),
				    true); // artificial_livelock (-lv)
	  stats("-TA -DS -lv", t);
	  stats("-TA -DS -lv -RT", minimize_ta(t));
	}

	{
	  // run 0 ../ltl2tgba -TA -DS -sp -ks "$1"
	  // run 0 ../ltl2tgba -TA -DS -sp -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    true, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    true, // single_pass (-sp),
				    false); // artificial_livelock (-lv)
	  stats("-TA -DS -sp", t);
	  stats("-TA -DS -sp -RT", minimize_ta(t));
	}

	{
	  // run 0 ../ltl2tgba -TA -DS -lv -sp -ks "$1"
	  // run 0 ../ltl2tgba -TA -DS -lv -sp -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    true, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    true, // single_pass (-sp),
				    true); // artificial_livelock (-lv)
	  stats("-TA -DS -lv -sp", t);
	  stats("-TA -DS -lv -sp -RT", minimize_ta(t));
	}
      }
      // Some cases with -x -R3 -DS -in
      {
	auto a = spot::degeneralize(scc_filter(ltl_to_tgba_fm(f, d, true)));
	bdd ap_set = atomic_prop_collect_as_bdd(f, a);

	{
	  // run 0 ../ltl2tgba -x -R3 -DS -TA -in -ks "$1"
	  // run 0 ../ltl2tgba -x -R3 -DS -TA -in -RT -ks "$1"
	  auto t = spot::tgba_to_ta(a, ap_set,
				    true, // degen (-DS)
				    false, // artificial_initial_state (-in)
				    false, // single_pass (-sp),
				    true); // artificial_livelock (-lv)
	  stats("-x -TA -DS -in", t);
	  stats("-x -TA -DS -in -RT", minimize_ta(t));
	}

      }

      f->destroy();
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
