// Copyright (C) 2008, 2009, 2010, 2011 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2004, 2006, 2007 Laboratoire d'Informatique de Paris
// 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#include <iostream>
#include <fstream>
#include <cassert>
#include <cstdlib>
#include <string>
#include <cstring>
#include "ltlparse/public.hh"
#include "ltlvisit/dump.hh"
#include "ltlvisit/tostring.hh"
#include "ltlvisit/simplify.hh"
#include "ltlvisit/length.hh"
#include "ltlast/allnodes.hh"

void
syntax(char* prog)
{
  std::cerr << prog << " option formula1 (formula2)?" << std::endl;
  exit(2);
}

int
main(int argc, char** argv)
{
  bool readfile = false;
  bool hidereduc = false;
  unsigned long sum_before = 0;
  unsigned long sum_after = 0;
  spot::ltl::ltl_simplifier_options o(false, false, false, false, false);

  if (argc < 3)
    syntax(argv[0]);

  if (!strncmp(argv[1], "-f", 3))
    {
      readfile = true;
      ++argv;
      --argc;
    }

  if (!strncmp(argv[1], "-h", 3))
    {
      hidereduc = true;
      ++argv;
      --argc;
    }

  switch (atoi(argv[1]))
    {
    case 0:
      o.reduce_basics = true;
      break;
    case 1:
      o.synt_impl = true;
      break;
    case 2:
      o.event_univ = true;
      break;
    case 3:
      o.reduce_basics = true;
      o.synt_impl = true;
      o.event_univ = true;
      break;
    case 4:
      o.reduce_basics = true;
      o.synt_impl = true;
      break;
    case 5:
      o.reduce_basics = true;
      o.event_univ = true;
      break;
    case 6:
      o.synt_impl = true;
      o.event_univ = true;
      break;
    case 7:
      o.containment_checks = true;
      break;
    case 8:
      o.containment_checks = true;
      o.containment_checks_stronger = true;
      break;
    case 9:
      o.reduce_basics = true;
      o.synt_impl = true;
      o.event_univ = true;
      o.containment_checks = true;
      o.containment_checks_stronger = true;
      break;
    case 10:
      o.reduce_basics = true;
      o.containment_checks = true;
      o.containment_checks_stronger = true;
      break;
    case 11:
      o.synt_impl = true;
      o.containment_checks = true;
      o.containment_checks_stronger = true;
      break;
    case 12:
      o.reduce_basics = true;
      o.synt_impl = true;
      o.containment_checks = true;
      o.containment_checks_stronger = true;
      break;
    case 13:
      o.event_univ = true;
      o.containment_checks = true;
      o.containment_checks_stronger = true;
      break;
    case 14:
      o.reduce_basics = true;
      o.event_univ = true;
      o.containment_checks = true;
      o.containment_checks_stronger = true;
      break;
    default:
      return 2;
  }

  spot::ltl::ltl_simplifier* simp = new spot::ltl::ltl_simplifier(o);

  spot::ltl::formula* f1 = 0;
  spot::ltl::formula* f2 = 0;

  std::ifstream* fin = 0;

  if (readfile)
    {
      fin = new std::ifstream(argv[2]);
      if (!*fin)
	{
	  std::cerr << "Cannot open " << argv[2] << std::endl;
	  exit(2);
	}
    }

  int exit_code = 0;

 next_line:

  if (fin)
    {
      std::string input;
      do
	{
	  if (!std::getline(*fin, input))
	    goto end;
	}
      while (input == "");

      spot::ltl::parse_error_list p1;
      f1 = spot::ltl::parse(input, p1);
      if (spot::ltl::format_parse_errors(std::cerr, input, p1))
	return 2;
    }
  else
    {
      spot::ltl::parse_error_list p1;
      f1 = spot::ltl::parse(argv[2], p1);
      if (spot::ltl::format_parse_errors(std::cerr, argv[2], p1))
	return 2;
    }

  if (argc == 4)
    {
      if (readfile)
	{
	  std::cerr << "Cannot read from file and check result." << std::endl;
	  exit(2);
	}

      spot::ltl::parse_error_list p2;
      f2 = spot::ltl::parse(argv[3], p2);
      if (spot::ltl::format_parse_errors(std::cerr, argv[3], p2))
	return 2;
    }

  {
    spot::ltl::formula* ftmp1;

    ftmp1 = f1;
    f1 = simp->negative_normal_form(f1, false);
    ftmp1->destroy();

    int length_f1_before = spot::ltl::length(f1);
    std::string f1s_before = spot::ltl::to_string(f1);

    ftmp1 = f1;
    f1 = simp->simplify(f1);

    if (!simp->are_equivalent(ftmp1, f1))
      {
	std::cerr << "Incorrect reduction from `" << f1s_before
		  << "' to `" << spot::ltl::to_string(f1) << "'."
		  << std::endl;
	exit_code = 3;
      }

    ftmp1->destroy();

    int length_f1_after = spot::ltl::length(f1);
    std::string f1s_after = spot::ltl::to_string(f1);

    std::string f2s = "";
    if (f2)
      {
	ftmp1 = f2;
	f2 = simp->negative_normal_form(f2, false);
	ftmp1->destroy();
	f2s = spot::ltl::to_string(f2);
      }

    sum_before += length_f1_before;
    sum_after += length_f1_after;

    // If -h is set, we want to print only formulae that have become larger.
    if (!f2 && (!hidereduc || (length_f1_after > length_f1_before)))
      {
	std::cout << length_f1_before << " " << length_f1_after
		  << " '" << f1s_before << "' reduce to '" << f1s_after << "'"
		  << std::endl;
      }

    if (f2)
      {
	if (f1 != f2)
	  {
	    if (length_f1_after < length_f1_before)
	      std::cout << f1s_before << " ** " << f2s << " ** " << f1s_after
			<< " KOREDUC " << std::endl;
	    else
	      std::cout << f1s_before << " ** " << f2s << " ** " << f1s_after
			<< " KOIDEM " << std::endl;
	    exit_code = 1;
	  }
	else
	  {
	    if (f1s_before != f1s_after)
	      std::cout << f1s_before << " ** " << f2s << " ** " << f1s_after
			<< " OKREDUC " << std::endl;
	    else
	      std::cout << f1s_before << " ** " << f2s << " ** " << f1s_after
			<< " OKIDEM" << std::endl;
	    exit_code = 0;
	  }
      }
    else
      {
	if (length_f1_after > length_f1_before)
	  exit_code = 1;
      }

    f1->destroy();
    if (f2)
      f2->destroy();

    if (fin)
      goto next_line;
  }
 end:

  delete simp;

  if (fin)
    {
      float before = sum_before;
      float after = sum_after;
      std::cout << "gain: "
		<< (1 - (after / before)) * 100 << "%" << std::endl;
      delete fin;
    }

  spot::ltl::atomic_prop::dump_instances(std::cerr);
  spot::ltl::unop::dump_instances(std::cerr);
  spot::ltl::binop::dump_instances(std::cerr);
  spot::ltl::multop::dump_instances(std::cerr);
  spot::ltl::automatop::dump_instances(std::cerr);
  assert(spot::ltl::atomic_prop::instance_count() == 0);
  assert(spot::ltl::unop::instance_count() == 0);
  assert(spot::ltl::binop::instance_count() == 0);
  assert(spot::ltl::multop::instance_count() == 0);
  assert(spot::ltl::automatop::instance_count() == 0);

  return exit_code;
}
