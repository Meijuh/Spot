// -*- coding: utf-8 -*-
// Copyright (C) 2008, 2009, 2010, 2011, 2012, 2014, 2015 Laboratoire
// de Recherche et Développement de l'Epita (LRDE).
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

#include <iomanip>
#include <iostream>
#include "twaalgos/dot.hh"
#include "twaalgos/hoa.hh"
#include "hoaparse/public.hh"
#include "twa/twaproduct.hh"
#include "twaalgos/gtec/gtec.hh"
#include "twaalgos/ltl2tgba_fm.hh"
#include "ltlparse/public.hh"
#include "twaalgos/stats.hh"
#include "twaalgos/emptiness.hh"
#include "ltlast/unop.hh"
#include "twaalgos/stats.hh"
#include "twaalgos/emptiness_stats.hh"
#include "twaalgos/degen.hh"

#include "twa/twasafracomplement.hh"

void usage(const char* prog)
{
  std::cout << "usage: " << prog << " [options]" << std::endl;
  std::cout << "with options" << std::endl
            << "-H                      Output in HOA\n"
            << "-s     buchi_automaton  display the safra automaton\n"
            << "-a     buchi_automaton  display the complemented automaton\n"
            << "-astat buchi_automaton  statistics for !a\n"
            << "-fstat formula          statistics for !A_f\n"
            << "-f     formula          test !A_f and !A_!f\n"
            << "-p     formula          print the automaton for f\n";
}

int main(int argc, char* argv[])
{
  char *file = 0;
  bool print_safra = false;
  bool print_automaton = false;
  //bool check = false;
  int return_value = 0;
  bool stats = false;
  bool formula = false;
  bool print_formula = false;
  bool save_hoa = false;

  if (argc < 3)
  {
    usage(argv[0]);
    return 1;
  }

  for (int i = 1; i < argc; ++i)
  {
    if (argv[i][0] == '-')
    {
      if (strcmp(argv[i] + 1, "H") == 0)
      {
	save_hoa = true;
	continue;
      }

      if (strcmp(argv[i] + 1, "astat") == 0)
      {
        stats = true;
        formula = false;
        continue;
      }

      if (strcmp(argv[i] + 1, "fstat") == 0)
      {
        stats = true;
        formula = true;
        continue;
      }

      switch (argv[i][1])
      {
        case 's':
          print_safra = true; break;
        case 'a':
          print_automaton = true; break;
        case 'f':
          //check = true;
	  break;
        case 'p':
          print_formula = true; break;
        default:
          std::cerr << "unrecognized option `-" << argv[i][1]
                    << '\'' << std::endl;
          return 2;
      }
    }
    else
      file = argv[i];
  }

  if (file == 0)
  {
    usage(argv[0]);
    return 1;
  }

  auto dict = spot::make_bdd_dict();
  if (print_automaton || print_safra)
  {
    spot::ltl::environment& env(spot::ltl::default_environment::instance());
    spot::hoa_parse_error_list pel;
    auto h = spot::hoa_parse(file, pel, dict, env);
    if (spot::format_hoa_parse_errors(std::cerr, file, pel))
      return 2;
    spot::twa_graph_ptr a = h->aut;

    spot::twa_ptr complement = 0;

    complement = spot::make_safra_complement(a);

    if (print_automaton)
      {
	if (save_hoa)
	  spot::print_hoa(std::cout, complement, nullptr);
	else
	  spot::print_dot(std::cout, complement);
      }

    if (print_safra)
    {
      auto safra_complement =
	std::dynamic_pointer_cast<spot::tgba_safra_complement>(complement);
      spot::display_safra(safra_complement);
    }
  }
  else if (print_formula)
  {
    spot::ltl::parse_error_list p1;
    auto* f1 = spot::ltl::parse_infix_psl(file, p1);

    if (spot::ltl::format_parse_errors(std::cerr, file, p1))
      return 2;

    auto a = spot::ltl_to_tgba_fm(f1, dict);
    spot::twa_ptr complement = 0;
    complement = spot::make_safra_complement(a);

    spot::print_dot(std::cout, complement);
    f1->destroy();
  }
  else if (stats)
  {
    spot::twa_graph_ptr a;
    const spot::ltl::formula* f1 = 0;

    if (formula)
    {
      spot::ltl::parse_error_list p1;
      f1 = spot::ltl::parse_infix_psl(file, p1);

      if (spot::ltl::format_parse_errors(std::cerr, file, p1))
        return 2;

      a = spot::ltl_to_tgba_fm(f1, dict);
    }
    else
    {
      spot::hoa_parse_error_list pel;
      spot::ltl::environment& env(spot::ltl::default_environment::instance());
      auto h = spot::hoa_parse(file, pel, dict, env);
      if (spot::format_hoa_parse_errors(std::cerr, file, pel))
        return 2;
      a = h->aut;
    }

    auto safra_complement = spot::make_safra_complement(a);

    spot::tgba_statistics a_size =  spot::stats_reachable(a);
    std::cout << "Original: "
              << a_size.states << ", "
              << a_size.transitions << ", "
              << a->acc().num_sets()
              << std::endl;

    auto buchi = spot::degeneralize(a);
    std::cout << "Buchi: "
              << buchi->num_states()
	      << buchi->num_transitions()
              << buchi->acc().num_sets()
              << std::endl;

    spot::tgba_statistics b_size =  spot::stats_reachable(safra_complement);
    std::cout << "Safra Complement: "
              << b_size.states << ", "
              << b_size.transitions << ", "
              << safra_complement->acc().num_sets()
              << std::endl;

    if (formula)
    {
      auto nf1 = spot::ltl::unop::instance(spot::ltl::unop::Not, f1->clone());
      auto a2 = spot::ltl_to_tgba_fm(nf1, dict);
      spot::tgba_statistics a_size =  spot::stats_reachable(a2);
      std::cout << "Not Formula: "
                << a_size.states << ", "
                << a_size.transitions << ", "
                << a2->acc().num_sets()
                << std::endl;

      f1->destroy();
      nf1->destroy();
    }
  }
  else
  {
    spot::ltl::parse_error_list p1;
    auto* f1 = spot::ltl::parse_infix_psl(file, p1);

    if (spot::ltl::format_parse_errors(std::cerr, file, p1))
      return 2;

    auto Af = spot::ltl_to_tgba_fm(f1, dict);
    auto nf1 = spot::ltl::unop::instance(spot::ltl::unop::Not, f1->clone());
    auto Anf = spot::ltl_to_tgba_fm(nf1, dict);
    auto nAf = spot::make_safra_complement(Af);
    auto nAnf = spot::make_safra_complement(Anf);
    auto ec = spot::couvreur99(spot::otf_product(nAf, nAnf));
    auto res = ec->check();
    spot::tgba_statistics a_size =  spot::stats_reachable(ec->automaton());
    std::cout << "States: "
              << a_size.states << std::endl
              << "Transitions: "
              << a_size.transitions << std::endl
              << "Acc Cond: "
              << ec->automaton()->acc().num_sets()
              << std::endl;
    if (res)
      {
	std::cout << "FAIL\n";
	return_value = 1;
	if (auto run = res->accepting_run())
	  {
	    spot::print_dot(std::cout, ec->automaton());
	    spot::print_tgba_run(std::cout, ec->automaton(), run);
	  }
      }
    else
      {
	std::cout << "OK\n";
      }
    nf1->destroy();
    f1->destroy();
  }

  return return_value;
}
