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

#include <memory>
#include <vector>

#include "common_aoutput.hh"
#include "common_finput.hh"
#include "common_setup.hh"
#include "common_sys.hh"

#include <spot/misc/game.hh>
#include <spot/misc/minato.hh>
#include <spot/tl/formula.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twa/twagraph.hh>

enum
{
  OPT_INPUT = 256,
  OPT_PRINT
};

static const argp_option options[] =
  {
    { "input", OPT_INPUT, "PROPS", 0,
      "comma-separated list of atomic propositions", 0},
    { "print-pg", OPT_PRINT, nullptr, 0,
      "print the parity game in the pgsolver format, do not solve it", 0},
    { nullptr, 0, nullptr, 0, nullptr, 0 },
  };

const struct argp_child children[] =
  {
    { &finput_argp, 0, nullptr, 1 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

const char argp_program_doc[] =
"Answer the LTL realizability problem given an LTL formula and a list of"
" uncontrollable (a.k.a. input) proposition names.";

std::vector<std::string> input_aps;

bool opt_print_pg{false};

namespace
{
  // Take an automaton and a set of atomic propositions I, and split each
  // transition
  //
  //     p -- cond --> q                cond in 2^2^AP
  //
  // into a set of transitions of the form
  //
  //     p -- i1 --> r1 -- o1 --> q     i1 in 2^I
  //                                    o1 in 2^O
  //
  //     p -- i2 --> r2 -- o2 --> q     i2 in 2^I
  //                                    o2 in 2^O
  //     ...
  //
  // where O = AP\I, and such that cond = (i1 & o1) | (i2 & o2) | ...
  //
  // When determinized, this encodes a game automaton that has a winning
  // strategy iff aut has an accepting run for all valuation of atomic
  // propositions in I.

  spot::twa_graph_ptr
  split_automaton(const spot::twa_graph_ptr& aut,
                  bdd input_bdd)
  {
    auto tgba = spot::to_generalized_buchi(aut);
    auto split = spot::make_twa_graph(tgba->get_dict());
    split->copy_ap_of(tgba);
    split->copy_acceptance_of(tgba);
    split->new_states(tgba->num_states());
    split->set_init_state(tgba->get_init_state_number());

    for (unsigned src = 0; src < tgba->num_states(); ++src)
      for (const auto& e: tgba->out(src))
        {
          spot::minato_isop isop(e.cond);
          bdd cube;
          while ((cube = isop.next()) != bddfalse)
            {
              unsigned q = split->new_state();
              bdd in = bdd_existcomp(cube, input_bdd);
              bdd out = bdd_exist(cube, input_bdd);
              split->new_edge(src, q, in, 0);
              split->new_edge(q, e.dst, out, e.acc);
            }
        }
    split->prop_universal(spot::trival::maybe());
    return split;
  }

  // Generates a vector indicating the owner of each state, with the
  // convention that false is player 0 (the environment) and true is player 1
  // (the controller).  Starting with player 0 on the initial state, the owner
  // is switched after each transition.
  std::vector<bool> make_alternating_owner(const spot::twa_graph_ptr& dpa,
                                           bool init_owner = false)
  {
    std::vector<bool> seen(dpa->num_states(), false);
    std::vector<unsigned> todo({dpa->get_init_state_number()});
    std::vector<bool> owner(dpa->num_states());
    owner[dpa->get_init_state_number()] = init_owner;
    while (!todo.empty())
      {
        unsigned src = todo.back();
        todo.pop_back();
        seen[src] = true;
        for (auto& e: dpa->out(src))
          {
            if (!seen[e.dst])
              {
                owner[e.dst] = !owner[src];
                todo.push_back(e.dst);
              }
          }
      }
    return owner;
  }

  spot::parity_game to_parity_game(const spot::twa_graph_ptr& split)
  {
    auto dpa = spot::tgba_determinize(split);
    dpa->merge_edges();
    spot::complete_here(dpa);
    spot::colorize_parity_here(dpa, true);
    spot::change_parity_here(dpa, spot::parity_kind_max,
                             spot::parity_style_odd);
    if (opt_print_pg)
      dpa = spot::sbacc(dpa);
    bool max, odd;
    dpa->acc().is_parity(max, odd);
    assert(max && odd);
    assert(spot::is_deterministic(dpa));
    auto owner = make_alternating_owner(dpa);
    return spot::parity_game(dpa, owner);
  }

  class ltl_processor final : public job_processor
  {
  public:
    spot::translator& trans;
    std::vector<std::string> input_aps;

    ltl_processor(spot::translator& trans, std::vector<std::string> input_aps)
      : trans(trans), input_aps(input_aps)
    {
    }

    int process_formula(spot::formula f,
                        const char*, int) override
    {
      auto aut = trans.run(&f);
      bdd input_bdd = bddtrue;
      for (unsigned i = 0; i < input_aps.size(); ++i)
        {
          std::ostringstream lowercase;
          for (char c: input_aps[i])
            lowercase << (char)std::tolower(c);
          auto ap = spot::formula::ap(lowercase.str());
          input_bdd &= bdd_ithvar(aut->register_ap(ap));
        }
      auto split = split_automaton(aut, input_bdd);
      auto pg = to_parity_game(split);
      if (opt_print_pg)
        {
          pg.print(std::cout);
          return 0;
        }
      if (pg.solve_qp())
        std::cout << "realizable\n";
      else
        std::cout << "unrealizable\n";
      return 0;
    }
  };
}

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  switch (key)
    {
    case OPT_INPUT:
      {
        std::istringstream aps(arg);
        std::string ap;
        while (std::getline(aps, ap, ','))
          {
            ap.erase(remove_if(ap.begin(), ap.end(), isspace), ap.end());
            input_aps.push_back(ap);
          }
        break;
      }
    case OPT_PRINT:
      opt_print_pg = true;
      break;
    }
  return 0;
}

int main(int argc, char **argv)
{
  setup(argv);
  const argp ap = { options, parse_opt, nullptr,
                    argp_program_doc, children, nullptr, nullptr };
  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
    exit(err);
  spot::translator trans;
  ltl_processor processor(trans, input_aps);
  processor.run();
}
