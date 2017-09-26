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

#include <config.h>

#include <cmath>
#include <map>
#include <memory>
#include <string>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "common_aoutput.hh"
#include "common_finput.hh"
#include "common_setup.hh"
#include "common_sys.hh"

#include <spot/misc/bddlt.hh>
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
  OPT_ALGO = 256,
  OPT_INPUT,
  OPT_OUTPUT,
  OPT_PRINT,
  OPT_REAL
};

enum solver
{
  QP,
  REC
};

static const argp_option options[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Input options:", 1 },
    { "input", OPT_INPUT, "PROPS", 0,
      "comma-separated list of uncontrollable (a.k.a. input) atomic"
      " propositions", 0},
    { "output", OPT_OUTPUT, "PROPS", 0,
      "comma-separated list of controllable (a.k.a. output) atomic"
      " propositions", 0},
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Fine tuning:", 10 },
    { "algo", OPT_ALGO, "ALGO", 0,
      "choose the parity game algorithm, valid ones are rec (Zielonka's"
      " recursive algorithm, default) and qp (Calude et al.'s quasi-polynomial"
      " time algorithm)", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", 20 },
    { "print-pg", OPT_PRINT, nullptr, 0,
      "print the parity game in the pgsolver format, do not solve it", 0},
    { "realizability", OPT_REAL, nullptr, 0,
      "realizability only, do not synthesize the circuit", 0},
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 },
  };

const struct argp_child children[] =
  {
    { &finput_argp_headless, 0, nullptr, 0 },
    { &misc_argp, 0, nullptr, 0 },
    { nullptr, 0, nullptr, 0 }
  };

const char argp_program_doc[] =
"Synthesize an AIGER circuit from its LTL specifications.";

std::vector<std::string> input_aps;
std::vector<std::string> output_aps;
std::unordered_map<unsigned, unsigned> bddvar_to_inputnum;
std::unordered_map<unsigned, unsigned> bddvar_to_outputnum;

bool opt_print_pg(false);
bool opt_real(false);
solver opt_solver(REC);

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
  // strategy iff aut has an accepting run for any valuation of atomic
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

  spot::twa_graph_ptr to_dpa(const spot::twa_graph_ptr& split)
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
    return dpa;
  }

  // Parity game strategy to AIGER

  class aig
  {
  private:
    unsigned num_inputs_;
    unsigned max_var_;
    std::map<unsigned, std::pair<unsigned, unsigned>> and_gates_;
    std::vector<unsigned> latches_;
    std::vector<unsigned> outputs_;
    // Cache the function computed by each variable as a bdd.
    std::unordered_map<unsigned, bdd> var2bdd_;
    std::unordered_map<bdd, unsigned, spot::bdd_hash> bdd2var_;

  public:
    aig(unsigned num_inputs, unsigned num_latches, unsigned num_outputs)
      : num_inputs_(num_inputs),
        max_var_((num_inputs + num_latches) * 2),
        latches_(std::vector<unsigned>(num_latches)),
        outputs_(std::vector<unsigned>(num_outputs))
    {
      bdd2var_[bddtrue] = 1;
      var2bdd_[1] = bddtrue;
      bdd2var_[bddfalse] = 0;
      var2bdd_[0] = bddfalse;
    }

    unsigned input_var(unsigned i, bdd b)
    {
      assert(i < num_inputs_);
      unsigned v = (1 + i) * 2;
      bdd2var_[b] = v;
      var2bdd_[v] = b;
      return v;
    }

    unsigned latch_var(unsigned i, bdd b)
    {
      assert(i < latches_.size());
      unsigned v = (1 + num_inputs_ + i) * 2;
      bdd2var_[b] = v;
      var2bdd_[v] = b;
      return v;
    }

    void set_output(unsigned i, unsigned v)
    {
      outputs_[i] = v;
    }

    void set_latch(unsigned i, unsigned v)
    {
      latches_[i] = v;
    }

    unsigned aig_true() const
    {
      return 1;
    }

    unsigned aig_false() const
    {
      return 0;
    }

    unsigned aig_not(unsigned v)
    {
      unsigned not_v = v + 1 - 2 * (v % 2);
      assert(var2bdd_.count(v));
      var2bdd_[not_v] = !(var2bdd_[v]);
      bdd2var_[var2bdd_[not_v]] = not_v;
      return not_v;
    }

    unsigned aig_and(unsigned v1, unsigned v2)
    {
      assert(var2bdd_.count(v1));
      assert(var2bdd_.count(v2));
      bdd b = var2bdd_[v1] & var2bdd_[v2];
      auto it = bdd2var_.find(b);
      if (it != bdd2var_.end())
        return it->second;
      max_var_ += 2;
      and_gates_[max_var_] = {v1, v2};
      bdd v1v2 = var2bdd_[v1] & var2bdd_[v2];
      bdd2var_[v1v2] = max_var_;
      var2bdd_[max_var_] = v1v2;
      return max_var_;
    }

    unsigned aig_and(std::vector<unsigned> vs)
    {
      if (vs.empty())
        return aig_true();
      if (vs.size() == 1)
        return vs[0];
      if (vs.size() == 2)
        return aig_and(vs[0], vs[1]);
      unsigned m = vs.size() / 2;
      std::vector<unsigned> left(vs.begin(), vs.begin() + m);
      std::vector<unsigned> right(vs.begin() + m, vs.end());
      return aig_and(aig_and(left), aig_and(right));
    }

    unsigned aig_or(unsigned v1, unsigned v2)
    {
      return aig_not(aig_and(aig_not(v1), aig_not(v2)));
    }

    unsigned aig_or(std::vector<unsigned> vs)
    {
      for (unsigned i = 0; i < vs.size(); ++i)
        vs[i] = aig_not(vs[i]);
      return aig_not(aig_and(vs));
    }

    unsigned aig_pos(unsigned v)
    {
      return v - v % 2;
    }

    void remove_unused()
    {
      std::unordered_set<unsigned> todo;
      for (unsigned v : outputs_)
        todo.insert(aig_pos(v));
      std::unordered_set<unsigned> used;
      while (!todo.empty())
        {
          used.insert(todo.begin(), todo.end());
          std::unordered_set<unsigned> todo_next;
          for (unsigned v : todo)
            {
              auto it_and = and_gates_.find(v);
              if (it_and != and_gates_.end())
                {
                  if (!used.count(aig_pos(it_and->second.first)))
                    todo_next.insert(aig_pos(it_and->second.first));
                  if (!used.count(aig_pos(it_and->second.second)))
                    todo_next.insert(aig_pos(it_and->second.second));
                }
              else if (v <= (num_inputs_ + latches_.size()) * 2
                       && v > num_inputs_ * 2)
                {
                  unsigned l = v / 2 - num_inputs_ - 1;
                  if (!used.count(aig_pos(latches_[l])))
                    todo_next.insert(aig_pos(latches_[l]));
                }
            }
          todo = todo_next;
        }
      std::unordered_set<unsigned> unused;
      for (auto& p : and_gates_)
        if (!used.count(p.first))
          unused.insert(p.first);
      for (unsigned v : unused)
        and_gates_.erase(v);
    }

    void print()
    {
      std::cout << "aag " << max_var_ / 2
                << ' ' << num_inputs_
                << ' ' << latches_.size()
                << ' ' << outputs_.size()
                << ' ' << and_gates_.size() << '\n';
      for (unsigned i = 0; i < num_inputs_; ++i)
        std::cout << (1 + i) * 2 << '\n';
      for (unsigned i = 0; i < latches_.size(); ++i)
        std::cout << (1 + num_inputs_ + i) * 2
                  << ' ' << latches_[i] << '\n';
      for (unsigned i = 0; i < outputs_.size(); ++i)
        std::cout << outputs_[i] << '\n';
      for (auto& p : and_gates_)
        std::cout << p.first
                  << ' ' << p.second.first
                  << ' ' << p.second.second << '\n';
      for (unsigned i = 0; i < num_inputs_; ++i)
        std::cout << 'i' << i << ' ' << input_aps[i] << '\n';
      for (unsigned i = 0; i < outputs_.size(); ++i)
        std::cout << 'o' << i << ' ' << output_aps[i] << '\n';
    }
  };

  std::vector<bool> output_to_vec(bdd b)
  {
    std::vector<bool> v(bddvar_to_outputnum.size());
    while (b != bddtrue && b != bddfalse)
      {
         unsigned i = bddvar_to_outputnum[bdd_var(b)];
         v[i] = (bdd_low(b) == bddfalse);
         if (v[i])
           b = bdd_high(b);
         else
           b = bdd_low(b);
      }
    return v;
  }

  bdd state_to_bdd(unsigned s, bdd all)
  {
    bdd b = bddtrue;
    unsigned size = bdd_nodecount(all);
    if (size)
      {
        unsigned st0 = bdd_var(all);
        for (unsigned i = 0; i < size; ++i)
          {
            b &= s % 2 ? bdd_ithvar(st0 + i) : bdd_nithvar(st0 + i);
            s >>= 1;
          }
      }
    return b;
  }

  // Construct a smaller automaton, filtering out states that are not
  // accessible.  Also merge back pairs of p --(i)--> q --(o)--> r
  // transitions to p --(i&o)--> r.
  spot::twa_graph_ptr
  strat_to_aut(const spot::parity_game& pg,
               const spot::parity_game::strategy_t& strat,
               const spot::twa_graph_ptr& dpa,
               bdd all_outputs)
  {
    auto aut = spot::make_twa_graph(dpa->get_dict());
    aut->copy_ap_of(dpa);
    std::vector<unsigned> todo{pg.get_init_state_number()};
    std::vector<int> pg2aut(pg.num_states(), -1);
    aut->set_init_state(aut->new_state());
    pg2aut[pg.get_init_state_number()] = aut->get_init_state_number();
    while (!todo.empty())
      {
        unsigned s = todo.back();
        todo.pop_back();
        for (auto& e1: dpa->out(s))
          {
            unsigned i = 0;
            for (auto& e2: dpa->out(e1.dst))
              {
                bool self_loop = false;
                if (e1.dst == s || e2.dst == e1.dst)
                  self_loop = true;
                if (self_loop || strat.at(e1.dst) == i)
                  {
                    bdd out = bdd_satoneset(e2.cond, all_outputs, bddfalse);
                    if (pg2aut[e2.dst] == -1)
                      {
                        pg2aut[e2.dst] = aut->new_state();
                        todo.push_back(e2.dst);
                      }
                    aut->new_edge(pg2aut[s], pg2aut[e2.dst],
                                  (e1.cond & out), 0);
                    break;
                  }
                ++i;
              }
          }
      }
    aut->purge_dead_states();
    return aut;
  }

  std::vector<bool> state_to_vec(unsigned s, unsigned size)
  {
    std::vector<bool> v(size);
    for (unsigned i = 0; i < size; ++i)
      {
        v[i] = s % 2;
        s >>= 1;
      }
    return v;
  }

  // Switch initial state and 0 in the AIGER encoding, so that the
  // 0-initialized latches correspond to the initial state.
  unsigned encode_init_0(unsigned src, unsigned init)
  {
    return src == init ? 0 : src == 0 ? init : src;
  }

  aig aut_to_aiger(const spot::twa_graph_ptr& aut,
                     bdd all_inputs, bdd all_outputs)
  {
    // Encode state in log2(num_states) latches.
    unsigned log2n = std::ceil(std::log2(aut->num_states()));
    unsigned st0 = aut->get_dict()->register_anonymous_variables(log2n, aut);
    bdd all_states = bddtrue;
    for (unsigned i = 0; i < log2n; ++i)
      all_states &= bdd_ithvar(st0 + i);

    unsigned num_inputs = bdd_nodecount(all_inputs);
    unsigned num_outputs = bdd_nodecount(all_outputs);
    unsigned num_latches = bdd_nodecount(all_states);
    unsigned init = aut->get_init_state_number();

    aig circuit(num_inputs, num_latches, num_outputs);
    bdd b;

    // Latches and outputs are expressed as a DNF in which each term represents
    // a transition.
    // latch[i] (resp. out[i]) represents the i-th latch's (resp.  output's)
    // DNF.
    std::vector<std::vector<unsigned>> latch(num_latches);
    std::vector<std::vector<unsigned>> out(num_outputs);
    for (unsigned s = 0; s < aut->num_states(); ++s)
      for (auto& e: aut->out(s))
        {
          spot::minato_isop cond(e.cond);
          while ((b = cond.next()) != bddfalse)
            {
              bdd input = bdd_existcomp(b, all_inputs);
              bdd letter_out = bdd_existcomp(b, all_outputs);
              auto out_vec = output_to_vec(letter_out);
              unsigned dst = encode_init_0(e.dst, init);
              auto next_state_vec = state_to_vec(dst, log2n);
              unsigned src = encode_init_0(s, init);
              bdd state_bdd = state_to_bdd(src, all_states);
              std::vector<unsigned> prod;
              while (input != bddfalse && input != bddtrue)
                {
                  unsigned v =
                    circuit.input_var(bddvar_to_inputnum[bdd_var(input)],
                                      bdd_ithvar(bdd_var(input)));
                  if (bdd_high(input) == bddfalse)
                    {
                      v = circuit.aig_not(v);
                      input = bdd_low(input);
                    }
                  else
                    input = bdd_high(input);
                  prod.push_back(v);
                }

              while (state_bdd != bddfalse && state_bdd != bddtrue)
                {
                  unsigned v =
                    circuit.latch_var(bdd_var(state_bdd) - st0,
                                      bdd_ithvar(bdd_var(state_bdd)));
                  if (bdd_high(state_bdd) == bddfalse)
                    {
                      v = circuit.aig_not(v);
                      state_bdd = bdd_low(state_bdd);
                    }
                  else
                      state_bdd = bdd_high(state_bdd);
                  prod.push_back(v);
                }
              unsigned t = circuit.aig_and(prod);
              for (unsigned i = 0; i < next_state_vec.size(); ++i)
                if (next_state_vec[i])
                  latch[i].push_back(t);
              for (unsigned i = 0; i < num_outputs; ++i)
                if (out_vec[i])
                  out[i].push_back(t);
            }
        }
    for (unsigned i = 0; i < num_latches; ++i)
      circuit.set_latch(i, circuit.aig_or(latch[i]));
    for (unsigned i = 0; i < num_outputs; ++i)
      circuit.set_output(i, circuit.aig_or(out[i]));
    circuit.remove_unused();
    return circuit;
  }

  class ltl_processor final : public job_processor
  {
  private:
    spot::translator& trans_;
    std::vector<std::string> input_aps_;
    std::vector<std::string> output_aps_;

  public:

    ltl_processor(spot::translator& trans,
                  std::vector<std::string> input_aps_,
                  std::vector<std::string> output_aps_)
      : trans_(trans), input_aps_(input_aps_), output_aps_(output_aps_)
    {
    }

    int process_formula(spot::formula f,
                        const char*, int) override
    {
      auto aut = trans_.run(&f);
      bdd all_inputs = bddtrue;
      bdd all_outputs = bddtrue;
      for (unsigned i = 0; i < input_aps_.size(); ++i)
        {
          std::ostringstream lowercase;
          for (char c: input_aps_[i])
            lowercase << (char)std::tolower(c);
          unsigned v = aut->register_ap(spot::formula::ap(lowercase.str()));
          all_inputs &= bdd_ithvar(v);
          bddvar_to_inputnum[v] = i;
        }
      for (unsigned i = 0; i < output_aps_.size(); ++i)
        {
          std::ostringstream lowercase;
          for (char c: output_aps_[i])
            lowercase << (char)std::tolower(c);
          unsigned v = aut->register_ap(spot::formula::ap(lowercase.str()));
          all_outputs &= bdd_ithvar(v);
          bddvar_to_outputnum[v] = i;
        }
      auto split = split_automaton(aut, all_inputs);
      auto dpa = to_dpa(split);
      auto owner = make_alternating_owner(dpa);
      auto pg = spot::parity_game(dpa, owner);
      if (opt_print_pg)
        {
          pg.print(std::cout);
          return 0;
        }
      switch (opt_solver)
        {
          case REC:
            {
              spot::parity_game::strategy_t strategy;
              spot::parity_game::region_t winning_region;
              std::tie(winning_region, strategy) = pg.solve();
              if (winning_region.count(pg.get_init_state_number()))
                {
                  std::cout << "REALIZABLE\n";
                  if (!opt_real)
                    {
                      auto strat_aut = strat_to_aut(pg, strategy, dpa, all_outputs);
                      auto circuit = aut_to_aiger(strat_aut, all_inputs, all_outputs);
                      circuit.print();
                    }
                }
              else
                std::cout << "UNREALIZABLE\n";
              return 0;
            }
          case QP:
            if (!opt_real)
              {
                std::cout << "The quasi-polynomial time algorithm does not"
                  " implement synthesis yet, use --realizability\n";
                return 1;
              }
            else if (pg.solve_qp())
              std::cout << "REALIZABLE\n";
            else
              std::cout << "UNREALIZABLE\n";
            return 0;
          default:
            SPOT_UNREACHABLE();
            return 0;
        }
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
    case OPT_OUTPUT:
      {
        std::istringstream aps(arg);
        std::string ap;
        while (std::getline(aps, ap, ','))
          {
            ap.erase(remove_if(ap.begin(), ap.end(), isspace), ap.end());
            output_aps.push_back(ap);
          }
        break;
      }
    case OPT_PRINT:
      opt_print_pg = true;
      break;
    case OPT_ALGO:
      if (arg && strcmp(arg, "rec") == 0)
        opt_solver = REC;
      else if (arg && strcmp(arg, "qp") == 0)
        opt_solver = QP;
      else
        {
          std::cout << "Unknown solver: " << (arg ? arg : "") << '\n';
          return 1;
        }
      break;
    case OPT_REAL:
      opt_real = true;
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
  check_no_formula();

  spot::translator trans;
  ltl_processor processor(trans, input_aps, output_aps);
  processor.run();
}
