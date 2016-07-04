// -*- coding: utf-8 -*-
// Copyright (C) 2016 Laboratoire de Recherche et Développement
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

#include <cassert>
#include <ctime>
#include <vector>
#include <spot/twaalgos/dualize.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/iscolored.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/randomgraph.hh>
#include <spot/misc/random.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twa/fwd.hh>
#include <spot/twa/acc.hh>
#include <spot/misc/trival.hh>
#include <utility>
#include <string>
#include <iostream>

#define LAST_AUT result.back().first
#define LAST_NUM_SETS result.back().second
#define NEW_AUT() do {                                                      \
  result.emplace_back(spot::random_graph(6, 0.5, &apf,                      \
                      current_bdd, 0, 0, 0.5, true), 0);                    \
  LAST_NUM_SETS = 0;                                                        \
  /* print_hoa need this */                                                 \
  LAST_AUT->prop_state_acc(spot::trival::maybe());                          \
} while (false)

#define SET_TR(t, value) do {                                               \
  unsigned value_tmp = value;                                               \
  if (value_tmp + 1 > LAST_NUM_SETS)                                        \
    LAST_NUM_SETS = value_tmp + 1;                                          \
  t.acc.set(value_tmp);                                                     \
} while (false)


static std::vector<std::pair<spot::twa_graph_ptr, unsigned>>
generate_aut(const spot::bdd_dict_ptr& current_bdd)
{
  spot::atomic_prop_set apf = spot::create_atomic_prop_set(3);
  std::vector<std::pair<spot::twa_graph_ptr, unsigned>> result;
  // No accset on any transition
  NEW_AUT();
  // The same accset on every transitions
  NEW_AUT();
  for (auto& t: LAST_AUT->edges())
    SET_TR(t, 0);

  // All used / First unused / Last unused / First and last unused
  for (auto incr_ext: { 0, 1 })
    for (auto used: { 1, 2 })
      for (auto modulo: { 4, 5, 6 })
        if (incr_ext + modulo <= 6)
          {
            NEW_AUT();
            unsigned count = 0;
            for (auto& t: LAST_AUT->edges())
              if (std::rand() % used == 0)
                {
                  auto value = ++count % modulo + incr_ext;
                  SET_TR(t, value);
                }
          }

  // One-Three in middle not used
  for (auto i: { 0, 1 })
    for (auto start: { 1, 2 })
      for (auto unused: { 1, 2, 3 })
        {
          NEW_AUT();
          auto count = 0;
          for (auto& t: LAST_AUT->edges())
            {
              int val = 0;
              if (count % (3 + i) < start)
                val = count % (3 + i);
              else
                val = count % (3 + i) + unused;
              SET_TR(t, val);
            }
        }

  // All accset on all transitions
  for (auto i: { 0, 1 })
  {
    NEW_AUT();
    for (auto& t: LAST_AUT->edges())
      for (auto acc = 0; acc < 5 + i; ++acc)
        SET_TR(t, acc);
  }

  // Some random automata
  std::vector<std::vector<int>> cont_sets;
  for (auto i = 0; i <= 6; ++i)
    {
      std::vector<int> cont_set;
      for (auto j = 0; j < i; ++j)
        cont_set.push_back(j);
      cont_sets.push_back(cont_set);
    }
  for (auto min: { 0, 1 })
    {
      for (auto num_sets: { 1, 2, 5, 6 })
        for (auto i = 0; i < 10; ++i)
          {
            NEW_AUT();
            for (auto& t: LAST_AUT->edges())
              {
                auto nb_acc = std::rand() % (num_sets - min + 1) + min;
                std::random_shuffle(cont_sets[num_sets].begin(),
                                    cont_sets[num_sets].end());
                for (auto j = 0; j < nb_acc; ++j)
                  SET_TR(t, cont_sets[num_sets][j]);
              }
          }
      for (auto num_sets: {2, 3})
        for (auto even: {0, 1})
          if ((num_sets - 1) * 2 + even < 6)
            {
              NEW_AUT();
              for (auto& t: LAST_AUT->edges())
                {
                  auto nb_acc = std::rand() % (num_sets - min + 1) + min;
                  std::random_shuffle(cont_sets[num_sets].begin(),
                                      cont_sets[num_sets].end());
                  for (auto j = 0; j < nb_acc; ++j)
                    {
                      auto value = cont_sets[num_sets][j] * 2 + even;
                      SET_TR(t, value);
                    }
                }
            }
    }
  return result;
}

static std::vector<std::tuple<spot::acc_cond::acc_code, bool, bool, unsigned>>
generate_acc()
{
  std::vector<std::tuple<spot::acc_cond::acc_code, bool, bool, unsigned>>
  result;
  for (auto max: { true, false })
    for (auto odd: { true, false })
      for (auto num_sets: { 0, 1, 2, 5, 6 })
        result.emplace_back(spot::acc_cond::acc_code::parity(max, odd,
                            num_sets), max, odd, num_sets);
  return result;
}

static bool is_included(spot::const_twa_graph_ptr left,
                        spot::const_twa_graph_ptr right, bool first_left)
{
  auto tmp = spot::dualize(right);
  auto product = spot::product(left, tmp);
  if (!product->is_empty())
    {
      std::cerr << "======Not included======" << std::endl;
      if (first_left)
        std::cerr << "======First automaton======" << std::endl;
      else
        std::cerr << "======Second automaton======" << std::endl;
      spot::print_hoa(std::cerr, left);
      std::cerr << std::endl;
      if (first_left)
        std::cerr << "======Second automaton======" << std::endl;
      else
        std::cerr << "======First automaton======" << std::endl;
      spot::print_hoa(std::cerr, right);
      std::cerr << std::endl;
      if (first_left)
        std::cerr << "======!Second automaton======" << std::endl;
      else
        std::cerr << "======!First automaton======" << std::endl;
      spot::print_hoa(std::cerr, tmp);
      std::cerr << std::endl;
      if (first_left)
        std::cerr << "======First X !Second======" <<std::endl;
      else
        std::cerr << "======Second X !First======" <<std::endl;
      spot::print_hoa(std::cerr, product);
      std::cerr << std::endl;
      return false;
    }
  return true;
}

static bool are_equiv(spot::const_twa_graph_ptr left,
                      spot::const_twa_graph_ptr right)
{
  return is_included(left, right, true) && is_included(right, left, false);
}

static bool is_right_parity(spot::const_twa_graph_ptr aut,
                            spot::parity_kind target_kind,
                            spot::parity_style target_style,
                            bool origin_max, bool origin_odd, unsigned num_sets)
{
  bool is_max;
  bool is_odd;
  if (!aut->acc().is_parity(is_max, is_odd))
    return false;
  bool target_max;
  bool target_odd;
  if (aut->num_sets() <= 1 || num_sets <= 1
      || target_kind == spot::parity_kind_any)
    target_max = is_max;
  else if (target_kind == spot::parity_kind_max)
    target_max = true;
  else if (target_kind == spot::parity_kind_min)
    target_max = false;
  else
    target_max = origin_max;
  if (aut->num_sets() == 0 || num_sets == 0
      || target_style == spot::parity_style_any)
    target_odd = is_odd;
  else if (target_style == spot::parity_style_odd)
    target_odd = true;
  else if (target_style == spot::parity_style_even)
    target_odd = false;
  else
    target_odd = origin_odd;
  if (!(is_max == target_max && is_odd == target_odd))
    {
      std::cerr << "======Wrong accceptance======" << std::endl;
      std::string kind[] = { "max", "min", "same", "any" };
      std::string style[] = { "odd", "even", "same", "any" };
      std::cerr << "target: " << kind[target_kind] << ' '
                << style[target_style] << std::endl;
      std::cerr << "origin: " << kind[origin_max ? 0 : 1] << ' '
                << style[origin_odd ? 0 : 1] << ' '
                << num_sets << std::endl;
      std::cerr << "actually: " << kind[is_max ? 0 : 1] << ' '
                << style[is_odd ? 0 : 1] << ' '
                << aut->num_sets() << std::endl;
      std::cerr << std::endl;
      return false;
    }
  return true;
}

static bool is_almost_colored(spot::const_twa_graph_ptr aut)
{
  for (auto t: aut->edges())
    if (t.acc.count() > 1)
      {
        std::cerr << "======Not colored======" << std::endl;
        spot::print_hoa(std::cerr, aut);
        std::cerr << std::endl;
        return false;
      }
  return true;
}

static bool is_colored_printerr(spot::const_twa_graph_ptr aut)
{
  bool result = is_colored(aut);
  if (!result)
    {
      std::cerr << "======Not colored======" << std::endl;
      spot::print_hoa(std::cerr, aut);
      std::cerr << std::endl;
    }
  return result;
}

static spot::parity_kind to_parity_kind(bool is_max)
{
  if (is_max)
    return spot::parity_kind_max;
  return spot::parity_kind_min;
}

static spot::parity_style to_parity_style(bool is_odd)
{
  if (is_odd)
    return spot::parity_style_odd;
  return spot::parity_style_even;
}

int main()
{
  auto current_bdd = spot::make_bdd_dict();
  spot::srand(0);
  auto parity_kinds =
  {
    spot::parity_kind_max,
    spot::parity_kind_min,
    spot::parity_kind_same,
    spot::parity_kind_any,
  };
  auto parity_styles =
  {
    spot::parity_style_odd,
    spot::parity_style_even,
    spot::parity_style_same,
    spot::parity_style_any,
  };

  auto acceptance_sets = generate_acc();
  auto automata_tuples = generate_aut(current_bdd);

  unsigned num_automata = automata_tuples.size();
  unsigned num_acceptance = acceptance_sets.size();

  std::cerr << "num of automata: " << num_automata << '\n';
  std::cerr << "num of acceptance expression: " << num_acceptance << '\n';

  for (auto acc_tuple: acceptance_sets)
    for (auto& aut_tuple: automata_tuples)
      {
        auto& aut = aut_tuple.first;
        auto aut_num_sets = aut_tuple.second;

        auto acc = std::get<0>(acc_tuple);
        auto is_max = std::get<1>(acc_tuple);
        auto is_odd = std::get<2>(acc_tuple);
        auto acc_num_sets = std::get<3>(acc_tuple);
        if (aut_num_sets <= acc_num_sets)
          {
            aut->set_acceptance(acc_num_sets, acc);
            // Check change_parity
            for (auto kind: parity_kinds)
              for (auto style: parity_styles)
                {
                  auto output = spot::change_parity(aut, kind, style);
                  assert(is_right_parity(output, kind, style,
                                         is_max, is_odd, acc_num_sets)
                         && "change_parity: wrong acceptance.");
                  assert(are_equiv(aut, output)
                         && "change_parity: not equivalent.");
                  assert(is_almost_colored(output)
                         && "change_parity: too many acc on a transition");
                }
            // Check colorize_parity
            for (auto keep_style: { true, false })
              {
                auto output = spot::colorize_parity(aut, keep_style);
                assert(is_colored_printerr(output)
                       && "colorize_parity: not colored.");
                assert(are_equiv(aut, output)
                       && "colorize_parity: not equivalent.");
                auto target_kind = to_parity_kind(is_max);
                auto target_style = keep_style ? to_parity_style(is_odd)
                                    : spot::parity_style_any;
                assert(is_right_parity(output, target_kind, target_style,
                                       is_max, is_odd, acc_num_sets)
                       && "change_parity: wrong acceptance.");
              }
            // Check cleanup_parity
            for (auto keep_style: { true, false })
              {
                auto output = spot::cleanup_parity(aut, keep_style);
                assert(is_almost_colored(output)
                       && "cleanup_parity: too many acc on a transition.");
                assert(are_equiv(aut, output)
                       && "cleanup_parity: not equivalent.");
                auto target_kind = to_parity_kind(is_max);
                auto target_style = keep_style ? to_parity_style(is_odd)
                                    : spot::parity_style_any;
                assert(is_right_parity(output, target_kind, target_style,
                                       is_max, is_odd, acc_num_sets)
                       && "cleanup_parity: wrong acceptance.");
              }
          }
        }

  std::random_shuffle(automata_tuples.begin(), automata_tuples.end());
  unsigned num_left = 15;
  unsigned num_right = 15;
  unsigned acc_index = 0;

  unsigned nb = 0;
  // Parity product and sum
  for (unsigned left_index = 0; left_index < num_left; ++left_index)
    {
      auto& aut_tuple_first = automata_tuples[left_index % num_automata];
      auto& left = aut_tuple_first.first;
      auto aut_num_sets_first = aut_tuple_first.second;
      while (std::get<3>(acceptance_sets[acc_index]) < aut_num_sets_first)
        acc_index = (acc_index + 1) % num_acceptance;
      auto acc_tuple_first = acceptance_sets[acc_index];
      acc_index = (acc_index + 1) % num_acceptance;
      auto acc_first = std::get<0>(acc_tuple_first);
      auto acc_num_sets_first = std::get<3>(acc_tuple_first);
      left->set_acceptance(acc_num_sets_first, acc_first);
      for (unsigned right_index = 0; right_index < num_right; ++right_index)
        {
          auto& aut_tuple_second =
            automata_tuples[(num_left + right_index) % num_automata];
          auto& right = aut_tuple_second.first;
          auto aut_num_sets_second = aut_tuple_second.second;
          while (std::get<3>(acceptance_sets[acc_index]) < aut_num_sets_second)
            acc_index = (acc_index + 1) % num_acceptance;
          auto acc_tuple_second = acceptance_sets[acc_index];
          acc_index = (acc_index + 1) % num_acceptance;
          auto acc_second = std::get<0>(acc_tuple_second);
          auto acc_num_sets_second = std::get<3>(acc_tuple_second);
          right->set_acceptance(acc_num_sets_second, acc_second);
          auto result_prod = spot::parity_product(left, right);
          auto ref_prod = spot::product(left, right);
          if (!are_equiv(result_prod, ref_prod))
            {
              std::cerr << nb << ": parity_product: Not equivalent.\n"
                        << "=====First Automaton=====\n";
              spot::print_hoa(std::cerr, left);
              std::cerr << "=====Second Automaton=====\n";
              spot::print_hoa(std::cerr, right);
              assert(false && "parity_product: Not equivalent.\n");
            }
          assert(is_colored_printerr(result_prod)
                 && "parity_product: not colored.");
          assert(is_right_parity(result_prod, spot::parity_kind_any,
                                 spot::parity_style_any,
                                 true, true, 2)
                 && "parity_product: not a parity acceptance condition");

          auto result_sum = spot::parity_product_or(left, right);
          auto ref_sum = spot::product_or(left, right);
          if (!are_equiv(result_sum, ref_sum))
            {
              std::cerr << nb << ": parity_product_or: Not equivalent.\n"
                        << "=====First Automaton=====\n";
              spot::print_hoa(std::cerr, left);
              std::cerr << "=====Second Automaton=====\n";
              spot::print_hoa(std::cerr, right);
              assert(false && "parity_product_or: Not equivalent.\n");
            }
          assert(is_colored_printerr(result_sum)
                 && "parity_product_or: not colored.");
          assert(is_right_parity(result_sum, spot::parity_kind_any,
                                 spot::parity_style_any,
                                 true, true, 2)
                 && "parity_product_or: not a parity acceptance condition");
          ++nb;
        }
    }
  return 0;
}
