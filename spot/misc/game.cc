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
#include "spot/misc/game.hh"

namespace spot
{

void parity_game::print(std::ostream& os)
{
  os << "parity " << num_states() - 1 << ";\n";
  std::vector<bool> seen(num_states(), false);
  std::vector<unsigned> todo({get_init_state_number()});
  while (!todo.empty())
    {
      unsigned src = todo.back();
      todo.pop_back();
      seen[src] = true;
      os << src << ' ';
      os << out(src).begin()->acc.max_set() - 1 << ' ';
      os << owner(src) << ' ';
      bool first = true;
      for (auto& e: out(src))
        {
          if (!first)
            os << ',';
          first = false;
          os << e.dst;
          if (!seen[e.dst])
            todo.push_back(e.dst);
        }
      if (src == get_init_state_number())
        os << " \"INIT\"";
      os << ";\n";
    }
}

std::pair<parity_game::region_t, parity_game::strategy_t>
parity_game::solve() const
{
  region_t states_;
  for (unsigned i = 0; i < num_states(); ++i)
    states_.insert(i);
  unsigned m = max_parity();
  return solve_rec(states_, m);
}

bool parity_game::solve_qp() const
{
  return reachability_game(*this).is_reachable();
}

parity_game::strategy_t
parity_game::attractor(const region_t& subgame, region_t& set,
                       unsigned max_parity, bool odd, bool attr_max) const
{
  strategy_t strategy;
  unsigned size;
  std::unordered_set<unsigned> complement = subgame;
  std::unordered_set<unsigned> delta = set;
  do
    {
      size = set.size();
      for (unsigned s: delta)
        complement.erase(s);
      for (unsigned s: complement)
        {
          bool any = false;
          bool all = true;
          unsigned i = 0;
          for (auto& e: out(s))
            {
              if (e.acc.max_set() - 1 <= max_parity && subgame.count(e.dst))
                {
                  if (set.count(e.dst)
                      || (attr_max && e.acc.max_set() - 1 == max_parity))
                    {
                      if (!any && owner_[s] && odd)
                        strategy[s] = i;
                      any = true;
                    }
                  else
                    all = false;
                }
              ++i;
            }
          if ((owner_[s] == odd && any) || (owner_[s] != odd && all))
            {
              set.insert(s);
              delta.insert(s);
            }
        }
    } while (set.size() != size);
  return strategy;
}

auto parity_game::solve_rec(region_t& subgame, unsigned max_parity) const
  -> std::pair<region_t, strategy_t>
{
  // The algorithm works recursively on subgames. To avoid useless copies of
  // the game at each call, subgame and max_parity are used to filter states
  // and transitions.
  if (max_parity == 0 || subgame.empty())
    return {};
  bool odd = max_parity % 2 == 1;
  region_t w1;
  strategy_t strategy;

  // Recursion on max_parity.
  region_t u;
  auto strat_u = attractor(subgame, u, max_parity, odd, true);

  for (unsigned s: u)
    subgame.erase(s);
  region_t w00; // Even's winning region in the first recursive call.
  region_t w10; // Odd's winning region in the first recursive call.
  strategy_t s10; // Odd's winning strategy in the first recursive call.
  std::tie(w10, s10) = solve_rec(subgame, max_parity - 1);
  if (odd && w10.size() != subgame.size())
    for (unsigned s: subgame)
      if (w10.find(s) == w10.end())
        w00.insert(s);
  // If !odd, w00 is not used, no need to compute it.
  subgame.insert(u.begin(), u.end());

  if (odd && w10.size() + u.size() == subgame.size())
    {
      strategy.insert(s10.begin(), s10.end());
      strategy.insert(strat_u.begin(), strat_u.end());
      w1.insert(subgame.begin(), subgame.end());
      return {w1, strategy};
    }
  else if (!odd && w10.empty())
    return {};

  // Recursion on game size.
  auto& wni = odd ? w00 : w10;
  auto strat_wni = attractor(subgame, wni, max_parity, !odd);
  if (!odd)
    strat_wni.insert(s10.begin(), s10.end());

  for (unsigned s: wni)
    subgame.erase(s);

  region_t w11; // Odd's winning region in the second recursive call.
  strategy_t s11; // Odd's winning strategy in the second recursive call.
  std::tie(w11, s11) = solve_rec(subgame, max_parity);

  w1.insert(w11.begin(), w11.end());
  strategy.insert(s11.begin(), s11.end());
  if (!odd)
    {
      strategy.insert(strat_wni.begin(), strat_wni.end());
      w1.insert(wni.begin(), wni.end());
    }
  subgame.insert(wni.begin(), wni.end());
  return {w1, strategy};
}

int reachability_state::compare(const state* other) const
{
  auto o = down_cast<const reachability_state*>(other);
  assert(o);
  if (num_ != o->num())
    return num_ - o->num();
  if (b_ < o->b())
    return -1;
  if (b_ > o->b())
    return 1;
  return 0;
}

bool reachability_state::operator<(const reachability_state& o) const
{
  // Heuristic to process nodes with a higher chance of leading to a target
  // node first.
  assert(b_.size() == o.b().size());
  for (unsigned i = b_.size(); i > 0; --i)
    if (b_[i - 1] != o.b()[i - 1])
      return b_[i - 1] > o.b()[i - 1];
  return num_ < o.num();
}



const reachability_state* reachability_game_succ_iterator::dst() const
{
  // NB: colors are indexed at 1 in Calude et al.'s paper and at 0 in spot
  // All acceptance sets are therefore incremented (which is already done by
  // max_set), so that 0 can be kept as a special value indicating that no
  // i-sequence is tracked at this index. Hence the parity switch in the
  // following implementation, compared to the paper.
  std::vector<unsigned> b = state_.b();
  unsigned a = it_->acc.max_set();
  assert(a);
  unsigned i = -1U;
  bool all_even = a % 2 == 0;
  for (unsigned j = 0; j < b.size(); ++j)
    {
      if ((b[j] % 2 == 1 || b[j] == 0) && all_even)
        i = j;
      else if (b[j] > 0 && a > b[j])
        i = j;
      all_even = all_even && b[j] > 0 && b[j] % 2 == 0;
    }
  if (i != -1U)
    {
      b[i] = a;
      for (unsigned j = 0; j < i; ++j)
        b[j] = 0;
    }
  return new reachability_state(it_->dst, b, !state_.anke());
}



const reachability_state* reachability_game::get_init_state() const
{
  // b[ceil(log(n + 1))] != 0 implies there is an i-sequence of length
  // 2^(ceil(log(n + 1))) >= 2^log(n + 1) = n + 1, so it has to contain a
  // cycle.
  unsigned i = std::ceil(std::log2(pg_.num_states() + 1));
  return new reachability_state(pg_.get_init_state_number(),
                                std::vector<unsigned>(i + 1),
                                false);
}

reachability_game_succ_iterator*
reachability_game::succ_iter(const state* s) const
{
  auto state = down_cast<const reachability_state*>(s);
  return new reachability_game_succ_iterator(pg_, *state);
}

std::string reachability_game::format_state(const state* s) const
{
  auto state = down_cast<const reachability_state*>(s);
  std::ostringstream fmt;
  bool first = true;
  fmt << state->num() << ", ";
  fmt << '[';
  for (unsigned b : state->b())
    {
      if (!first)
        fmt << ',';
      else
        first = false;
      fmt << b;
    }
  fmt << ']';
  return fmt.str();
}

bool reachability_game::is_reachable()
{
  std::set<spot::reachability_state> todo{*init_state_};
  while (!todo.empty())
    {
      spot::reachability_state v = *todo.begin();
      todo.erase(todo.begin());

      std::vector<spot::const_reachability_state_ptr> succs;
      spot::reachability_game_succ_iterator* it = succ_iter(&v);
      for (it->first(); !it->done(); it->next())
        succs.push_back(spot::const_reachability_state_ptr(it->dst()));

      if (is_target(v))
        {
          c_[v] = 1;
          if (mark(v))
            return true;
          continue;
        }
      else if (v.anke())
        c_[v] = 1;
      else
        c_[v] = succs.size();
      for (auto succ: succs)
        {
          if (parents_[*succ].empty())
            {
              if (*succ != *init_state_)
                {
                  todo.insert(*succ);
                  parents_[*succ] = { v };
                  c_[*succ] = -1U;
                }
            }
          else
            {
              parents_[*succ].push_back(v);
              if (c_[*succ] == 0 && mark(v))
                return true;
            }
        }
    }
  return false;
}

bool reachability_game::mark(const spot::reachability_state& s)
{
  if (c_[s] > 0)
    {
      --c_[s];
      if (c_[s] == 0)
        {
          if (s == *init_state_)
            return true;
          for (auto& u: parents_[s])
            if (mark(u))
              return true;
        }
    }
  return false;
}

bool reachability_game::is_target(const reachability_state& v)
{
  return v.b().back();
}

}
