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

bool parity_game::solve_qp() const
{
  return reachability_game(*this).is_reachable();
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
