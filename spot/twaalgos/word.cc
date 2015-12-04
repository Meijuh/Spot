// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et Développement
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

#include <spot/twaalgos/word.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twa/bdddict.hh>

namespace spot
{
  twa_word::twa_word(const twa_run_ptr run)
    : dict_(run->aut->get_dict())
  {
    for (auto& i: run->prefix)
      prefix.push_back(i.label);
    for (auto& i: run->cycle)
      cycle.push_back(i.label);
    dict_->register_all_variables_of(run->aut, this);
  }

  void
  twa_word::simplify()
  {
    // If all the formulas on the cycle are compatible, reduce the
    // cycle to a simple conjunction.
    //
    // For instance
    //   !a|!b; b; a&b; cycle{a; b; a&b}
    // can be reduced to
    //   !a|!b; b; a&b; cycle{a&b}
    {
      bdd all = bddtrue;
      for (auto& i: cycle)
	all &= i;
      if (all != bddfalse)
	{
	  cycle.clear();
	  cycle.push_back(all);
	}
    }
    // If the last formula of the prefix is compatible with the
    // last formula of the cycle, we can shift the cycle and
    // reduce the prefix.
    //
    // For instance
    //   !a|!b; b; a&b; cycle{a&b}
    // can be reduced to
    //   !a|!b; cycle{a&b}
    while (!prefix.empty())
      {
	bdd a = prefix.back() & cycle.back();
	if (a == bddfalse)
	  break;
	prefix.pop_back();
	cycle.pop_back();
	cycle.push_front(a);
      }
    // Get rid of any disjunction.
    //
    // For instance
    //   !a|!b; cycle{a&b}
    // can be reduced to
    //   !a&!b; cycle{a&b}
    for (auto& i: prefix)
      i = bdd_satone(i);
    for (auto& i: cycle)
      i = bdd_satone(i);
  }

  std::ostream&
  operator<<(std::ostream& os, const twa_word& w)
  {
    auto d = w.get_dict();
    if (!w.prefix.empty())
      for (auto& i: w.prefix)
	{
	  bdd_print_formula(os, d, i);
	  os << "; ";
	}
    assert(!w.cycle.empty());
    bool notfirst = false;
    os << "cycle{";
    for (auto& i: w.cycle)
      {
	if (notfirst)
	  os << "; ";
	notfirst = true;
	bdd_print_formula(os, d, i);
      }
    os << '}';
    return os;
  }
}
