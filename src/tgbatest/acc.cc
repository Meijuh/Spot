// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et Développement
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

#include <iostream>
#include <iterator>
#include <vector>
#include <cassert>
#include <cstdlib>
#include "tgba/acc.hh"

void check(spot::acc_cond& ac, spot::acc_cond::mark_t m)
{
  std::cout << '#' << m.count() << ": " << ac.format(m);
  if (!m)
    std::cout << "empty";
  if (ac.accepting(m))
    std::cout << " accepting";
  std::cout << '\n';
}

int main()
{
  spot::acc_cond ac(4);
  ac.set_generalized_buchi();
  std::cout << ac.get_acceptance() << '\n';

  auto m1 = ac.marks({0, 2});
  auto m2 = ac.marks({0, 3});
  auto m3 = ac.marks({2, 1});

  check(ac, m1);
  check(ac, m2);
  check(ac, m3);
  check(ac, m1 | m2);
  check(ac, m2 & m1);
  check(ac, m1 | m2 | m3);

  ac.add_set();
  ac.set_generalized_buchi();

  check(ac, m1);
  check(ac, m2);
  check(ac, m3);
  check(ac, m1 | m2);
  check(ac, m2 & m1);
  check(ac, m1 | m2 | m3);

  check(ac, m2 & m3);
  check(ac, ac.comp(m2 & m3));

  spot::acc_cond ac2(ac.num_sets());
  ac2.set_generalized_buchi();
  check(ac2, m3);

  spot::acc_cond ac3(ac.num_sets() + ac2.num_sets());
  ac3.set_generalized_buchi();
  std::cout << ac.num_sets() << " + "
	    << ac2.num_sets() << " = " << ac3.num_sets() << '\n';
  auto m5 = ac3.join(ac, m2, ac2, m3);
  check(ac3, m5);
  auto m6 = ac3.join(ac, ac.comp(m2 & m3), ac2, m3);
  check(ac3, m6);
  auto m7 = ac3.join(ac, ac.comp(m2 & m3), ac2, ac2.all_sets());
  check(ac3, m7);

  const char* comma = "";
  for (auto i: m7.sets())
    {
      std::cout << comma << i;
      comma = ",";
    };
  std::cout << '\n';

  spot::acc_cond ac4;
  ac4.set_generalized_buchi();
  check(ac4, ac4.all_sets());
  check(ac4, ac4.comp(ac4.all_sets()));

  check(ac, (m1 | m2).remove_some(2));

  std::vector<spot::acc_cond::mark_t> s = { m1, m2, m3 };
  check(ac, ac.useless(s.begin(), s.end()));
  s.push_back(ac.mark(4));
  auto u = ac.useless(s.begin(), s.end());
  check(ac, u);
  std::cout << "stripping\n";
  for (auto& v: s)
    {
      check(ac, v);
      check(ac, v.strip(u));
    }


  auto code1 = ac.inf({0, 1, 3});
  std::cout << code1.size() << ' ' << code1 << '\n';
  code1.append_or(ac.fin({2}));
  std::cout << code1.size() << ' ' << code1 << '\n';
  code1.append_or(ac.fin({0}));
  std::cout << code1.size() << ' ' << code1 << '\n';
  code1.append_or(ac.fin({}));
  std::cout << code1.size() << ' ' << code1 << '\n';
  code1.append_and(ac.inf({}));
  std::cout << code1.size() << ' ' << code1 << '\n';
  code1.append_and(ac.fin({}));
  std::cout << code1.size() << ' ' << code1 << '\n';
}
