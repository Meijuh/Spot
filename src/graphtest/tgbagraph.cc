// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement de
// l'Epita.
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
#include "tgba/tgbagraph.hh"
#include "tgbaalgos/dotty.hh"
#include "ltlenv/defaultenv.hh"

void f1()
{
  spot::bdd_dict d;

  auto& e = spot::ltl::default_environment::instance();

  spot::tgba_digraph tg(&d);
  auto& g = tg.get_graph();

  auto* f1 = e.require("p1");
  auto* f2 = e.require("p2");
  bdd p1 = bdd_ithvar(d.register_proposition(f1, &tg));
  bdd p2 = bdd_ithvar(d.register_proposition(f2, &tg));
  bdd a1 = bdd_ithvar(d.register_acceptance_variable(f1, &tg));
  bdd a2 = bdd_ithvar(d.register_acceptance_variable(f2, &tg));
  f1->destroy();
  f2->destroy();

  auto s1 = g.new_state();
  auto s2 = g.new_state();
  auto s3 = g.new_state();
  g.new_transition(s1, s1, bddfalse, bddfalse);
  g.new_transition(s1, s2, p1, bddfalse);
  g.new_transition(s1, s3, p2, !a1 & a2);
  g.new_transition(s2, s3, p1 & p2, a1 & !a2);
  g.new_transition(s3, s1, p1 | p2, (!a1 & a2) | (a1 & !a2));
  g.new_transition(s3, s2, p1 >> p2, bddfalse);
  g.new_transition(s3, s3, bddtrue, (!a1 & a2) | (a1 & !a2));

  spot::dotty_reachable(std::cout, &tg);

  {
    auto i = g.out_iteraser(s3);
    ++i;
    i.erase();
    i.erase();
    assert(!i);
    spot::dotty_reachable(std::cout, &tg);
  }

  {
    auto i = g.out_iteraser(s3);
    i.erase();
    assert(!i);
    spot::dotty_reachable(std::cout, &tg);
  }

  g.new_transition(s3, s1, p1 | p2, (!a1 & a2) | (a1 & !a2));
  g.new_transition(s3, s2, p1 >> p2, bddfalse);
  g.new_transition(s3, s1, bddtrue, (!a1 & a2) | (a1 & !a2));

  std::cerr << tg.num_transitions() << '\n';
  assert(tg.num_transitions() == 7);

  spot::dotty_reachable(std::cout, &tg);
  tg.merge_transitions();
  spot::dotty_reachable(std::cout, &tg);

  std::cerr << tg.num_transitions() << '\n';
  assert(tg.num_transitions() == 5);
}

int main()
{
  f1();
}