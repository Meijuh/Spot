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
  auto d = spot::make_bdd_dict();

  auto& e = spot::ltl::default_environment::instance();

  auto tg = make_twa_graph(d);

  auto* f1 = e.require("p1");
  auto* f2 = e.require("p2");
  bdd p1 = bdd_ithvar(d->register_proposition(f1, tg));
  bdd p2 = bdd_ithvar(d->register_proposition(f2, tg));
  tg->acc().add_sets(2);
  f1->destroy();
  f2->destroy();

  auto s1 = tg->new_state();
  auto s2 = tg->new_state();
  auto s3 = tg->new_state();
  tg->new_transition(s1, s1, bddfalse, 0U);
  tg->new_transition(s1, s2, p1, 0U);
  tg->new_transition(s1, s3, p2, tg->acc().mark(1));
  tg->new_transition(s2, s3, p1 & p2, tg->acc().mark(0));
  tg->new_transition(s3, s1, p1 | p2, tg->acc().marks({0, 1}));
  tg->new_transition(s3, s2, p1 >> p2, 0U);
  tg->new_transition(s3, s3, bddtrue, tg->acc().marks({0, 1}));

  spot::dotty_reachable(std::cout, tg);

  {
    auto i = tg->get_graph().out_iteraser(s3);
    ++i;
    i.erase();
    i.erase();
    assert(!i);
    spot::dotty_reachable(std::cout, tg);
  }

  {
    auto i = tg->get_graph().out_iteraser(s3);
    i.erase();
    assert(!i);
    spot::dotty_reachable(std::cout, tg);
  }

  auto all = tg->acc().marks({0, 1});
  tg->new_transition(s3, s1, p1 | p2, all);
  tg->new_transition(s3, s2, p1 >> p2, 0U);
  tg->new_transition(s3, s1, bddtrue, all);

  std::cerr << tg->num_transitions() << '\n';
  assert(tg->num_transitions() == 7);

  spot::dotty_reachable(std::cout, tg);
  tg->merge_transitions();
  spot::dotty_reachable(std::cout, tg);

  std::cerr << tg->num_transitions() << '\n';
  assert(tg->num_transitions() == 5);

  // Add enough states so that the state vector is reallocated.
  for (unsigned i = 0; i < 100; ++i)
    tg->new_state();
  spot::dotty_reachable(std::cout, tg);
}

int main()
{
  f1();
}
