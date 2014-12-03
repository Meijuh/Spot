// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2012, 2013, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include "config.h"
#include "random.hh"

namespace spot
{
  static std::mt19937 gen;

  void
  srand(unsigned int seed)
  {
    gen.seed(seed);
  }

  double
  drand()
  {
    return
      std::generate_canonical<double,
			      std::numeric_limits<double>::digits>(gen);
  }

  int
  mrand(int max)
  {
    std::uniform_int_distribution<> dis(0, max - 1);
    return dis(gen);
  }

  int
  rrand(int min, int max)
  {
    std::uniform_int_distribution<> dis(min, max);
    return dis(gen);
  }

  int
  barand::rand()
  {
    return (*this)(gen);
  }
}
