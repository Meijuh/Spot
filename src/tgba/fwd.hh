// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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

#ifndef SPOT_TGBA_FWD_HH
# define SPOT_TGBA_FWD_HH

#include <memory>

namespace spot
{
  class tgba;
  typedef std::shared_ptr<tgba> tgba_ptr;
  typedef std::shared_ptr<const tgba> const_tgba_ptr;

  class tgba_digraph;
  typedef std::shared_ptr<const tgba_digraph> const_tgba_digraph_ptr;
  typedef std::shared_ptr<tgba_digraph> tgba_digraph_ptr;

  class tgba_product;
  typedef std::shared_ptr<const tgba_product> const_tgba_product_ptr;
  typedef std::shared_ptr<tgba_product> tgba_product_ptr;
}

#endif // SPOT_TGBA_FWD_HH
