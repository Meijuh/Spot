// -*- coding: utf-8 -*-
// Copyright (C) 2012 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#include "common_sys.hh"
#include "common_cout.hh"
#include <iostream>
#include "error.h"

void check_cout()
{
  // Make sure we abort if we can't write to std::cout anymore
  // (like disk full or broken pipe with SIGPIPE ignored).
  if (!std::cout)
    error(2, 0, "error writing to standard output");
}

void flush_cout()
{
  std::cout.flush();
  check_cout();
}