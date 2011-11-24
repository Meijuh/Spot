// Copyright (C) 2011 Laboratoire de Recherche et Developpement
// de l'Epita (LRDE)
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


#include "../kripkeparse/public.hh"
#include "../kripkeparse/parsedecl.hh"
#include "../kripke/kripkeprint.hh"
#include "../tgba/bddprint.hh"
#include "ltlast/allnodes.hh"


using namespace spot;

int main(int argc, char** argv)
{
  int returnValue = 0;
  kripke_parse_error_list pel;
  bdd_dict* dict = new bdd_dict;

  kripke_explicit* k = kripke_parse(argv[1], pel, dict);
  if (!pel.empty())
  {
    format_kripke_parse_errors(std::cerr, argv[1], pel);
    returnValue = 1;
  }

  if (!returnValue)
  {
    KripkePrinter* kp = new KripkePrinter(k, std::cout);
    kp->run();
    delete kp;
  }

  delete k;
  delete dict;
  assert(ltl::atomic_prop::instance_count() == 0);
  assert(ltl::unop::instance_count() == 0);
  assert(ltl::binop::instance_count() == 0);
  assert(ltl::multop::instance_count() == 0);
  return returnValue;
}
