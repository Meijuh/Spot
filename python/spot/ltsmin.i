// -*- coding: utf-8 -*-
// Copyright (C) 2016 Laboratoire de Recherche et Développement de
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

%{
  // Workaround for SWIG 2.0.2 using ptrdiff_t but not including cstddef.
  // It matters with g++ 4.6.
#include <cstddef>
%}

%module(package="spot", director="1") ltsmin

%include "std_string.i"
%include "std_set.i"
%include "std_shared_ptr.i"

%shared_ptr(spot::bdd_dict)
%shared_ptr(spot::twa)
%shared_ptr(spot::kripke)
%shared_ptr(spot::fair_kripke)

%{
#include <spot/ltsmin/ltsmin.hh>
using namespace spot;
%}

%import(module="spot.impl") <spot/misc/common.hh>
%import(module="spot.impl") <spot/twa/bdddict.hh>
%import(module="spot.impl") <spot/twa/twa.hh>
%import(module="spot.impl") <spot/tl/formula.hh>
%import(module="spot.impl") <spot/tl/apcollect.hh>
%import(module="spot.impl") <spot/kripke/fairkripke.hh>
%import(module="spot.impl") <spot/kripke/kripke.hh>

namespace std {
  %template(atomic_prop_set) set<spot::formula>;
}

%include <spot/ltsmin/ltsmin.hh>

%pythoncode %{
import spot

def load(filename, ap_set, dict=spot._bdd_dict,
         dead=spot.formula_ap('dead'),
         compress=2, debug=False):
  s = spot.atomic_prop_set()
  for ap in ap_set:
    s.insert(spot.formula_ap(ap))
  return load_ltsmin(filename, dict, s, dead, compress, debug)
%}
