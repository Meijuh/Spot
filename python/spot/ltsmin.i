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

%exception {
  try {
    $action
  }
  catch (const std::runtime_error& e)
  {
    SWIG_exception(SWIG_RuntimeError, e.what());
  }
}

namespace std {
  %template(atomic_prop_set) set<spot::formula>;
}

%rename(model) spot::ltsmin_model;
%rename(kripke_raw) spot::ltsmin_model::kripke;
%include <spot/ltsmin/ltsmin.hh>

%pythoncode %{
import spot

def load(filename):
  return model.load(filename)

@spot._extend(model)
class model:
  def kripke(self, ap_set, dict=spot._bdd_dict,
	      dead=spot.formula_ap('dead'),
	      compress=2):
    s = spot.atomic_prop_set()
    for ap in ap_set:
      s.insert(spot.formula_ap(ap))
    return self.kripke_raw(s, dict, dead, compress)

  def info(self):
    res = {}
    ss = self.state_size()
    res['state_size'] = ss
    res['variables'] = [(self.state_variable_name(i),
			 self.state_variable_type(i)) for i in range(ss)]
    tc = self.type_count()
    res['types'] = [(self.type_name(i),
		     [self.type_value_name(i, j)
		      for j in range(self.type_value_count(i))])
		     for i in range(tc)]
    return res

  def __repr__(self):
    res = "ltsmin model with the following variables:\n";
    info = self.info()
    for (var, t) in info['variables']:
      res += '  ' + var + ': ';
      type, vals = info['types'][t]
      if vals:
        res += str(vals)
      else:
        res += type
      res += '\n';
    return res
%}
