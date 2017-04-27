// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement de
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

%module(package="spot", director="1") gen

%include "std_string.i"
%include "exception.i"
%include "std_shared_ptr.i"

%shared_ptr(spot::twa_graph)

%{
#include <spot/gen/automata.hh>
#include <spot/gen/formulas.hh>
using namespace spot;
%}

%import(module="spot.impl") <spot/misc/common.hh>
%import(module="spot.impl") <spot/tl/formula.hh>
%import(module="spot.impl") <spot/twa/fwd.hh>

%exception {
  try {
    $action
  }
  catch (const std::runtime_error& e)
  {
    SWIG_exception(SWIG_RuntimeError, e.what());
  }
}

%include <spot/gen/automata.hh>
%include <spot/gen/formulas.hh>

%pythoncode %{
def ltl_patterns(*args):
  """
  Generate LTL patterns.

  The arguments should be have one of these three forms:
    - (id, n)
    - (id, min, max)
    - id
  In the first case, the pattern id=n is generated.  In the second
  case, all pattern id=n for min<=n<=max are generated.  The
  third case is a shorthand for (id, 1, 10), except when
  id denotes one of the hard-coded list of LTL formulas (like,
  DAC_PATTERNS, EH_PATTERNS, etc.) where all formulas from that
  list are output.
  """
  for spec in args:
    if type(spec) is int:
      pat = spec
      min = 1
      max = ltl_pattern_max(spec) or 10
    else:
      ls = len(spec)
      if ls == 2:
        pat, min, max = spec[0], spec[1], spec[1]
      elif ls == 3:
        pat, min, max = spec
      else:
        raise RuntimeError("invalid pattern specification")
    for n in range(min, max + 1):
      yield ltl_pattern(pat, n)

def aut_patterns(*args):
  """
  Generate automata patterns.

  The arguments should be have one of these three forms:
    - (id, n)
    - (id, min, max)
    - id
  In the first case, the pattern id=n is generated.  In the second
  case, all pattern id=n for min<=n<=max are generated.  The
  third case is a shorthand for (id, 1, 10).
  """
  for spec in args:
    if type(spec) is int:
      pat = spec
      min = 1
      max = 10
    else:
      ls = len(spec)
      if ls == 2:
        pat, min, max = spec[0], spec[1], spec[1]
      elif ls == 3:
        pat, min, max = spec
      else:
        raise RuntimeError("invalid pattern specification")
    for n in range(min, max + 1):
      yield aut_pattern(pat, n)
%}
