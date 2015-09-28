// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2013, 2014, 2015 Laboratoire de Recherche et
// Developpement de l'Epita (LRDE)
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

#pragma once

#include "kripke/kripke.hh"
#include "tl/apcollect.hh"

namespace spot
{

  // \brief Load an ltsmin model, either from divine or promela.
  //
  // The filename given can be either a *.pm/*.pml/*.prom promela
  // source or a *.spins dynamic library compiled with "spins file".
  // If a promela source is supplied, this function will call spins to
  // update the *.spins library only if it is not newer.
  //
  // Similarly the divine models can be specified as *.dve source or
  // *.dve or *.dve2C libraries.
  //
  // The dead parameter is used to control the behavior of the model
  // on dead states (i.e. the final states of finite sequences).
  // If DEAD is "false", it means we are not
  // interested in finite sequences of the system, and dead state
  // will have no successor.  If DEAD is
  // "true", we want to check finite sequences as well as infinite
  // sequences, but do not need to distinguish them.  In that case
  // dead state will have a loop labeled by true.  If DEAD is any
  // other string, this is the name a property that should be true
  // when looping on a dead state, and false otherwise.
  //
  // This function returns 0 on error.
  //
  // \a file the name of the *.prom source file or the dynamic library
  // \a to_observe the list of atomic propositions that should be observed
  //               in the model
  // \a dict the BDD dictionary to use
  // \a dead an atomic proposition or constant to use for looping on
  //         dead states
  // \a verbose whether to output verbose messages
  SPOT_API kripke_ptr
  load_ltsmin(const std::string& file, const bdd_dict_ptr& dict,
	      const atomic_prop_set* to_observe,
	      formula dead = formula::tt(),
	      int compress = 0, bool verbose = true);
}
