// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include "common_sys.hh"
#include "twaalgos/postproc.hh"
#include <argp.h>

extern const struct argp post_argp;	     // postprocessing enabled
extern const struct argp post_argp_disabled; // postprocessing disabled

extern spot::postprocessor::output_type type;
extern spot::postprocessor::output_pref pref;
extern spot::postprocessor::output_pref comp;
extern spot::postprocessor::optimization_level level;
