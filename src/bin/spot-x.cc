// -*- coding: utf-8 -*-
// Copyright (C) 2013 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include "common_sys.hh"
#include <string>
#include <iostream>
#include <cstdlib>
#include <argp.h>
#include "common_setup.hh"

const char argp_program_doc[] ="\
Common fine-tuning options for binaries built with Spot.\n\
\n\
The argument of -x or --extra-options is a comma-separated list of KEY=INT \
assignments that are passed to the post-processing routines (they may \
be passed to other algorithms in the future). These options are \
mostly used for benchmarking and debugging purpose. KEYR (without any \
value) is a shorthand for KEY=1, while !KEY is a shorthand for KEY=0.";

#define DOC(NAME, TXT) NAME, 0, 0, OPTION_DOC | OPTION_NO_USAGE, TXT, 0

static const argp_option options[] =
  {
    { 0, 0, 0, 0, "Postprocessing options:", 0 },
    { DOC("scc-filter", "Set to 1 (the default) to enable \
SCC-pruning and acceptance simplification at the beginning of \
post-processing. Transitions that are outside of accepting SCC are \
removed from accepting sets, except those that enter into an accepting \
SCC. Set to 2 to remove even these entering transition from the \
accepting sets. Set to 0 to disable this SCC-pruning and acceptance \
simpification pass.") },
    { DOC("degen-reset", "If non-zero (the default), the \
degeneralization algorithm will reset its level any time it exits \
a non-accepting SCC.") },
    { DOC("degen-lcache", "If non-zero (the default), whenever the \
degeneralization algorithm enters an SCC on a state that has already \
been associated to a level elsewhere, it should reuse that level. \
The \"lcache\" stands for \"level cache\".") },
    { DOC("degen-order", "If non-zero, the degeneralization algorithm \
will compute one degeneralization order for each SCC it processes. \
This is currently disabled by default.") },
    { DOC("simul", "Set to 0 to disable simulation-based reductions. \
Set to 1 to use only direct simulation. Set to 2 to use only reverse \
simulation. Set to 3 to iterate both direct and reverse simulations. \
Set to 4 to apply only \"don't care\" direct simulation. Set to 5 to \
iterate \"don't care\" direct simulation and reverse simulation. The \
default is 3, except when option --low is specified, in which case the \
default is 1.") },
    { DOC("simul-limit", "Can be set to a positive integer to cap the \
number of \"don't care\" transitions considered by the \
\"don't care\"-simulation algorithm. A negative value (the default) \
does not enforce any limit. Note that if there are N \"don't care\" \
transitions, the algorithm may potentially test 2^N configurations.") },
    { DOC("ba-simul", "Set to 0 to disable simulation-based reductions \
on the Büchi automaton (i.e., after degeneralization has been performed). \
Set to 1 to use only direct simulation.  Set to 2 to use only reverse \
simulation.  Set to 3 to iterate both direct and reverse simulations.   \
The default is 3 in --high mode, and 0 otherwise.") },
    { 0, 0, 0, 0, 0, 0 }
  };

const struct argp_child children[] =
  {
    { &misc_argp_hidden, 0, 0, -1 },
    { 0, 0, 0, 0 }
  };

int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, 0, 0, argp_program_doc, children, 0, 0 };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, 0, 0))
    exit(err);

  std::cerr << "This binary serves no purpose other than generating"
	    << " the spot-x.7 manpage.\n";

  return 1;
}
