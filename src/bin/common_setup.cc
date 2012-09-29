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

#include "common_setup.hh"
#include "argp.h"

const char* argp_program_bug_address = "<" PACKAGE_BUGREPORT ">";

static void
display_version(FILE *stream, struct argp_state*)
{
  fputs(program_name, stream);
  fputs(" (" PACKAGE_STRING ")\n\
\n\
Copyright (C) 2012  Laboratoire de Recherche et Développement de l'Epita.\n\
This is free software; see the source for copying conditions.  There is NO\n\
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE,\n\
to the extent permitted by law.\n", stream);
}

void
setup(char** argv)
{
  // Simplify the program name, because argp() uses it to report
  // errors and display help text.
  set_program_name(argv[0]);
  argv[0] = const_cast<char*>(program_name);

  argp_program_version_hook = display_version;
}
