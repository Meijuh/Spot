## -*- coding: utf-8 -*-
## Copyright (C) 2012 Laboratoire de Recherche et Développement
## de l'Epita (LRDE).
##
## This file is part of Spot, a model checking library.
##
## Spot is free software; you can redistribute it and/or modify it
## under the terms of the GNU General Public License as published by
## the Free Software Foundation; either version 2 of the License, or
## (at your option) any later version.
##
## Spot is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
## or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
## License for more details.
##
## You should have received a copy of the GNU General Public License
## along with Spot; see the file COPYING.  If not, write to the Free
## Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
## 02111-1307, USA.

common_dep = $(top_builddir)/configure.ac
x_to_1 = $(top_builddir)/tools/x-to-1
convman = ARGP_HELP_FMT=header-col=0 $(SHELL) "$(x_to_1)" \
          "$(PERL)" "$(top_srcdir)/tools/help2man -N -L 'en_US.UTF-8'"

dist_man1_MANS = ltlfilt.1 genltl.1 randltl.1 ltl2tgba.1
MAINTAINERCLEANFILES = $(dist_man1_MANS)
EXTRA_DIST = $(dist_man1_MANS:.1=.x)

ltl2tgba.1: $(common_dep) $(srcdir)/ltl2tgba.x $(srcdir)/../ltl2tgba.cc
	$(convman) ../ltl2tgba$(EXEEXT) $(srcdir)/ltl2tgba.x $@

ltlfilt.1: $(common_dep) $(srcdir)/ltlfilt.x $(srcdir)/../ltlfilt.cc
	$(convman) ../ltlfilt$(EXEEXT) $(srcdir)/ltlfilt.x $@

genltl.1: $(common_dep) $(srcdir)/genltl.x $(srcdir)/../genltl.cc
	$(convman) ../genltl$(EXEEXT) $(srcdir)/genltl.x $@

randltl.1: $(common_dep) $(srcdir)/randltl.x $(srcdir)/../randltl.cc
	$(convman) ../randltl$(EXEEXT) $(srcdir)/randltl.x $@
