## -*- coding: utf-8 -*-
## Copyright (C) 2010, 2011, 2013, 2014, 2015, 2016, 2017 Laboratoire de
## Recherche et Développement de l'Epita (LRDE).
## Copyright (C) 2003, 2004, 2005 Laboratoire d'Informatique de Paris
## 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
## Université Pierre et Marie Curie.
##
## This file is part of Spot, a model checking library.
##
## Spot is free software; you can redistribute it and/or modify it
## under the terms of the GNU General Public License as published by
## the Free Software Foundation; either version 3 of the License, or
## (at your option) any later version.
##
## Spot is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
## or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
## License for more details.
##
## You should have received a copy of the GNU General Public License
## along with this program.  If not, see <http://www.gnu.org/licenses/>.

DOXYGEN = doxygen

SUBDIRS = tl

.PHONY: doc fast-doc

all-local: $(srcdir)/stamp $(srcdir)/org-stamp

doc:
	-rm -f $(srcdir)/stamp
	$(MAKE) $(srcdir)/stamp

fast-doc:
	$(MAKE) Doxyfile
## Doxygen 1.8.x will easily segfault during the parallel runs of dot.
## 1.8.11 is supposed to be fixed, but until this version reaches all
## our build hosts, let's try to run doxygen a second time when the
## first attempt fails.
## https://bugzilla.gnome.org/show_bug.cgi?id=756241
	$(DOXYGEN) || $(DOXYGEN)
	touch $(srcdir)/stamp

$(srcdir)/stamp: $(srcdir)/Doxyfile.in $(top_srcdir)/configure.ac
	$(MAKE) Doxyfile dot
	-rm -rf spot.html spot.latex
	$(DOXYGEN)
	touch $@

$(srcdir)/spot.html $(srcdir)/spot.tag: $(srcdir)/stamp

# spot.tag is useful to third-party packages that must link to the
# Spot documentation.
dist_pkgdata_DATA = $(srcdir)/spot.tag

.PHONY: org org-man
org:
	cd $(top_builddir) && $(MAKE) doc/org/init.el
	rm -rf $(srcdir)/userdoc
	$(MAKE) org-man org/plantuml.jar
	$(EMACS) --batch -Q -l org/init.el

org/plantuml.jar:
	wget http://downloads.sourceforge.net/project/plantuml/plantuml.jar -O org/plantuml.jar

org-man:
	mkdir -p $(srcdir)/userdoc/man
	$(top_srcdir)/tools/man2html.pl $(top_srcdir)/bin/man $(srcdir)/userdoc/man

ORG_FILES = \
  org/.dir-locals.el.in \
  org/g++wrap.in \
  org/init.el.in \
  org/spot.css \
  org/arch.tex \
  $(srcdir)/org/arch.png \
  org/autfilt.org \
  org/csv.org \
  org/citing.org \
  org/compile.org \
  org/concepts.org \
  org/dstar2tgba.org \
  org/genltl.org \
  org/hoa.org \
  org/hierarchy.org \
  org/hierarchy.tex \
  $(srcdir)/org/hierarchy.png \
  org/index.org \
  org/install.org \
  org/ioltl.org \
  org/ltl2tgba.org \
  org/ltl2tgta.org \
  org/ltlcross.org \
  org/ltldo.org \
  org/ltlfilt.org \
  org/ltlgrind.org \
  org/oaut.org \
  org/randaut.org \
  org/randltl.org \
  org/tools.org \
  org/tut.org \
  org/tut01.org \
  org/tut02.org \
  org/tut03.org \
  org/tut04.org \
  org/tut10.org \
  org/tut20.org \
  org/tut21.org \
  org/tut22.org \
  org/tut23.org \
  org/tut24.org \
  org/tut30.org \
  org/tut31.org \
  org/tut50.org \
  org/tut51.org \
  org/upgrade2.org \
  org/satmin.org \
  org/satmin.tex \
  org/setup.org \
  $(srcdir)/org/satmin.png

$(srcdir)/org/satmin.png: org/satmin.tex
	cd $(srcdir)/org && \
	pdflatex -shell-escape satmin.tex && \
	rm -f satmin.pdf satmin.aux satmin.log

$(srcdir)/org/arch.png: org/arch.tex
	cd $(srcdir)/org && \
	pdflatex -shell-escape arch.tex && \
	rm -f arch.pdf arch.aux arch.log

$(srcdir)/org/hierarchy.png: org/hierarchy.tex
	cd $(srcdir)/org && \
	pdflatex -shell-escape hierarchy.tex && \
	rm -f hierarchy.pdf hierarchy.aux hierarchy.log

$(srcdir)/org-stamp: $(ORG_FILES) $(configure_ac)
	$(MAKE) org && touch $@

$(srcdir)/userdoc: $(srcdir)/org-stamp

EXTRA_DIST = \
  footer.html \
  mainpage.dox \
  $(srcdir)/stamp \
  $(srcdir)/spot.html \
  $(ORG_FILES) \
  $(srcdir)/org-stamp \
  $(srcdir)/userdoc

dist-hook: optipng
.PHONY: optipng
optipng:
	-(optipng -v >/dev/null) && optipng -o5 $(distdir)/userdoc/*.png

DISTCLEANFILES = org/plantuml.jar
