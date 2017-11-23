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

SUBDIRS = tl

DOXYGEN = doxygen
if ENABLE_DOXYGEN
  DOXY_STAMP = stamp
endif

all-local: $(DOXY_STAMP) $(srcdir)/org-stamp

.PHONY: doc
doc:
	-rm -f stamp
	$(MAKE) stamp

stamp: $(srcdir)/Doxyfile.in $(top_srcdir)/configure.ac
	$(MAKE) Doxyfile
	-rm -rf spot.html spot.latex
	$(DOXYGEN)
	touch $@

spot.html spot.tag: stamp

DISTCLEANFILES = spot.tag spot.html stamp

.PHONY: org org-man
org:
	cd $(top_builddir) && $(MAKE) doc/org/init.el
	rm -rf $(srcdir)/userdoc $(builddir)/org/org.errors
	$(MAKE) org-man org/plantuml.jar
	$(EMACS) --batch -Q -l org/init.el
	if test -s $(builddir)/org/org.errors; then \
	  cat $(builddir)/org/org.errors; exit 1; \
        else :; fi

org/plantuml.jar:
	wget http://downloads.sourceforge.net/project/plantuml/plantuml.jar -O org/plantuml.jar || curl http://downloads.sourceforge.net/project/plantuml/plantuml.jar -o org/plantuml.jar

org-man:
	mkdir -p $(srcdir)/userdoc/man
	$(top_srcdir)/tools/man2html.pl $(top_srcdir)/bin/man $(srcdir)/userdoc/man

ORG_FILES = \
  org/.dir-locals.el.in \
  org/g++wrap.in \
  org/init.el.in \
  org/spot.css \
  org/arch.tex \
  $(srcdir)/org/arch.svg \
  org/autcross.org \
  org/autfilt.org \
  org/csv.org \
  org/citing.org \
  org/compile.org \
  org/concepts.org \
  org/dstar2tgba.org \
  org/genaut.org \
  org/genltl.org \
  org/hoa.org \
  org/hierarchy.org \
  org/hierarchy.tex \
  $(srcdir)/org/hierarchy.svg \
  org/index.org \
  org/install.org \
  org/ioltl.org \
  org/ltl2tgba.org \
  org/ltl2tgta.org \
  org/ltlcross.org \
  org/ltldo.org \
  org/ltlfilt.org \
  org/ltlgrind.org \
  org/ltlsynt.org \
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
  org/tut11.org \
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
  $(srcdir)/org/satmin.svg

$(srcdir)/org/satmin.svg: org/satmin.tex
	cd $(srcdir)/org && \
	pdflatex satmin.tex && \
	pdf2svg satmin.pdf satmin.svg && \
	rm -f satmin.pdf satmin.aux satmin.log

$(srcdir)/org/arch.svg: org/arch.tex
	cd $(srcdir)/org && \
	pdflatex arch.tex && \
	pdf2svg arch.pdf arch.svg && \
	rm -f arch.pdf arch.aux arch.log

$(srcdir)/org/hierarchy.svg: org/hierarchy.tex
	cd $(srcdir)/org && \
	pdflatex hierarchy.tex && \
	pdf2svg hierarchy.pdf hierarchy.svg && \
	rm -f hierarchy.pdf hierarchy.aux hierarchy.log

$(srcdir)/org-stamp: $(ORG_FILES) $(configure_ac)
	$(MAKE) org && touch $@

$(srcdir)/userdoc: $(srcdir)/org-stamp

EXTRA_DIST = \
  footer.html \
  mainpage.dox \
  $(ORG_FILES) \
  $(srcdir)/org-stamp \
  $(srcdir)/userdoc

DISTCLEANFILES = org/plantuml.jar
