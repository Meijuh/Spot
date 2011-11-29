## Copyright (C) 2011 Laboratoire de Recherche et Développement de
## l'Epita (LRDE).
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


all: $(srcdir)/tl.pdf
LATEXMK = latexmk -pdf -ps- -dvi- -e '$$bibtex_use=2' \
          -pdflatex='pdflatex %O "\def\SpotVersion{$(VERSION)}\input{%S}"'

dist_pdf_DATA = $(srcdir)/tl.pdf

$(srcdir)/tl.pdf: $(srcdir)/tl.tex $(srcdir)/tl.bib
	$(LATEXMK) $(srcdir)/tl.tex
	test '$(srcdir)' = '.' || cp $@ $(srcdir)/$@

pvc:
	$(LATEXMK) -pvc $(srcdir)/tl.tex

.PHONY: mostlyclean-local pvc
mostlyclean-local:
	$(LATEXMK) -c $(srcdir)/tl.tex
