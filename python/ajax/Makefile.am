## -*- coding: utf-8 -*-
## Copyright (C) 2011, 2012, 2015, 2016 Laboratoire de Recherche et
## Développement de l'Epita (LRDE).
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

nodist_noinst_SCRIPTS = spotcgi.py
EXTRA_DIST = $(srcdir)/spotcgi.in README trans.html css/trans.css	\
  css/tipTip.css js/jquery.tipTip.minified.js js/jquery.ba-bbq.min.js	\
  js/jquery.ba-dotimeout.min.js logos/spot64s.png logos/mail.png	\
  css/loading.gif protocol.txt

CLEANFILES = $(nodist_noinst_SCRIPTS)

spotcgi.py: $(srcdir)/spotcgi.in Makefile
	sed -e 's|[@]PYTHON[@]|@PYTHON@|g' \
	    -e 's|[@]pythondir[@]|@pythondir@|g' \
	    -e 's|[@]srcdir[@]|@srcdir@|g' \
	    -e 's|[@]top_builddir[@]|@top_builddir@|g' \
	    -e 's|[@]PACKAGE_VERSION[@]|@PACKAGE_VERSION@|g' \
	    -e 's|[@]DOT[@]|@DOT@|g' \
	    -e 's|[@]LTL3BA[@]|@LTL3BA@|g' \
	    <$(srcdir)/spotcgi.in >spotcgi.tmp
	chmod +x spotcgi.tmp
	mv -f spotcgi.tmp $@

clean-local:
	rm -rf spotimg
