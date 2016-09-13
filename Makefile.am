## -*- coding: utf-8 -*-
## Copyright (C) 2011, 2012, 2013, 2014, 2015, 2016 Laboratoire de
## Recherche et Développement de l'Epita (LRDE).
## Copyright (C) 2003, 2005  Laboratoire d'Informatique de Paris 6 (LIP6),
## département Systèmes Répartis Coopératifs (SRC), Université Pierre
## et Marie Curie.
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

if NEVER
  # For Automake a, conditional directory
  # is conditionally built, but unconditionally distributed.
  # So using NEVER here ensures that `make all' will not
  # recurse in bench/, but `make dist' will.
  NEVER_SUBDIRS = bench elisp
endif

if USE_PYTHON
  PYTHON_SUBDIR = python
endif

SUBDIRS = picosat buddy lib ltdl spot bin tests $(PYTHON_SUBDIR) doc \
					$(NEVER_SUBDIRS)

UTF8 = utf8/doc/ReleaseNotes utf8/doc/utf8cpp.html utf8/utf8.h	\
  utf8/utf8/checked.h utf8/utf8/core.h utf8/utf8/unchecked.h

DEBIAN =					\
  debian/changelog				\
  debian/changelog.in				\
  debian/compat					\
  debian/control				\
  debian/copyright				\
  debian/docs					\
  debian/libbddx0.install			\
  debian/libbddx-dev.install			\
  debian/libspot0.install			\
  debian/libspotltsmin0.install			\
  debian/libspot-dev.install			\
  debian/python3-spot.examples			\
  debian/python3-spot.install			\
  debian/rules					\
  debian/source/format				\
  debian/source/lintian-overrides		\
  debian/spot-doc.doc-base			\
  debian/spot-doc.docs				\
  debian/spot-doc.install			\
  debian/spot.install

debian/changelog: configure.ac
	$(top_builddir)/config.status --file debian/changelog

EXTRA_DIST = HACKING ChangeLog.1 tools/gitlog-to-changelog	\
	     tools/help2man tools/man2html.pl			\
	     tools/test-driver-teamcity $(UTF8) $(DEBIAN)	\
	     m4/gnulib-cache.m4 .dir-locals.el

dist-hook: gen-ChangeLog

gen_start = 2012-03-10
.PHONY: gen-ChangeLog deb
gen-ChangeLog:
	if test -d .git; then						\
## Generate all commits in the form "SHA1 subject"
	  git log --since=$(gen_start) --pretty=oneline |		\
## Filter out commits whose subject start with '['.  These are usually
## [buddy] or [lbtt] tags to indicate we are committing on a subproject.
            grep -v '........................................ \[' |	\
## Keep the SHA1
	    cut -c 1-40 |						\
## Feed all that to gitlog-to-changelog
            $(top_srcdir)/tools/gitlog-to-changelog			\
	      --no-cluster --format='%s%n%n%b%n' --			\
              --stdin --no-walk > $(distdir)/cl-t;			\
          rm -f $(distdir)/ChangeLog;					\
          mv $(distdir)/cl-t $(distdir)/ChangeLog;			\
	fi

# Build Debian packages.
# Run it with:  make DEBUILDFLAGS=-j8 deb -j8
deb: dist
	rm -rf spot-$(VERSION) spot-$(VERSION)$(GITPATCH)
	tar zxvf spot-$(VERSION).tar.gz
	mv spot-$(VERSION) spot-$(VERSION)$(GITPATCH)
	tar Jcvf spot_$(VERSION)$(GITPATCH).orig.tar.xz \
	         spot-$(VERSION)$(GITPATCH)
	cd spot-$(VERSION)$(GITPATCH) && debuild $(DEBUILDFLAGS) -us -uc
