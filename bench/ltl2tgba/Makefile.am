EXTRA_DIST = \
  algorithms \
  big \
  formulae.ltl \
  known \
  small \
  sum.py

OUTPUTS = known small big
OUTCSV = $(OUTPUTS:=.csv)
OUTJSON = $(OUTPUTS:=.json)
OUTLOG = $(OUTPUTS:=.log)

CLEANFILES = $(OUTCSV) $(OUTJSON) $(OUTLOG) \
             results.pdf results.aux results.log results.tex

.PHONY = run

run: $(OUTJSON)

deps = $(srcdir)/algorithms \
       $(top_srcdir)/configure.ac \
       $(top_builddir)/src/bin/ltl2tgba

small.json: $(srcdir)/small $(deps)
	$(srcdir)/small
big.json: $(srcdir)/big $(deps)
	$(srcdir)/big
known.json: $(srcdir)/known $(srcdir)/formulae.ltl $(deps)
	$(srcdir)/known

results.tex: $(srcdir)/sum.py $(OUTJSON)
	v=`git describe --always --dirty 2>/dev/null || \
	  echo $(PACKAGE_STRING)`; \
	$(srcdir)/sum.py $(OUTJSON) >$(@:.tex=.tmp) \
	  --intro "Results assembled on `LANG=C date` with $$v."; \
	mv $(@:.tex=.tmp) $@

results.pdf: results.tex
	pdflatex results.tex
