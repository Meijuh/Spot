#!/bin/sh

OUTPUT=bench_formulas.csv
RANDLTL=../../src/bin/randltl
LTLFILT=../../src/bin/ltlfilt

if test -f bench_formulas.csv; then
  echo -n "$OUTPUT already exists. [a]ppend, [r]emove it or [q]uit?"
  read ans
  if test "$ans" = "r"; then
    rm "$OUTPUT"
  else if test "$ans" = "q" -o "$ans" != "a"; then
    echo "abort."
    exit 0
  fi
  fi
fi

for ap in 1 2 3 4; do
  echo "Generating benchmarks for formulas with $ap atomic propositions..."
  $RANDLTL $ap --tree-size=..30 -n 20000 | $LTLFILT --ap=$ap |
  ./stutter_invariance_formulas -F- >> "$OUTPUT"
done
