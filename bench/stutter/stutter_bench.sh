#!/bin/sh

RANDLTL=../../src/bin/randltl
LTLFILT=../../src/bin/ltlfilt

OUTPUT=bench_formulas.csv
echo 'formula,algo,ap,states,result,time' > "$OUTPUT"
for ap in 1 2 3 4; do
  echo "Generating benchmarks for formulas with $ap atomic propositions..."
  $RANDLTL $ap --tree-size=..30 -n 20000 | $LTLFILT --ap=$ap |
  ./stutter_invariance_formulas -F- >> "$OUTPUT"
done

echo "Generating benchmarks for random graphs..."
OUTPUT=bench_randgraph.csv
echo 'algo,ap,states,result,time' > "$OUTPUT"
./stutter_invariance_randomgraph >> "$OUTPUT"
