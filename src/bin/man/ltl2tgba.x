[NAME]
ltl2tgba \- translate LTL/PSL formulas into Büchi automata
[NOTE ON LBTT'S FORMAT]
The format, described at
http://www.tcs.hut.fi/Software/lbtt/doc/html/Format-for-automata.html,
has support for both transition-based and state based generalized acceptance.

Because Spot uses transition-based generalized Büchi automata
internally, it will normally use the transition-based flavor of that
format, indicated with a 't' flag after the number of acceptance sets.
For instance:

  % bin/ltl2tgba --lbtt 'GFp0 & GFp1 & FGp2'
  2 2t                   // 2 states, 2 transition-based acceptance sets
  0 1                    // state 0: initial
  0 -1 t                 //   trans. to state 0, no acc., label: true
  1 -1 | & p0 p2 & p1 p2 //   trans. to state 1, no acc., label: (p0&p2)|(p1&p2)
  -1                     // end of state 0
  1 0                    // state 1: not initial
  1 0 1 -1 & & p0 p1 p2  //   trans. to state 1, acc. 0 and 1, label: p0&p1&p2
  1 0 -1 & & p1 p2 ! p0  //   trans. to state 1, acc. 0, label: !p0&p1&p2
  1 1 -1 & & p0 p2 ! p1  //   trans. to state 1, acc. 1, label: p0&!p1&p2
  1 -1 & & p2 ! p0 ! p1  //   trans. to state 1, no acc., label: !p0&!p1&p2
  -1                     // end if state 1

Here, the two acceptance sets are represented by the numbers 0 and 1,
and they each contain two transitions (the first transition of state 1
belongs to both sets).

When both --ba and --lbtt options are used, the state-based flavor of
the format is used instead.  Note that the LBTT format supports
generalized acceptance conditions on states, but Spot only use this
format for Büchi automata, where there is always only one acceptance
set.  Unlike in the LBTT documentation, we do not use the
optional 's' flag to indicate the state-based acceptance, this way our
output is also compatible with that of LBT (see
http://www.tcs.hut.fi/Software/maria/tools/lbt/).

  % ltl2tgba --ba --lbtt FGp0
  2 1                 // 2 states, 1 (state-based) accepance set
  0 1 -1              // state 0: initial, non-accepting
  0 t                 //   trans. to state 0, label: true
  1 p0                //   trans. to state 1, label: p0
  -1                  // end of state 0
  1 0 0 -1            // state 1: not initial, in acceptance set 0
  1 p0                //   trans. to state 0, label: p0
  -1                  // end if state 1

You can force ltl2tgba to use the transition-based flavor of the
format even for Büchi automaton using --lbtt=t.

  % ltl2tgba --ba --lbtt=t FGp0
  2 1t                // 2 states, 1 transition-based accepance set.
  0 1                 // state 0: initial
  0 -1 t              //   trans. to state 0, no acc., label: true
  1 -1 p0             //   trans. to state 1, no acc., label: p0
  -1                  // end of state 0
  1 0                 // state 1: not initial
  1 0 -1 p0           //   trans. to state 1, acc. 0, label: p0
  -1                  // end if state 1

When representing a Büchi automaton using transition-based acceptance,
all transitions leaving accepting states are put into the acceptance set.

A final note concerns the name of the atomic propositions.  The
original LBTT and LBT formats require these atomic propositions to
have names such as 'p0', 'p32', ...  We extend the format to accept
atomic proposition with arbitrary names that do not conflict with
LBT's operators (e.g. 'i' is the symbol of the implication operator so
it may not be used as an atomic proposition), or as double-quoted
strings.  Spot will always output atomic-proposition that do not match
p[0-9]+ as double-quoted strings.

  % bin/ltl2tgba --lbtt 'GFa & GFb'
  1 2t
  0 1
  0 0 1 -1 & "a" "b"
  0 0 -1 & "b" ! "a"
  0 1 -1 & "a" ! "b"
  0 -1 & ! "b" ! "a"
  -1

[SEE ALSO]
.BR spot-x (7)
