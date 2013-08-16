[NAME]
dstar2tgba \- convert Rabin or Streett automata into Büchi automata
[BIBLIOGRAPHY]
.TP
1. 
<http://www.ltl2dstar.de/docs/ltl2dstar.html>

Documents the output format of ltl2dstar.

.TP
2.
Chistof Löding: Mehods for the Transformation of ω-Automata:
Complexity and Connection to Second Order Logic.  Diploma Thesis.
University of Kiel. 1998.

Describes various tranformations from non-deterministic Rabin and
Streett automata to Büchi automata.  Slightly optimized variants of
these transformations are used by dstar2tgba for the general cases.

.TP
3.
Sriram C. Krishnan, Anuj Puri, and Robert K. Brayton: Deterministic
ω-automata vis-a-vis Deterministic Büchi Automata.  ISAAC'94.

Explains how to preserve the determinism of Rabin and Streett automata
when the property can be repreted by a Deterministic automaton.
dstar2tgba implements this for the Rabin case only.  In other words,
translating a deterministic Rabin automaton with dstar2tgba will
produce a deterministic TGBA or BA if such a automaton exists.

[SEE ALSO]
.BR spot-x (7)
