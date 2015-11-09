.\" -*- coding: utf-8 -*-
[NAME]
autfilt \- filter, convert, and transform omega-automata
[DESCRIPTION]
.\" Add any additional description here
[BIBLIOGRAPHY]
The following papers are related to some of the transformations implemented
in autfilt.

.TP
\(bu
Etienne Renault, Alexandre Duret-Lutz, Fabrice Kordon, and Denis Poitrenaud:
Strength-based decomposition of the property Büchi automaton for faster
model checking. Proceedings of TACAS'13. LNCS 7795.

The \fB\-\-strength\-decompose\fR option implements the definitions
given in the above paper.
.TP
\(bu
František Blahoudek, Alexandre Duret-Lutz, Vojtčech Rujbr, and Jan Strejček:
On refinement of Büchi automata for explicit model checking.
Proceedings of SPIN'15.  LNCS 9232.

That paper gives the motivation for options \fB\-\-exclusive\-ap\fR
and \fB\-\-simplify\-exclusive\-ap\fR.

[SEE ALSO]
.BR spot-x (7)
.BR dstar2tgba (1)
