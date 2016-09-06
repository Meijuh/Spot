[NAME]
spot-x \- Common fine-tuning options and environment variables.

[SYNOPSIS]
.B \-\-extra-options STRING
.br
.B \-x STRING

[DESCRIPTION]
.\" Add any additional description here

[ENVIRONMENT VARIABLES]

.TP
\fBSPOT_DEFAULT_FORMAT\fR
Set to a value of \fBdot\fR or \fBhoa\fR to override the default
format used to output automata.  Up to Spot 1.9.6 the default output
format for automata used to be \fBdot\fR.  Starting with Spot 1.9.7,
the default output format switched to \fBhoa\fR as it is more
convenient when chaining tools in a pipe.  Set this variable to
\fBdot\fR to get the old behavior.  Additional options may be
passed to the printer by suffixing the output format with
\fB=\fR and the options.  For instance running
.in +4n
.nf
.ft C
% SPOT_DEFAULT_FORMAT=dot=bar autfilt ...
.fi
.in -4n
is the same as running
.in +4n
.nf
.ft C
% autfilt --dot=bar ...
.fi
.in -4n
but the use of the environment variable makes more sense if you set
it up once for many commands.

.TP
\fBSPOT_DOTDEFAULT\fR
Whenever the \f(CW--dot\fR option is used without argument (even
implicitely via \fBSPOT_DEFAULT_FORMAT\fR), the contents of this
variable is used as default argument.  If you have some default
settings in \fBSPOT_DOTDEFAULT\fR and want to append to options
\f(CWxyz\fR temporarily for one call, use \f(CW--dot=.xyz\fR:
the dot character will be replaced by the contents of the
\f(CWSPOT_DOTDEFAULT\fR environment variable.

.TP
\fBSPOT_DOTEXTRA\fR
The contents of this variable is added to any dot output, immediately
before the first state is output.  This makes it easy to override
global attributes of the graph.

.TP
\fBSPOT_SATLOG\fR
If set to a filename, the SAT-based minimization routines will append
statistics about each iteration to the named file.  Each line lists
the following comma-separated values: requested number of states,
number of reachable states in the output, number of edges in the
output, number of transitions in the output, number of variables in
the SAT problem, number of clauses in the SAT problem, user time for
encoding the SAT problem, system time for encoding the SAT problem,
user time for solving the SAT problem, system time for solving the SAT
problem.

.TP
\fBSPOT_SATSOLVER\fR
If set, this variable should indicate how to call a SAT\-solver.  This
is used by the sat\-minimize option described above.  The default
value is \f(CW"glucose -verb=0 -model %I >%O"\fR, it is correct for
glucose version 3.0 (for older versions, remove the \fCW(-model\fR
option).  The escape sequences \f(CW%I\fR and \f(CW%O\fR respectively
denote the names of the input and output files.  These temporary files
are created in the directory specified by \fBSPOT_TMPDIR\fR or
\fBTMPDIR\fR (see below).  The SAT-solver should follow the convention
of the SAT Competition for its input and output format.

.TP
\fBSPOT_STREETT_CONV_MIN\fR
The number of Streett pairs above which conversion from Streett
acceptance to generalized-Büchi acceptance should be made with a
dedicated algorithm.  By default this is 3, i.e., if a Streett
automaton with 3 acceptance pairs or more has to be converted into
generalized-Büchi, the dedicated algorithm is used.  This algorithm is
close to the classical conversion from Streett to Büchi, but with
several tweaks.  When this algorithm is not used, the standard
"Fin-removal" approach is used instead: first the acceptance condition
is converted into disjunctive normal form (DNF), then Fin acceptance
is removed like for Rabin automata, yielding a disjuction of
generalized Büchi acceptance, and the result is finally converted into
conjunctive normal form (CNF) to obtain a generalized Büchi
acceptance.  Both algorithms have a worst-case size that is
exponential in the number of Streett pairs, but in practice the
dedicated algorithm works better for most Streett automata with 3 or
more pairs (and many 2-pair Streett automata as well, but the
difference here is less clear).  Setting this variable to 0 will
disable the dedicated algorithm.  Setting it to 1 will enable it for
all Streett automata, however we do not recommand setting it to less
than 2, because the "Fin-removal" approach is better for single-pair
Streett automata.

.TP
\fBSPOT_TMPDIR\fR, \fBTMPDIR\fR
These variables control in which directory temporary files (e.g.,
those who contain the input and output when interfacing with
translators) are created.  \fBTMPDIR\fR is only read if
\fBSPOT_TMPDIR\fR does not exist.  If none of these environment
variables exist, or if their value is empty, files are created in the
current directory.

.TP
\fBSPOT_TMPKEEP\fR
When this variable is defined, temporary files are not removed.
This is mostly useful for debugging.

[BIBLIOGRAPHY]
.TP
1.
Christian Dax, Jochen Eisinger, Felix Klaedtke: Mechanizing the
Powerset Construction for Restricted Classes of
ω-Automata. Proceedings of ATVA'07.  LNCS 4762.

Describes the WDBA-minimization algorithm implemented in Spot.  The
algorithm used for the tba-det options is also a generalization (to
TBA instead of BA) of what they describe in sections 3.2 and 3.3.

.TP
2.
Tomáš Babiak, Thomas Badie, Alexandre Duret-Lutz, Mojmír Křetínský,
Jan Strejček: Compositional Approach to Suspension and Other
Improvements to LTL Translation.  Proceedings of SPIN'13.  LNCS 7976.

Describes the compositional suspension, the simulation-based
reductions, and the SCC-based simplifications.

.TP
3.
Rüdiger Ehlers: Minimising Deterministic Büchi Automata Precisely using
SAT Solving.  Proceedings of SAT'10.  LNCS 6175.

Our SAT-based minimization procedures are generalizations of this
paper to deal with TBA or TGBA.

[SEE ALSO]
.BR ltl2tgba (1)
.BR ltl2tgta (1)
.BR dstar2tgba (1)
.BR autfilt (1)
