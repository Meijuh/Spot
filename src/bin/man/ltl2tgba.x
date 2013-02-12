[NAME]
ltl2tgba \- translate LTL/PSL formulas into Büchi automata
[DESCRIPTION]
.\" Add any additional description here
[FINE-TUNING OPTIONS]

The \fB\-\-extra\-options\fR argument is a comma-separated list of
\fIKEY\fR=\fIINT\fR assignments that are passed to the post-processing
routines (they may be passed to other algorithms in the future).
These options are mostly used for benchmarking and debugging
purpose.  \fIKEY\fR (without any value) is a
shorthand for \fIKEY\fR=1, and !\fIKEY\fR is a shorthand for
\fIKEY\fR=0.

Supported options are:
.TP
\fBdegen\-reset\fR
If non-zero (the default), the degeneralization algorithm will reset
its level any time it exits a non-accepting SCC.
.TP
\fBdegen\-lcache\fR
If non-zero (the default), whenever the degeneralization algorithm enters
an SCC on a state that has already been associated to a level elsewhere,
it should reuse that level.  The "lcache" stands for "level cache".
.TP
\fBdegen\-order\fR
If non-zero, the degeneralization algorithm will compute one degeneralization
order for each SCC it processes.  This is currently disabled by default.
.TP
\fBsimul\fR
Set to 0 to disable simulation-based reductions.  Set to 1 to use only
direct simulation.  Set to 2 to use only reverse simulation.  Set to 3
to iterate both direct and reverse simulations.  Set to 4 to apply
only "don't care" direct simulation.  Set to 5 to iterate "don't care"
direct simulation and reverse simulation.  The default is 3, except
when option \fB\-\-low\fR is specified, in which case the default is
1.
.TP
\fBsimul-limit\fR
Can be set to a positive integer to cap the number of "don't care"
transitions considered by the "don't care"-simulation algorithm.  A
negative value (the default) does not enforce any limit.  Note that if
there are \fIN\fR "don't care" transitions, the algorithm may
potentially test 2^\fIN\fR configurations.
