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
