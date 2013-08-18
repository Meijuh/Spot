[NAME]
ltlcross \- cross-compare LTL/PSL translators to Büchi automata
[DESCRIPTION]
.\" Add any additional description here
[EXAMPLES]
The following commands compare never claims produced by ltl2tgba(1)
and spin(1) and 100 random formulas, using a timeout of 2 minutes.  A
trace of the execution of the two tools, including any potential issue
detected, is reported on standard error, while statistics are
written to \f(CWresults.json\fR.

.nf
% randltl \-n100 \-\-tree\-size=20..30 a b c | \e
ltlcross \-T120 'ltl2tgba \-s %f >%N' 'spin \-f %s >%N' \-\-json=results.json
.fi
.LP

The next command compares lbt, ltl3ba, and ltl2tgba(1) on a set of
formulas saved in file \f(CWinput.ltl\fR.  Statistics are again writen
as CSV into \f(CWresults.csv\fR.  Note the use of \f(CW%L\fR to
indicate that the formula passed to lbt should be written into a file
in LBT's format, and \f(CW%T\fR to read the output in LBTT's format
(which is a superset of the format output by LBT).

.nf
% ltlcross \-F input.ltl \-\-csv=results.csv \e
           'lbt <%L >%T' \e
           'ltl3ba \-f %s >%N' \e
           'ltl2tgba \-\-lbtt %f >%T'
.fi
.LP

Rabin or Streett automata output by ltl2dstar can be read from a
file specified with \f(CW%D\fR.  For instance:

.nf
% ltlcross \-F input.ltl \e
  'ltl2dstar \-\-ltl2nba=spin:path/ltl2tgba@\-s %L %D' \e
  'ltl2dstar \-\-automata=streett \-\-ltl2nba=spin:path/ltl2tgba@\-s %L %D' \e
.fi
.LP

However because Spot only supports Büchi acceptance, these Rabin and
Streett automata are immediately converted to TGBA before further
processing by ltlcross.  This is still interesting to search for bugs
in translators to Rabin or Streett automata, but the statistics might
not be very relevant.

If you use ltlcross in an automated testsuite just to check for
potential problems, avoid the \fB\-\-csv\fR and \fB\-\-json\fR
options: ltlcross is faster when it does not have to compute these
statistics.

[ENVIRONMENT VARIABLES]

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


[SEE ALSO]
.BR randltl (1),
.BR genltl (1),
.BR ltlfilt (1),
.BR ltl2tgba (1)

[BIBLIOGRAPHY]
ltlcross is a Spot-based reimplementation of a tool called LBTT.  LBTT
was developped by Heikki Tauriainen at the Helsinki University of
Technology.  The main motivation for the reimplementation was to
support PSL, and output more statistics about the translations.

The sanity checks performed on the result of each translator (by
either LBTT or ltlcross) are described in the following paper.

.TP
th02
H. Tauriainen and K. Heljanko: Testing LTL formula translation into
Büchi automata.  Int. J. on Software Tools for Technology Transfer.
Volume 4, number 1, October 2002.

LBTT did not implement Test 2 described in this paper.  ltlcross
implements a slight variation: when an automaton produced by some
translator is deterministic, its complement is built and used for
additional cross-comparisons with other tools.  If the translation P1
of the positive formula and the translation N1 of the negative formula
both yield deterministic automata (this may only happen for obligation
properties) then the emptiness check of Comp(P1)*Comp(N1) is
equivalent to Test 2 of Tauriainen and Heljanko.  If only one
automaton is deterministic, say P1, it can still be used to check we
can be used to check the result of another translators, for instance
checking the emptiness of Comp(P1)*P2.

Our implementation will detect and reports problems (like
inconsistencies between two translations) but unlike LBTT it does not
offer an interactive mode to investigate such problems.


