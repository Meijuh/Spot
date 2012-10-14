[NAME] ltlcheck \- translate LTL/PSL formulas into Büchi automata
[DESCRIPTION]
.\" Add any additional description here
[EXAMPLES]
The following commands compare never claims produced by ltl2tgba(1)
and spin(1) and 100 random formulas, using a timeout of 2 minutes.  A
trace of the execution of the two tools, including any potential issue
detected, is reported on standard error, while statistics gathered
(normally sent to standard output) are redicted to \f(CWresults.json\fR.

\f(CW% randltl -n100 --tree-size=20..30 a b c | \e
.br
ltlcheck -T120 'ltl2tgba -s %f > %N' 'spin -f %s > %N' > results.json\fR

The next command compare lbt, ltl3ba, and ltl2tgba(1) on a set of
formulas saved in file \f(CWinput.ltl\fR.  Statistis are again
redirected to \f(CWresults.json\fR.  Note the use of \f(CW%L\fR to
indicate that the LBT formula should be written into a file, and
\f(CW%T\fR to read the output in LBTT's format (which is a superset of
the format output by LBT).

\f(CW% ltlcheck -F input.ltl 'lbt < %L > %T' 'ltl2tgba --lbtt %f > %T'\fR

[SEE ALSO]
randltl(1), genltl(1), ltlfilt(1), ltl2tgba(1)

[BIBLIOGRAPHY]
ltlcheck is a Spot-based reimplementation of a tool called LBTT.  LBTT
was developped by Heikki Tauriainen at the Helsinki University of
Technology.  The main motivation for the reimplementation was to
support PSL, and output more statistics about the translation.

The sanity checks performed on the result of each translator (by
either LBTT or ltlcheck) are described in the following paper.  Our
implementation will detect and reports problems (like inconsistencies
between two translations) but unlike LBTT it does not offer an
interactive mode to investigate such problems.

.TP
th02
H. Tauriainen and K. Heljanko: Testing LTL formula translation into
Büchi automata.  Int. J. on Software Tools for Technology Transfer.
Volume 4, number 1, October 2002.
