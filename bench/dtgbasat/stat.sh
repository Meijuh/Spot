#!/bin/sh

ltlfilt=../../src/bin/ltlfilt
ltl2tgba=../../src/bin/ltl2tgba
dstar2tgba=../../src/bin/dstar2tgba
timeout='timeout -sKILL 2h'
stats=--stats="%s, %e, %t, %a, %c, %d, %p, %r"
empty='-, -, -, -, -, -, -, -'
tomany='!, !, !, !, !, !, !, !'
dbamin=${DBA_MINIMIZER-/home/adl/projs/dbaminimizer/minimize.py}

get_stats()
{
   $timeout "$@" "$stats" > stdin.$$ 2>stderr.$$
   if grep -q 'INT_MAX' stderr.$$; then
       # Too many SAT-clause?
       echo "$tomany"
   else
       tmp=`cat stdin.$$`
       echo ${tmp:-$empty}
   fi
   rm -f stdin.$$ stderr.$$
}

get_dbamin_stats()
{
    tmp=`./rundbamin.pl $timeout $dbamin "$@"`
    mye='-, -'
    echo ${tmp:-$mye}
}


f=$1
type=$2
accmax=$3

case $type in
    *WDBA*)
	echo "$f, $accmax, $type..." 1>&2
	input=`get_stats $ltl2tgba "$f" -BD`
	dba=$input
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA..." 1>&2
	mindba=`get_stats $ltl2tgba "$f" -BD -x 'sat-minimize=-1'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA..." 1>&2
	mindtgba=`get_stats $ltl2tgba "$f" -D -x 'sat-minimize=-1'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA, $mindtgba, minDTBA..." 1>&2
	mindtba=`get_stats $ltl2tgba "$f" -D -x 'sat-minimize=-1,sat-acc=1'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA, $mindtgba, minDTBA, $mindtba, dbaminimizer..." 1>&2
	$ltlfilt --remove-wm -f "$f" -l |
	ltl2dstar --ltl2nba=spin:$ltl2tgba@-sD - dra.$$
	dbamin=`get_dbamin_stats dra.$$`
	dra=`sed -n 's/States: \(.*\)/\1/p' dra.$$`
	rm dra.$$
	;;
    *TCONG*|*trad*)  # Not in WDBA
	echo "$f, $accmax, $type..." 1>&2
	input=`get_stats $ltl2tgba "$f" -D -x '!wdba-minimize,tba-det'`
	echo "$f, $accmax, $type, $input, DBA, ..." 1>&2
	dba=`get_stats $ltl2tgba "$f" -BD -x '!wdba-minimize,tba-det'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA..." 1>&2
	mindba=`get_stats $ltl2tgba "$f" -BD -x '!wdba-minimize,sat-minimize'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA..." 1>&2
	mindtgba=`get_stats $ltl2tgba "$f" -D -x '!wdba-minimize,sat-minimize'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA, $mindtgba, minDTBA..." 1>&2
	mindtba=`get_stats $ltl2tgba "$f" -D -x '!wdba-minimize,sat-minimize,sat-acc=1'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA, $mindtgba, minDTBA, $mindtba, dbaminimizer..." 1>&2
	case $type in
	    *TCONG*)   dbamin="n/a, n/a"  dra="n/a";;
            *trad*)
	       $ltlfilt --remove-wm -f "$f" -l |
	       ltl2dstar --ltl2nba=spin:$ltl2tgba@-sD - dra.$$
	       dbamin=`get_dbamin_stats dra.$$`
	       dra=`sed -n 's/States: \(.*\)/\1/p' dra.$$`
	       rm dra.$$
	       ;;
	esac
	;;
    *DRA*)
	echo "$f, $accmax, $type... " 1>&2
	$ltlfilt --remove-wm -f "$f" -l |
	ltl2dstar --ltl2nba=spin:$ltl2tgba@-sD - dra.$$
	input=`get_stats $dstar2tgba dra.$$ -D -x '!wdba-minimize'`
	echo "$f, $accmax, $type, $input, DBA, ... " 1>&2
	dba=`get_stats $dstar2tgba dra.$$ -BD -x '!wdba-minimize'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA... " 1>&2
	mindba=`get_stats $dstar2tgba dra.$$ -BD -x '!wdba-minimize,sat-minimize'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA..." 1>&2
	mindtgba=`get_stats $dstar2tgba dra.$$ -D -x '!wdba-minimize,sat-acc='$accmax`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA, $mindtgba, minDTBA..." 1>&2
	mindtba=`get_stats $dstar2tgba dra.$$ -D -x '!wdba-minimize,sat-acc=1'`
	echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA, $mindtgba, minDTBA, $mindtba, dbaminimizer..." 1>&2
	dbamin=`get_dbamin_stats dra.$$`
	dra=`sed -n 's/States: \(.*\)/\1/p' dra.$$`
	rm -f dra.$$
	;;
    *not*)
	exit 0
	;;
    *)
	echo "SHOULD NOT HAPPEND"
	exit 2
	;;
esac
echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA, $mindtgba, minDTBA, $mindtba, dbaminimizer, $dbamin, DRA, $dra" 1>&2
echo "$f, $accmax, $type, $input, DBA, $dba, minDBA, $mindba, minDTGBA, $mindtgba, minDTBA, $mindtba, dbaminimizer, $dbamin, DRA, $dra"
