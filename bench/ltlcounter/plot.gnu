set terminal postscript eps enhanced color
set ytics nomirror
set y2tics auto
set ylabel "states"
set y2label "ticks"
set key left top

set output 'results.fm.eps'

plot 'results.fm' using 1:($4+$5) '%lf,%lf,%lf,%lf,%*lf,%*lf,%lf,%*lf,%*lf' \
        with filledcurve x1 title "Total Time" axes x1y2, \
     'results.fm' using 1:4 '%lf,%lf,%lf,%lf,%*lf,%*lf,%lf,%*lf,%*lf' \
        with filledcurve x1 title "Translation Time" axes x1y2, \
     'results.fm' using 1:2 '%lf,%lf,%lf,%lf,%*lf,%*lf,%lf,%*lf,%*lf' \
        with lines title "States"


set output 'results.taa.eps'

plot 'results.taa' using 1:($4+$5) '%lf,%lf,%lf,%lf,%*lf,%*lf,%lf,%*lf,%*lf' \
        with filledcurve x1 title "Total Time" axes x1y2, \
     'results.taa' using 1:4 '%lf,%lf,%lf,%lf,%*lf,%*lf,%lf,%*lf,%*lf' \
        with filledcurve x1 title "Translation Time" axes x1y2, \
     'results.taa' using 1:2 '%lf,%lf,%lf,%lf,%*lf,%*lf,%lf,%*lf,%*lf' \
        with lines title "States"
