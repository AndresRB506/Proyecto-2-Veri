set datafile separator comma
set term png size 1200,800
set output out
set title "Ancho de banda promedio por terminal"
set xlabel "Tiempo"
set ylabel "BW (bytes/ciclo)"

plot csv using 0:5 with lines title "bw proxy"
