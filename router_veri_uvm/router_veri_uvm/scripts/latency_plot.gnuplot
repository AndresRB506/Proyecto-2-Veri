set datafile separator comma
set term png size 1200,800
set output out
set title "Latencia por paquete"
set xlabel "Paquete"
set ylabel "Latencia (ciclos)"
plot csv using 0:5 with linespoints title "latency"
