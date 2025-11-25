set datafile separator comma
set term png size 1200,800
set output "BW_plot.png" 
set title "Ancho de banda promedio por terminal"
set xlabel "Tiempo"
set ylabel "BW (bytes/ciclo)"

plot "cm_out/metrics.csv" using 0:5 with lines title "bw proxy"
