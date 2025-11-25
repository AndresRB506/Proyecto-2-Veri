set datafile separator comma
set term png size 1200,800
set output "latency_plot.png"  # ← Nombre de archivo específico
set title "Latencia por paquete"
set xlabel "Paquete"
set ylabel "Latencia (ciclos)"

plot "cm_out/metrics.csv" using 1:2 with lines title "Latencia"
