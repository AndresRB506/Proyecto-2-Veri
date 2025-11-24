// Recolector de métricas - recolecta estadísticas de rendimiento y latencia
package mesh_metrics_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;

  class metrics_collector extends uvm_subscriber #(mesh_uvm_pkg::hdr_t);
    `uvm_component_utils(metrics_collector)

    int unsigned rows    = 4;                    
    int unsigned colums  = 4;                   
    int unsigned PCKG_SZ = 40;                   // Tamaño del paquete en bits
    string       csv_path = "out/metrics.csv";   

    // Archivo de salida y estructuras de datos para métricas
    int fh;                          // Handle del archivo CSV
    longint pkt_cnt[int];           // Contador de paquetes por terminal 
    longint bytes_accum[int];       // Acumulador de bytes por terminal 
    longint first_time[int];        // Primer timestamp por terminal 
    longint last_time[int];         // Último timestamp por terminal 

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      void'(uvm_config_db#(int unsigned)::get(this, "", "ROWS",     rows));
      void'(uvm_config_db#(int unsigned)::get(this, "", "COLUMS",   colums));
      void'(uvm_config_db#(int unsigned)::get(this, "", "PCKG_SZ",  PCKG_SZ));
      void'(uvm_config_db#(string)::get(this, "", "CSV_PATH", csv_path));

      // Crear archivo CSV con encabezados
      fh = $fopen(csv_path, "w");
      $fdisplay(fh, "tx_time,rx_time,src_term,dst_term,latency,bytes");
    endfunction

    function void write(mesh_uvm_pkg::hdr_t h);
      // Calculan tiempos  y métricas
      longint rx_time = $time;
      longint tx_time = rx_time - 2;  // Se asume 2 ciclos de latencia
      
      int src_term = 0;                    
      int dst_term = 0;                   
      int bytes = (PCKG_SZ / 8);          // Convertiiendo bits a bytes
      longint latency = rx_time - tx_time; // Latencia calculada

      $fdisplay(fh, "%0d,%0d,%0d,%0d,%0d,%0d", 
                tx_time, rx_time, src_term, dst_term, latency, bytes);

      if (!pkt_cnt.exists(dst_term)) begin
        pkt_cnt[dst_term] = 0;
        bytes_accum[dst_term] = 0;
        first_time[dst_term] = 0;
        last_time[dst_term] = 0;
      end

      pkt_cnt[dst_term]++;
      bytes_accum[dst_term] += bytes;
      
      if (first_time[dst_term] == 0)
        first_time[dst_term] = rx_time;
      last_time[dst_term] = rx_time;
    endfunction

    // Reporte final de estadísticas
    function void report_phase(uvm_phase phase);
      for (int t = 0; t < rows*2 + colums*2; t++) begin
        if (pkt_cnt.exists(t) && pkt_cnt[t] > 0) begin
          longint duration = last_time[t] - first_time[t];
          real bw = (duration > 0) ? (bytes_accum[t] * 1.0 / duration) : 0.0;
          
          `uvm_info("METRICS", $sformatf(
            "term=%0d pkts=%0d bw_avg(bytes/cycle)=%0f", 
            t, pkt_cnt[t], bw
          ), UVM_LOW)
        end
      end

      if (fh) $fclose(fh);
    endfunction

  endclass

endpackage
