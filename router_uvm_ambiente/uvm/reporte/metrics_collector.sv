// Recolector de métricas - recolecta estadísticas de rendimiento y latencia
package mesh_metrics_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;

  class metrics_collector extends uvm_subscriber #(mesh_uvm_pkg::hdr_t);
    `uvm_component_utils(metrics_collector)

    int unsigned rows    = 4;                    
    int unsigned columns  = 4;                   
    int unsigned PCKG_SZ = 40;                   // Tamaño del paquete en bits
    string       csv_path = "cm_out/metrics.csv";   

    // Archivo de salida y estructuras de datos para métricas
    int fh;                          // Handle del archivo CSV
    longint pkt_cnt[int];           // Contador de paquetes por terminal 
    longint bytes_accum[int];       // Acumulador de bytes por terminal 
    longint first_time[int];        // Primer timestamp por terminal 
    longint last_time[int];         // Último timestamp por terminal 
    
    // ✅ NUEVO: Tracking de timestamps por paquete para latencia real
    longint tx_timestamps[int][int]; // [src][tid] = tx_time
    longint total_latency[int];      // Latencia acumulada por terminal
    int latency_samples[int];        // Número de muestras de latencia

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      `uvm_info("METRICS", "Iniciando build_phase del metrics collector", UVM_LOW)
      
      void'(uvm_config_db#(int unsigned)::get(this, "", "ROWS",     rows));
      void'(uvm_config_db#(int unsigned)::get(this, "", "COLUMS",   columns));
      void'(uvm_config_db#(int unsigned)::get(this, "", "PCKG_SZ",  PCKG_SZ));
      void'(uvm_config_db#(string)::get(this, "", "CSV_PATH", csv_path));

      `uvm_info("METRICS", $sformatf("Configuración: rows=%0d, columns=%0d, PCKG_SZ=%0d", 
                rows, columns, PCKG_SZ), UVM_LOW)
      `uvm_info("METRICS", $sformatf("Archivo CSV: %s", csv_path), UVM_LOW)

      // Crear archivo CSV con encabezados mejorados
      fh = $fopen(csv_path, "w");
      if (fh == 0) begin
        `uvm_fatal("METRICS", $sformatf("No se pudo crear archivo CSV: %s", csv_path))
      end
      
      // ✅ Encabezados más descriptivos
      $fdisplay(fh, "tx_time,rx_time,src_term,dst_r,dst_c,tid,latency_cycles,bytes,mode,payload");
      `uvm_info("METRICS", "Archivo CSV creado con encabezados", UVM_LOW)
    endfunction

    function void write(mesh_uvm_pkg::hdr_t h);
      // ✅ TODAS las declaraciones de variables AL INICIO
      longint rx_time;
      int src_term;
      int dst_r;
      int dst_c;
      int tid;
      int mode;
      longint payload;
      int bytes;
      longint latency;
      longint tx_time;
      bit valid_latency;
      int dst_term;
      
      // ✅ AHORA las asignaciones
      rx_time = $time;
      
      // Extraer información real del header
      src_term = h.src;
      dst_r = h.dst_r;
      dst_c = h.dst_c;
      tid = h.tid;
      mode = h.mode;
      payload = h.payload;
      bytes = (PCKG_SZ / 8);
      
      // Inicializar variables
      latency = 0;
      tx_time = 0;
      valid_latency = 0;
      
      // Calcular latencia real si tenemos tx_time
      if (tx_timestamps.exists(src_term) && tx_timestamps[src_term].exists(tid)) begin
        tx_time = tx_timestamps[src_term][tid];
        latency = rx_time - tx_time;
        valid_latency = 1;
        
        // Limpiar entrada usada
        tx_timestamps[src_term].delete(tid);
        
        `uvm_info("METRICS", $sformatf("Latencia calculada: src=%0d, tid=%0d, latencia=%0d ciclos", 
                  src_term, tid, latency), UVM_HIGH)
      end else begin
        // Si no tenemos tx_time, usar estimación conservadora
        tx_time = rx_time - 10; // Estimación
        latency = 10;
        `uvm_warning("METRICS", $sformatf("No se encontró tx_time para src=%0d, tid=%0d. Usando estimación.", 
                     src_term, tid))
      end

      // Validación de latencia
      if (latency < 0) begin
        `uvm_warning("METRICS", $sformatf("Latencia negativa detectada: %0d. Corrigiendo a 0.", latency))
        latency = 0;
      end else if (latency > 10000) begin
        `uvm_warning("METRICS", $sformatf("Latencia muy alta: %0d ciclos", latency))
      end

      // Calcular terminal destino basado en posición
      dst_term = calculate_dst_terminal(dst_r, dst_c);

      // Escribir al CSV
      $fdisplay(fh, "%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0d,%0h", 
                tx_time, rx_time, src_term, dst_r, dst_c, tid, latency, bytes, mode, payload);

      // Acumular estadísticas mejoradas
      if (!pkt_cnt.exists(dst_term)) begin
        pkt_cnt[dst_term] = 0;
        bytes_accum[dst_term] = 0;
        first_time[dst_term] = 0;
        last_time[dst_term] = 0;
        total_latency[dst_term] = 0;
        latency_samples[dst_term] = 0;
      end

      pkt_cnt[dst_term]++;
      bytes_accum[dst_term] += bytes;
      
      if (valid_latency) begin
        total_latency[dst_term] += latency;
        latency_samples[dst_term]++;
      end
      
      if (first_time[dst_term] == 0)
        first_time[dst_term] = rx_time;
      last_time[dst_term] = rx_time;

      `uvm_info("METRICS", $sformatf("Paquete registrado: src=%0d->dst=(%0d,%0d), latencia=%0d", 
                src_term, dst_r, dst_c, latency), UVM_HIGH)
    endfunction
    
    // ✅ Función para registrar TX desde el driver
    function void record_tx(int src_term, int tid, longint tx_time);
      tx_timestamps[src_term][tid] = tx_time;
      `uvm_info("METRICS", $sformatf("TX registrado: src=%0d, tid=%0d, tiempo=%0d", src_term, tid, tx_time), UVM_HIGH)
    endfunction
    // ✅ Calcular terminal destino según topología
    function int calculate_dst_terminal(int dst_r, int dst_c);
      // Declaraciones al inicio
      int result;
      
      // Para mesh topology: terminal = row * columns + column
      if (dst_r >= 0 && dst_r < rows && dst_c >= 0 && dst_c < columns) begin
        result = dst_r * columns + dst_c;
      end else begin
        `uvm_warning("METRICS", $sformatf("Coordenadas destino inválidas: (%0d,%0d)", dst_r, dst_c))
        result = -1; // Terminal inválido
      end
      
      return result;
    endfunction

    // ✅ Reporte final mejorado
    function void report_phase(uvm_phase phase);
      // Declaraciones al inicio
      int total_packets;
      longint total_bytes;
      real total_bw;
      int t;
      longint duration;
      real bw;
      real avg_latency;
      
      super.report_phase(phase);
      
      `uvm_info("METRICS", "=== REPORTE FINAL DE MÉTRICAS ===", UVM_LOW)
      
      total_packets = 0;
      total_bytes = 0;
      total_bw = 0.0;
      
      for (t = 0; t < rows*2 + columns*2; t++) begin
        if (pkt_cnt.exists(t) && pkt_cnt[t] > 0) begin
          duration = last_time[t] - first_time[t];
          bw = (duration > 0) ? (bytes_accum[t] * 1.0 / duration) : 0.0;
          avg_latency = (latency_samples[t] > 0) ? 
                        (total_latency[t] * 1.0 / latency_samples[t]) : 0.0;
          
          `uvm_info("METRICS", $sformatf(
            "Terminal %0d: pkts=%0d, bytes=%0d, bw=%.3f bytes/cycle, latencia_avg=%.2f ciclos", 
            t, pkt_cnt[t], bytes_accum[t], bw, avg_latency
          ), UVM_LOW)
          
          total_packets += pkt_cnt[t];
          total_bytes += bytes_accum[t];
          total_bw += bw;
        end
      end
      
      `uvm_info("METRICS", $sformatf(
        "TOTALES: pkts=%0d, bytes=%0d, bw_total=%.3f bytes/cycle", 
        total_packets, total_bytes, total_bw
      ), UVM_LOW)

      // Cerrar archivo
      if (fh) begin
        $fclose(fh);
        `uvm_info("METRICS", $sformatf("Archivo CSV cerrado: %s", csv_path), UVM_LOW)
      end
      
      `uvm_info("METRICS", "=== FIN REPORTE MÉTRICAS ===", UVM_LOW)
    endfunction

    // ✅ Función de limpieza
    function void final_phase(uvm_phase phase);
      // Declaraciones al inicio
      int src;
      int tid;
      
      super.final_phase(phase);
      
      // Reportar transacciones TX pendientes (no recibidas)
      foreach (tx_timestamps[src]) begin
        foreach (tx_timestamps[src][tid]) begin
          `uvm_warning("METRICS", $sformatf(
            "TX pendiente no recibido: src=%0d, tid=%0d, tx_time=%0d", 
            src, tid, tx_timestamps[src][tid]))
        end
      end
    endfunction

  endclass

endpackage
