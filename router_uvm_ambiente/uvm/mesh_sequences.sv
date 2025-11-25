// Secuencias - incluye sequence items y secuencias de prueba
package mesh_uvm_seq_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;

  class mesh_seq_item extends uvm_sequence_item;
    `uvm_object_utils(mesh_seq_item)

    rand int unsigned PCKG_SZ;
    rand int unsigned rows;
    rand int unsigned columns;
    
    // Header del paquete
    rand mesh_uvm_pkg::hdr_t hdr;
    
    // Índice del terminal
    rand int unsigned term_idx;
    
    // Flag para inyección de errores
    rand bit inject_error;

    // Restricciones de valores válidos
    constraint c_bounds {
      rows inside {[2:32]};
      columns inside {[2:32]};
      hdr.dst_r < rows;
      hdr.dst_c < columns;
    }

    function new(string name = "mesh_seq_item");
      super.new(name);
      // ✅ Inicializar valores por defecto
      PCKG_SZ = 40;
      rows = 6;
      columns = 6;
      inject_error = 0;
    endfunction

    // ✅ Agregar función de debug
    function string convert2string();
      return $sformatf("mesh_seq_item: term_idx=%0d, dst_r=%0d, dst_c=%0d, mode=%0d, src=%0d, tid=%0d, inject_error=%0d", 
                       term_idx, hdr.dst_r, hdr.dst_c, hdr.mode, hdr.src, hdr.tid, inject_error);
    endfunction

  endclass

  class timed_stress_seq extends uvm_sequence #(mesh_seq_item);
    `uvm_object_utils(timed_stress_seq)

    int unsigned TXS_PER_TERM = 50;  // Transacciones por terminal
    int unsigned MIN_GAP      = 0;   // Espacio mínimo entre transacciones
    int unsigned MAX_GAP      = 10;  // Espacio máximo entre transacciones

    task body();
      mesh_seq_item req;
      mesh_seq_item rsp; 
      int gap;
      int unsigned rows = 6, columns = 6, pckg_sz = 40;  // ✅ Valores por defecto
      
      `uvm_info("TIMED_SEQ", $sformatf("=== INICIANDO BODY - TXS_PER_TERM=%0d ===", TXS_PER_TERM), UVM_LOW)
      
      // ✅ Obtener configuración del testbench
      void'(uvm_config_db#(int unsigned)::get(null, "*", "ROWS", rows));
      void'(uvm_config_db#(int unsigned)::get(null, "*", "COLUMS", columns));
      void'(uvm_config_db#(int unsigned)::get(null, "*", "PCKG_SZ", pckg_sz));
      
      `uvm_info("TIMED_SEQ", $sformatf("Configuración obtenida: ROWS=%0d, COLUMS=%0d, PCKG_SZ=%0d", rows, columns, pckg_sz), UVM_MEDIUM)
      
      for (int t = 0; t < 4; t++) begin
        `uvm_info("TIMED_SEQ", $sformatf("--- Procesando Terminal %0d ---", t), UVM_MEDIUM)
       
        // Generar transacciones para terminal actual
        for (int i = 0; i < TXS_PER_TERM; i++) begin
          `uvm_info("TIMED_SEQ", $sformatf("Creando item %0d para terminal %0d", i, t), UVM_HIGH)
          `uvm_info("TIMED_SEQ", $sformatf("TXS_PER_TERM = %0d", TXS_PER_TERM), UVM_LOW)
          req = mesh_seq_item::type_id::create($sformatf("timed_%0d_%0d", t, i));
          `uvm_info("TIMED_SEQ", "Llamando start_item", UVM_HIGH)
          start_item(req);

            //  Configurar parámetros del item ANTES de usar
            req.rows = rows;
            req.columns = columns;
            req.PCKG_SZ = pckg_sz;
            req.term_idx = t;
            req.inject_error = 0;
            
            //  Asignar valores con verificación de rangos
            req.hdr.mode  = $urandom_range(0, 1);
            req.hdr.dst_r = $urandom_range(0, (rows > 1) ? rows - 1 : 0);
            req.hdr.dst_c = $urandom_range(0, (columns > 1) ? columns - 1 : 0);
            
            // Asignar valores aleatorios a otros campos
            req.hdr.src     = $urandom_range(0, 255);
            req.hdr.tid     = $urandom_range(0, 255);
            req.hdr.payload = {$random, $random};
            
          `uvm_info("TIMED_SEQ", $sformatf("Item configurado: %s", req.convert2string()), UVM_HIGH)
          `uvm_info("TIMED_SEQ", "Llamando finish_item", UVM_HIGH)
          finish_item(req);

          `uvm_info("TIMED_SEQ", "Llamando get_response", UVM_HIGH)
          get_response(rsp);
          
          `uvm_info("TIMED_SEQ", $sformatf("Item %0d completado para terminal %0d", i, t), UVM_HIGH)
          
          // Crear delay aleatorio entre transacciones
          gap = $urandom_range(MIN_GAP, MAX_GAP);
          if (gap > 0) begin
            `uvm_info("TIMED_SEQ", $sformatf("Aplicando gap de %0d ciclos", gap), UVM_HIGH)
            repeat(gap) begin
              #10; 
            end
          end
        end
        
        `uvm_info("TIMED_SEQ", $sformatf("Terminal %0d completado (%0d transacciones)", t, TXS_PER_TERM), UVM_MEDIUM)
      end
      
      `uvm_info("TIMED_SEQ", "=== BODY COMPLETADA ===", UVM_LOW)
    endtask

  endclass

  class error_injection_seq extends uvm_sequence #(mesh_seq_item);
    `uvm_object_utils(error_injection_seq)

    int unsigned TXS          = 100;  // Total de transacciones
    int unsigned ERR_RATE_PCT = 5;    // Porcentaje de paquetes con error

    task body();
      mesh_seq_item req;
      int unsigned rows = 6, columns = 6, pckg_sz = 40;  // ✅ Valores por defecto
      
      `uvm_info("ERR_SEQ", $sformatf("=== INICIANDO ERROR_INJECTION_SEQ - TXS=%0d, ERR_RATE=%0d%% ===", TXS, ERR_RATE_PCT), UVM_LOW)
      
      // ✅ Obtener configuración del testbench
      void'(uvm_config_db#(int unsigned)::get(null, "*", "ROWS", rows));
      void'(uvm_config_db#(int unsigned)::get(null, "*", "COLUMS", columns));
      void'(uvm_config_db#(int unsigned)::get(null, "*", "PCKG_SZ", pckg_sz));
      
      for (int i = 0; i < TXS; i++) begin
        `uvm_info("ERR_SEQ", $sformatf("Creando item de error %0d", i), UVM_HIGH)
        
        req = mesh_seq_item::type_id::create($sformatf("err_%0d", i));
        
        start_item(req);
          // ✅ Configurar parámetros del item ANTES de usar
          req.rows = rows;
          req.columns = columns;
          req.PCKG_SZ = pckg_sz;
          
          // Determinar si este paquete tendrá error
          req.inject_error = ($urandom_range(0, 99) < ERR_RATE_PCT);

          if (req.inject_error) begin
            `uvm_info("ERR_SEQ", $sformatf("Inyectando error en item %0d", i), UVM_HIGH)
            req.hdr.mode  = $urandom_range(0, 1);
            req.hdr.dst_r = req.rows;    // Fuera de rango
            req.hdr.dst_c = req.columns;  // Fuera de rango
          end else begin
            req.hdr.mode  = $urandom_range(0, 1);
            req.hdr.dst_r = $urandom_range(0, (req.rows > 1) ? req.rows - 1 : 0);
            req.hdr.dst_c = $urandom_range(0, (req.columns > 1) ? req.columns - 1 : 0);
          end

          // Asignar valores aleatorios a campos comunes
          req.hdr.src     = $urandom_range(0, 255);
          req.hdr.tid     = $urandom_range(0, 255);
          req.hdr.payload = {$random, $random};
          req.term_idx    = $urandom_range(0, 3);
          
        `uvm_info("ERR_SEQ", $sformatf("Item configurado: %s", req.convert2string()), UVM_HIGH)
        finish_item(req);
      end
      
      `uvm_info("ERR_SEQ", "=== ERROR_INJECTION_SEQ COMPLETADA ===", UVM_LOW)
    endtask

  endclass

endpackage
