// Secuencias - incluye sequence items y secuencias de prueba
package mesh_uvm_seq_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;

  class mesh_seq_item extends uvm_sequence_item;
    `uvm_object_utils(mesh_seq_item)

    rand int unsigned PCKG_SZ;
    rand int unsigned rows;
    rand int unsigned colums;
    
    // Header del paquete
    rand mesh_uvm_pkg::hdr_t hdr;
    
    // Índice del terminal
    rand int unsigned term_idx;
    
    // Flag para inyección de errores
    rand bit inject_error;

    // Restricciones de valores válidos
    constraint c_bounds {
      rows inside {[2:32]};
      colums inside {[2:32]};
      hdr.dst_r < rows;
      hdr.dst_c < colums;
    }

    function new(string name = "mesh_seq_item");
      super.new(name);
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
      
      for (int t = 0; t < 4; t++) begin
        
        // Generar transacciones para terminal actual
        for (int i = 0; i < TXS_PER_TERM; i++) begin
          req = mesh_seq_item::type_id::create($sformatf("timed_%0d_%0d", t, i));
          
          start_item(req);
            req.hdr.mode  = $urandom_range(0, 1);
            req.hdr.dst_r = $urandom_range(0, req.rows - 1);
            req.hdr.dst_c = $urandom_range(0, req.colums - 1);
            
            // Asignar valores aleatorios a otros campos
            req.hdr.src     = $urandom_range(0, 255);
            req.hdr.tid     = $urandom_range(0, 255);
            req.hdr.payload = {$random, $random};
            req.term_idx    = t;
          finish_item(req);

          get_response(rsp);
          
          // Crear delay aleatorio entre transacciones
          gap = $urandom_range(MIN_GAP, MAX_GAP);
          if (gap > 0) begin
            repeat(gap) begin
              #10; 
            end
          end
        end
      end
    endtask

  endclass

  class error_injection_seq extends uvm_sequence #(mesh_seq_item);
    `uvm_object_utils(error_injection_seq)

    int unsigned TXS          = 100;  // Total de transacciones
    int unsigned ERR_RATE_PCT = 5;    // Porcentaje de paquetes con error

    task body();
      mesh_seq_item req;
      
      for (int i = 0; i < TXS; i++) begin
        req = mesh_seq_item::type_id::create($sformatf("err_%0d", i));
        
        start_item(req);
          // Determinar si este paquete tendrá error
          req.inject_error = ($urandom_range(0, 99) < ERR_RATE_PCT);

          if (req.inject_error) begin
            req.hdr.mode  = $urandom_range(0, 1);
            req.hdr.dst_r = req.rows;    // Fuera de rango
            req.hdr.dst_c = req.colums;  // Fuera de rango
          end else begin
            req.hdr.mode  = $urandom_range(0, 1);
            req.hdr.dst_r = $urandom_range(0, req.rows - 1);
            req.hdr.dst_c = $urandom_range(0, req.colums - 1);
          end

          // Asignar valores aleatorios a campos comunes
          req.hdr.src     = $urandom_range(0, 255);
          req.hdr.tid     = $urandom_range(0, 255);
          req.hdr.payload = {$random, $random};
          req.term_idx    = $urandom_range(0, 3);
        finish_item(req);
      end
    endtask

  endclass

endpackage
