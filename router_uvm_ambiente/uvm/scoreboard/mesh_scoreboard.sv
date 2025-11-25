// Codigo para el scoreboard UVM - verifica direcciones de ruteo contra el modelo de referencia
package mesh_scoreboard_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;

  class mesh_scoreboard extends uvm_component;
    `uvm_component_utils(mesh_scoreboard)

    // Puerto de análisis para recibir transacciones
    uvm_analysis_imp#(mesh_uvm_pkg::hdr_t, mesh_scoreboard) imp;
    
    mesh_uvm_pkg::routing_ref_model refm;
    
    int unsigned rows   = 4;  // Número de filas en la malla
    int unsigned columns = 4;  // Número de columnas en la malla
    int unsigned R_ID   = 1;  // ID de fila del router actual
    int unsigned C_ID   = 1;  // ID de columna del router actual
    
    int unsigned errors = 0;  // Número de errores detectados
    int unsigned checks = 0;  // Número total de verificaciones

    function new(string name, uvm_component parent);
      super.new(name, parent);
      imp = new("imp", this);
    endfunction

    function void build_phase(uvm_phase phase);
      void'(uvm_config_db#(int unsigned)::get(this, "", "ROWS",   rows));
      void'(uvm_config_db#(int unsigned)::get(this, "", "COLUMS", columns));
      void'(uvm_config_db#(int unsigned)::get(this, "", "R_ID",   R_ID));
      void'(uvm_config_db#(int unsigned)::get(this, "", "C_ID",   C_ID));
      
      refm = new(rows, columns);
    endfunction

    function void write(mesh_uvm_pkg::hdr_t h);
      mesh_uvm_pkg::dir_e exp;
      
      checks++;
      
      // Calcular dirección esperada usando modelo de referencia
      exp = refm.calc_next_dir(h, R_ID, C_ID);
      
      // Comparar dirección esperada vs observada
      if (h.dir_sel != exp) begin
        errors++;
        `uvm_error("SB", $sformatf(
          "Mismatch dir: exp=%0d got=%0d dst_r=%0d dst_c=%0d mode=%0d id=(%0d,%0d)", 
          exp, h.dir_sel, h.dst_r, h.dst_c, h.mode, R_ID, C_ID
        ))
      end
    endfunction

    function void report_phase(uvm_phase phase);
      `uvm_info("SB", $sformatf("Checks=%0d Errors=%0d", checks, errors), UVM_LOW)
    endfunction

  endclass

endpackage
