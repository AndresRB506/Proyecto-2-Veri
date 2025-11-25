// Paquete UVM: tipos, modelo de referencia y clases
package mesh_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // ----------------------------------------
  // Tipos de datos para ruteo
  // ----------------------------------------
  typedef enum int unsigned {
    DIR_UP    = 0,
    DIR_RIGHT = 1,
    DIR_DOWN  = 2,
    DIR_LEFT  = 3,
    DIR_LOCAL = 4
  } dir_e;

  typedef struct packed {
    bit [7:0]   dir_sel;
    bit [3:0]   dst_r;
    bit [3:0]   dst_c;
    bit         mode;      // 0: X-Y, 1: Y-X
    bit [7:0]   src;
    bit [7:0]   tid;
    bit [255:0] payload;
  } hdr_t;

  // ----------------------------------------
  // Modelo de referencia de ruteo
  // ----------------------------------------
  class routing_ref_model;
    int unsigned rows;
    int unsigned columns;

    function new(int unsigned rows = 4, int unsigned columns = 4);
      this.rows    = rows;
      this.columns = columns;
    endfunction

    function automatic dir_e calc_next_dir(
      input hdr_t h,
      input int unsigned id_r,
      input int unsigned id_c
    );
      dir_e d = DIR_LOCAL;
      bit exit_case;

      exit_case = ((h.dst_r < id_r && id_r == 1) ||
                   (h.dst_r > id_r && id_r == rows) ||
                   (h.dst_c < id_c && id_c == 1) ||
                   (h.dst_c > id_c && id_c == columns));

      if (!exit_case) begin
        if (h.mode) begin
          if      (h.dst_r < id_r) d = DIR_UP;
          else if (h.dst_r > id_r) d = DIR_DOWN;
          else if (h.dst_c < id_c) d = DIR_LEFT;
          else if (h.dst_c > id_c) d = DIR_RIGHT;
          else                     d = DIR_LOCAL;
        end else begin
          if      (h.dst_c < id_c) d = DIR_LEFT;
          else if (h.dst_c > id_c) d = DIR_RIGHT;
          else if (h.dst_r < id_r) d = DIR_UP;
          else if (h.dst_r > id_r) d = DIR_DOWN;
          else                     d = DIR_LOCAL;
        end
        return d;
      end

      // Casos de salida por borde
      if ((h.dst_r < id_r) && (id_r == 1))
        return (h.dst_c == id_c) ? DIR_UP : (h.dst_c < id_c ? DIR_LEFT : DIR_RIGHT);
      if ((h.dst_r > id_r) && (id_r == rows))
        return (h.dst_c == id_c) ? DIR_DOWN : (h.dst_c < id_c ? DIR_LEFT : DIR_RIGHT);
      if ((h.dst_c < id_c) && (id_c == 1))
        return (h.dst_r == id_r) ? DIR_LEFT : (h.dst_r < id_r ? DIR_UP : DIR_DOWN);
      if ((h.dst_c > id_c) && (id_c == columns))
        return (h.dst_r == id_r) ? DIR_RIGHT : (h.dst_r < id_r ? DIR_UP : DIR_DOWN);

      return d;
    endfunction
  endclass

  // ----------------------------------------
  // Incluye clases UVM
  // ----------------------------------------
  `include "agent/mesh_driver.sv"
  `include "env/mesh_env.sv"
  `include "scoreboard/mesh_scoreboard.sv"
  `include "mesh_sequences.sv"
  `include "tests/algn_cov_suite.sv"

endpackage

