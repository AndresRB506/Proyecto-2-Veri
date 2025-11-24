// Aqui se definen los tipos de datos y el modelo de referencia de ruteo
package mesh_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Direcciones de ruteo
  typedef enum int unsigned {
    DIR_UP    = 0,
    DIR_RIGHT = 1,
    DIR_DOWN  = 2,
    DIR_LEFT  = 3,
    DIR_LOCAL = 4
  } dir_e;

  // Estructura del header
  typedef struct packed {
    bit [7:0]   dir_sel;  // Selector de dirección
    bit [3:0]   dst_r;    
    bit [3:0]   dst_c;    // Columna destino
    bit         mode;     // Modo de ruteo (0: X-Y, 1: Y-X)
    bit [7:0]   src;      
    bit [7:0]   tid;      // ID de transacción
    bit [255:0] payload;  // Datos del paquete
  } hdr_t;

  class routing_ref_model;
    
    // Dimensiones de la malla
    int unsigned rows;
    int unsigned colums;

    function new(int unsigned rows = 4, int unsigned colums = 4);
      this.rows   = rows;
      this.colums = colums;
    endfunction

    // Función para calcular la siguiente dirección de ruteo
    function automatic dir_e calc_next_dir(
      input hdr_t h,           
      input int unsigned id_r, // Fila actual del router
      input int unsigned id_c  // Columna actual del router
    );
      dir_e d = DIR_LOCAL;
      bit exit_case;

      // Caso 1: Router interno (no en los bordes)
      if ((id_r != rows) && (id_r != 1) && (id_c != colums) && (id_c != 1)) begin
        if (h.mode) begin
          // Modo Y-X: primero rutear en Y (filas), luego en X (columnas)
          if (h.dst_r < id_r)
            d = DIR_UP;
          else if (h.dst_r > id_r)
            d = DIR_DOWN;
          else begin
            if (h.dst_c < id_c)
              d = DIR_LEFT;
            else if (h.dst_c > id_c)
              d = DIR_RIGHT;
            else
              d = DIR_LOCAL;
          end
        end else begin
          // Modo X-Y: primero rutear en X (columnas), luego en Y (filas)
          if (h.dst_c < id_c)
            d = DIR_LEFT;
          else if (h.dst_c > id_c)
            d = DIR_RIGHT;
          else begin
            if (h.dst_r < id_r)
              d = DIR_UP;
            else if (h.dst_r > id_r)
              d = DIR_DOWN;
            else
              d = DIR_LOCAL;
          end
        end
        return d;
      end

      // Caso 2: Router en el borde - verificar si necesita salir de la malla
      // ✅ Ahora asignamos valor a la variable ya declarada
      exit_case = ((h.dst_r < id_r) && (id_r == 1)) ||
                  ((h.dst_r > id_r) && (id_r == rows)) ||
                  ((h.dst_c < id_c) && (id_c == 1)) ||
                  ((h.dst_c > id_c) && (id_c == colums));

      if (exit_case) begin
        // Casos de salida por los bordes
        if ((h.dst_r < id_r) && (id_r == 1))
          return (h.dst_c == id_c) ? DIR_UP : (h.dst_c < id_c ? DIR_LEFT : DIR_RIGHT);
        
        if ((h.dst_r > id_r) && (id_r == rows))
          return (h.dst_c == id_c) ? DIR_DOWN : (h.dst_c < id_c ? DIR_LEFT : DIR_RIGHT);
        
        if ((h.dst_c < id_c) && (id_c == 1))
          return (h.dst_r == id_r) ? DIR_LEFT : (h.dst_r < id_r ? DIR_UP : DIR_DOWN);
        
        if ((h.dst_c > id_c) && (id_c == colums))
          return (h.dst_r == id_r) ? DIR_RIGHT : (h.dst_r < id_r ? DIR_UP : DIR_DOWN);
      end else begin
        // Caso 3: Router en borde pero el destino dentro de la malla
        if (h.mode) begin
          // Modo Y-X
          if (h.dst_r < id_r)
            d = DIR_UP;
          else if (h.dst_r > id_r)
            d = DIR_DOWN;
          else begin
            if (h.dst_c < id_c)
              d = DIR_LEFT;
            else if (h.dst_c > id_c)
              d = DIR_RIGHT;
            else
              d = DIR_LOCAL;
          end
        end else begin
          // Modo X-Y
          if (h.dst_c < id_c)
            d = DIR_LEFT;
          else if (h.dst_c > id_c)
            d = DIR_RIGHT;
          else begin
            if (h.dst_r < id_r)
              d = DIR_UP;
            else if (h.dst_r > id_r)
              d = DIR_DOWN;
            else
              d = DIR_LOCAL;
          end
        end
      end

      return d;
    endfunction

  endclass

endpackage
