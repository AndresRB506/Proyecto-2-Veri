// Interfaz para router - define señales de comunicación entre testbench y DUT
interface mesh_if #(
  parameter int ROWS    = 4,   
  parameter int COLUMS  = 4,     
  parameter int PCKG_SZ = 40   
)(
  input logic clk,    
  input logic reset   
);

  // ========================================
  // SEÑALES DE SALIDA DEL DUT
  // ========================================
  
  logic pndng [ROWS*2 + COLUMS*2];
  
  // Datos de salida del router (una por puerto de salida)
  logic [PCKG_SZ-1:0] data_out [ROWS*2 + COLUMS*2];

  // ========================================
  // SEÑALES DE ENTRADA AL DUT
  // ========================================
  
  // Señales de pop desde terminales externos
  logic popin [ROWS*2 + COLUMS*2];
  
  // Señales de pop desde testbench
  logic pop [ROWS*2 + COLUMS*2];
  
  // Datos de entrada desde terminales
  logic [PCKG_SZ-1:0] data_out_i_in [ROWS*2 + COLUMS*2];
  
  // Señales de datos pendientes de entrada
  logic pndng_i_in [ROWS*2 + COLUMS*2];

endinterface
