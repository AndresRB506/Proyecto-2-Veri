//// Testbench Top ////
module tb_top;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;
  import mesh_uvm_seq_pkg::*;
  import mesh_agent_pkg::*;
  import mesh_scoreboard_pkg::*;
  import mesh_env_pkg::*;
  import mesh_tests_pkg::*;

  // ========================================
  // Parametros para instanciación de módulos
  // ========================================
  parameter int ROWS_P        = 6;
  parameter int COLUMS_P      = 6;
  parameter int PCKG_SZ_P     = 40;
  parameter int FIFO_DEPTH_P  = 4;
  parameter int BDCST_P       = 255;

  // ========================================
  // RELOJ Y RESET
  // ========================================
  logic clk = 0;
  always #2 clk = ~clk;

  logic reset;
  initial begin
    reset = 1;
    #5 reset = 0;
  end

  int unsigned ROWS        = ROWS_P;
  int unsigned COLUMS      = COLUMS_P;
  int unsigned PCKG_SZ     = PCKG_SZ_P;
  int unsigned FIFO_DEPTH  = FIFO_DEPTH_P;
  int unsigned BDCST       = BDCST_P;

  // ID del router
  int unsigned R_ID        = 1;
  int unsigned C_ID        = 1;

  // Configuración de pruebas
  string       CSV_PATH    = "cm_out/metrics.csv";
  int unsigned MIN_GAP     = 0;
  int unsigned MAX_GAP     = 10;
  int unsigned TXS_PER_TERM = 50;
  int unsigned ERR_RATE_PCT = 5;

  // ========================================
  // Procesando argumentos y plusargs
  // ========================================
  initial begin
    // Parámetros de la malla
    void'($value$plusargs("ROWS=%d",        ROWS));
    void'($value$plusargs("COLUMS=%d",      COLUMS));
    void'($value$plusargs("PCKG_SZ=%d",     PCKG_SZ));
    void'($value$plusargs("FIFO_DEPTH=%d",  FIFO_DEPTH));
    void'($value$plusargs("BDCST=%d",       BDCST));

    // ID del router
    void'($value$plusargs("R_ID=%d",        R_ID));
    void'($value$plusargs("C_ID=%d",        C_ID));

    // Configuración de pruebas
    void'($value$plusargs("CSV_PATH=%s",    CSV_PATH));
    void'($value$plusargs("MIN_GAP=%d",     MIN_GAP));
    void'($value$plusargs("MAX_GAP=%d",     MAX_GAP));
    void'($value$plusargs("TXS_PER_TERM=%d", TXS_PER_TERM));
    void'($value$plusargs("ERR_RATE_PCT=%d", ERR_RATE_PCT));
  end

  // ========================================
  // INSTANCIANDO INTERFAZ Y DUT
  // ========================================
  mesh_if #(
    .ROWS    (ROWS_P),
    .COLUMS  (COLUMS_P),
    .PCKG_SZ (PCKG_SZ_P)
  ) mif (
    .clk   (clk),
    .reset (reset)
  );

  mesh_gnrtr #(
    .ROWS       (ROWS_P),
    .COLUMS     (COLUMS_P),
    .pckg_sz    (PCKG_SZ_P),
    .fifo_depth (FIFO_DEPTH_P),
    .bdcst      (BDCST_P)
  ) dut (
    .pndng           (mif.pndng),
    .data_out        (mif.data_out),
    .popin           (mif.popin),
    .pop             (mif.pop),
    .data_out_i_in   (mif.data_out_i_in),
    .pndng_i_in      (mif.pndng_i_in),
    .clk             (clk),
    .reset           (reset)
  );

  // --- DEBUG: Confirmar que el reset baja en tb_top y que el mesh_if lo ve ---

  initial begin
    @(negedge reset);
    $display("[TB_TOP DBG] t=%0t reset=%0b mif.reset=%0b", $time, reset, mif.reset);
  end

  // ========================================
  // INICIALIZANDO LA INTERFAZ
  // ========================================
  initial begin
    foreach (mif.pop[i])
      mif.pop[i] = 1'b0;
    
    foreach (mif.pndng_i_in[i])
      mif.pndng_i_in[i] = 1'b0;
    
    foreach (mif.data_out_i_in[i])
      mif.data_out_i_in[i] = '0;
  end

  // ========================================
  // INICIANDO PRUEBAS
  // ========================================
  initial begin
    uvm_config_db#(virtual mesh_if)::set(null, "*", "vif", mif);
    // Configurar parámetros de la malla (usar variables para UVM)
    uvm_config_db#(int unsigned)::set(null, "*", "ROWS",       ROWS);
    uvm_config_db#(int unsigned)::set(null, "*", "COLUMS",     COLUMS);
    uvm_config_db#(int unsigned)::set(null, "*", "PCKG_SZ",    PCKG_SZ);
    uvm_config_db#(int unsigned)::set(null, "*", "BDCST",      BDCST);

    // Configurar ID del router
    uvm_config_db#(int unsigned)::set(null, "*", "R_ID",       R_ID);
    uvm_config_db#(int unsigned)::set(null, "*", "C_ID",       C_ID);

    // Configurar parámetros de prueba
    uvm_config_db#(string)::set(null, "*", "CSV_PATH",         CSV_PATH);
    uvm_config_db#(int unsigned)::set(null, "*", "MIN_GAP",    MIN_GAP);
    uvm_config_db#(int unsigned)::set(null, "*", "MAX_GAP",    MAX_GAP);
    uvm_config_db#(int unsigned)::set(null, "*", "TXS_PER_TERM", TXS_PER_TERM);
    uvm_config_db#(int unsigned)::set(null, "*", "ERR_RATE_PCT", ERR_RATE_PCT);

    `uvm_info("TB_TOP", "Configuración UVM completada, iniciando test...", UVM_LOW)
    
    // Iniciar prueba
    run_test("algn_cov_suite");
  end

  
  // SVA para la interfaz del bus del router
  bind router_bus_interface router_bus_if_sva #(
    .PCKG_SZ(40)  // Usar valor literal en lugar del parámetro
  ) bus_if_sva (
    .clk      (clk),
    .reset    (reset),
    .pop      (1'b0),
    .pndng    (1'b0),
    .data_out ('0)
  );

  // SVA para el árbitro del router
  bind Router_arbiter router_arbiter_sva #(
    .NUM     (4),
    .PCKG_SZ (40)  // Usar valor literal en lugar del parámetro
  ) arb_sva (
    .clk        (clk),
    .reset      (reset),
    .pndng_i    (pndng_i),
    .data_out_i (data_out_i),
    .trn        (trn),
    .push_i     (push_i),
    .pop_i      (pop_i),
    .data_in_i  (data_in_i)
  );

  // SVA para la FIFO (enlace de tipo genérico)
  bind fifo_flops fifo_sva #(
    .DEPTH (depth),
    .BITS  (bits)
  ) fifo_chk (
    .clk   (clk),
    .rst   (rst),
    .push  (push),
    .pop   (pop),
    .full  (full),
    .pndng (pndng),
    .count (count)
  );

  // SVA para bus paralelo 
  bind prll_bs_ntrfs prll_bus_sva #(
    .BITS(bits)
  ) bus_chk (
    .clk   (clk),
    .reset (reset),
    .bus   (bus)
  );

endmodule

