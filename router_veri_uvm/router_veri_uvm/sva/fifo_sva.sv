///// Módulo SVA para verificación de FIFO
module fifo_sva #(
  parameter int DEPTH = 16,
  parameter int BITS  = 32
)(
  input logic clk,
  input logic rst,
  input logic push,
  input logic pop,
  input logic full,
  input logic pndng,
  input logic [$clog2(DEPTH):0] count
);

  // Para no permitir underflow (pop cuando no hay datos)
  property no_underflow;
    @(posedge clk) disable iff(rst)
    pop |-> (pndng || (count > 0));
  endproperty

  assert property(no_underflow) 
    else $error("FIFO: pop sin datos (underflow)");

  //Para no permitir overflow (push cuando está lleno)
  property no_overflow;
    @(posedge clk) disable iff(rst)
    push && full |-> $stable(count);
  endproperty

  assert property(no_overflow) 
    else $error("FIFO: push en full (overflow)");

endmodule
