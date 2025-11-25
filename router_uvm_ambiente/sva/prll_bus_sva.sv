// Módulo SVA para verificación de bus paralelo - detecta estados X/Z no válidos
module prll_bus_sva #(
  parameter int BITS = 32
)(
  input  logic clk,
  input  logic reset,
  inout  wire [BITS-1:0] bus 
);

  // Propiedad: No permitir estados X/Z en el bus

  property no_xz_when_active;
    @(posedge clk) disable iff(reset)
    !$isunknown(bus);
  endproperty

  assert property(no_xz_when_active) 
    else $error("PRLL_BUS: bus en X/Z");

endmodule
