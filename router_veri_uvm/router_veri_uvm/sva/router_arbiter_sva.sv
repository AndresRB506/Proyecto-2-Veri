// Módulo SVA para verificación de árbitro de router - valida selección y coherencia de datos
module router_arbiter_sva #(
  parameter int NUM     = 4,
  parameter int PCKG_SZ = 40
)(
  input logic clk,
  input logic reset,
  input logic [NUM-1:0] pndng_i,
  input logic [PCKG_SZ-1:0] data_out_i [NUM-1:0],
  input logic [$clog2(NUM)-1:0] trn,
  input logic push_i,
  input logic pop_i,
  input logic [PCKG_SZ-1:0] data_in_i
);


  // Push solo debe ocurrir cuando hay datos pendientes en el puerto seleccionado
  property push_implies_pending_selected;
    @(posedge clk) disable iff(reset)
    push_i |-> pndng_i[trn];
  endproperty

  assert property(push_implies_pending_selected) 
    else $error("ARB: push_i asertado sin pndng_i[trn]");

  // Propiedad: Los datos de entrada deben coincidir con los datos del puerto seleccionado
  property mux_coherence_on_push;
    @(posedge clk) disable iff(reset)
    push_i |-> (data_in_i == data_out_i[trn]);
  endproperty

  assert property(mux_coherence_on_push) 
    else $error("ARB: data_in_i no coincide con data_out_i[trn] bajo push_i");

endmodule
