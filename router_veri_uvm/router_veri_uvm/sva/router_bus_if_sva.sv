// Módulo SVA para verificación de interfaz de bus de router - valida estabilidad de datos y operaciones pop
module router_bus_if_sva #(
  parameter int PCKG_SZ = 40
)(
  input logic clk,
  input logic reset,
  input logic pop,
  input logic pndng,
  input logic [PCKG_SZ-1:0] data_out
);


  //Los datos deben mantenerse estables cuando hay datos pendientes y no se hace pop
  property data_stable_when_pending_no_pop;
    @(posedge clk) disable iff(reset)
    pndng && !pop |-> $stable(data_out);
  endproperty

  assert property(data_stable_when_pending_no_pop) 
    else $error("BUS_IF: data_out cambió con pndng && !pop");

  //No se debe hacer pop cuando no había datos pendientes en el ciclo anterior
  property no_pop_when_empty;
    @(posedge clk) disable iff(reset)
    pop |-> $past(pndng);
  endproperty

  assert property(no_pop_when_empty) 
    else $error("BUS_IF: pop sin pndng previo");

endmodule
