// Paquete del agente UVM para verificación de mesh - incluye sequencer, driver, monitor y agente
package mesh_agent_pkg;

  // ========================================
  // Importando macros
  // ========================================
  
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;
  import mesh_uvm_seq_pkg::*;

  class mesh_sequencer extends uvm_sequencer #(mesh_seq_item);
    `uvm_component_utils(mesh_sequencer)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

  endclass

  class mesh_driver extends uvm_driver #(mesh_seq_item);
    `uvm_component_utils(mesh_driver)

    // Interfaz virtual y parámetros de configuración
    virtual mesh_if vif;
    int unsigned rows     = 4;
    int unsigned colums   = 4;
    int unsigned PCKG_SZ  = 40;
    int unsigned BDCST    = 255;
    int unsigned MIN_GAP  = 0;
    int unsigned MAX_GAP  = 0;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      // Obteniendo interfaz virtual 
      if (!uvm_config_db#(virtual mesh_if)::get(this, "", "vif", vif))
        `uvm_fatal("NOVIF", "mesh_if no encontrado")

      // Obteniendo los parámetros de configuración
      void'(uvm_config_db#(int unsigned)::get(this, "", "ROWS",    rows));
      void'(uvm_config_db#(int unsigned)::get(this, "", "COLUMS",  colums));
      void'(uvm_config_db#(int unsigned)::get(this, "", "PCKG_SZ", PCKG_SZ));
      void'(uvm_config_db#(int unsigned)::get(this, "", "BDCST",   BDCST));
      void'(uvm_config_db#(int unsigned)::get(this, "", "MIN_GAP", MIN_GAP));
      void'(uvm_config_db#(int unsigned)::get(this, "", "MAX_GAP", MAX_GAP));
    endfunction

    task run_phase(uvm_phase phase);
      mesh_seq_item req;
      bit [255:0] pkt;
      bit [255:0] pkt_slice;  
      int hi;
      int t;
      longint tx_time;
      int gap;
      int payload_width;
      bit [255:0] temp_payload;
      
      forever begin
        seq_item_port.get_next_item(req);

        // Construyendo paquete de datos
        pkt = '0;
        hi = PCKG_SZ - 1;
        t = req.term_idx;

        // Empaquetando campos del header
        pkt[hi -: 8]     = req.term_idx[7:0];
        pkt[hi-8 -: 4]   = req.hdr.dst_r;
        pkt[hi-12 -: 4]  = req.hdr.dst_c;
        pkt[hi-16]       = req.hdr.mode;
        pkt[hi-17 -: 8]  = req.hdr.src;
        pkt[hi-25 -: 8]  = req.hdr.tid;
        
        payload_width = PCKG_SZ - 34;
        if (payload_width > 0) begin
          temp_payload = req.hdr.payload;
          for (int j = 0; j < payload_width; j++) begin
            pkt[j] = temp_payload[j];
          end
        end

        // Inyectando un error si es solicitado, se marca con 0xFF en campo superior
        if (req.inject_error)
          pkt[hi -: 8] = 8'hFF;

        tx_time = $time;

        // ✅ Crear slice dinámicamente usando bucle en lugar de part select
        pkt_slice = '0;
        for (int k = 0; k < PCKG_SZ; k++) begin
          pkt_slice[k] = pkt[k];
        end

        // Transmitiendo el paquete a través de la interfaz
        vif.pndng_i_in[t]    <= 1'b1;
        vif.data_out_i_in[t] <= pkt_slice;  
        vif.pop[t]           <= 1'b1;
        @(posedge vif.clk);
        
        vif.pndng_i_in[t] <= 1'b0;
        repeat(2) @(posedge vif.clk);
        vif.pop[t] <= 1'b0;

        // Espacio aleatorio entre paquetes
        gap = $urandom_range(MIN_GAP, MAX_GAP);
        repeat(gap) @(posedge vif.clk);

        seq_item_port.item_done();
      end
    endtask

  endclass

  class mesh_monitor extends uvm_monitor;
    `uvm_component_utils(mesh_monitor)

    // Interfaz virtual y puerto de análisis
    virtual mesh_if vif;
    uvm_analysis_port#(mesh_uvm_pkg::hdr_t) ap;
    
    int unsigned PCKG_SZ = 40;
    int unsigned ROWS    = 4;
    int unsigned COLUMS  = 4;

    function new(string name, uvm_component parent);
      super.new(name, parent);
      ap = new("ap", this);
    endfunction

    function void build_phase(uvm_phase phase);
      void'(uvm_config_db#(virtual mesh_if)::get(this, "", "vif", vif));
      void'(uvm_config_db#(int unsigned)::get(this, "", "PCKG_SZ", PCKG_SZ));
      void'(uvm_config_db#(int unsigned)::get(this, "", "ROWS",    ROWS));
      void'(uvm_config_db#(int unsigned)::get(this, "", "COLUMS",  COLUMS));
    endfunction

    task run_phase(uvm_phase phase);
      mesh_uvm_pkg::hdr_t h;
      bit [255:0] pkt;
      bit [255:0] pkt_slice;  
      int hi;
      int payload_width;
      bit [255:0] temp_payload;
      
      forever begin
        @(posedge vif.clk);
        
        // Monitoreando los puertos de salida
        for (int i = 0; i < ROWS*2 + COLUMS*2; i++) begin
          if (vif.pndng[i]) begin
            pkt = '0;
            
            pkt_slice = vif.data_out[i];
            for (int k = 0; k < PCKG_SZ; k++) begin
              pkt[k] = pkt_slice[k];
            end
            
            hi = PCKG_SZ - 1;

            // Desempaquetando
            h.dir_sel = pkt[hi -: 8];
            h.dst_r   = pkt[hi-8 -: 4];
            h.dst_c   = pkt[hi-12 -: 4];
            h.mode    = pkt[hi-16];
            h.src     = pkt[hi-17 -: 8];
            h.tid     = pkt[hi-25 -: 8];
            
            payload_width = PCKG_SZ - 34;
            temp_payload = '0;
            if (payload_width > 0) begin
              for (int j = 0; j < payload_width; j++) begin
                temp_payload[j] = pkt[j];
              end
            end
            h.payload = temp_payload;

            ap.write(h);
          end
        end
      end
    endtask

  endclass

  class mesh_agent extends uvm_agent;
    `uvm_component_utils(mesh_agent)

    // Componentes del agente
    mesh_sequencer m_sequencer;
    mesh_driver    m_driver;
    mesh_monitor   m_monitor;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      // Creando componentes
      m_sequencer = mesh_sequencer::type_id::create("m_sequencer", this);
      m_driver    = mesh_driver::type_id::create("m_driver", this);
      m_monitor   = mesh_monitor::type_id::create("m_monitor", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      // Conectando driver con sequencer
      m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
    endfunction

  endclass

endpackage
