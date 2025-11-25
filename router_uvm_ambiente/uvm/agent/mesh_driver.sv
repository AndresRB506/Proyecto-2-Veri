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
    int unsigned columns   = 4;
    int unsigned PCKG_SZ  = 40;
    int unsigned BDCST    = 255;
    int unsigned MIN_GAP  = 0;
    int unsigned MAX_GAP  = 0;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Obteniendo interfaz virtual 
      if (!uvm_config_db#(virtual mesh_if)::get(this, "", "vif", vif))begin
        `uvm_fatal("NOVIF", "mesh_if no encontrado")
      end 

      `uvm_info("DRIVER", $sformatf("Obtuve VIF. vif.reset=%0b (t=%0t)", vif.reset, $time), UVM_MEDIUM)
      // Obteniendo los parámetros de configuración
      void'(uvm_config_db#(int unsigned)::get(this, "", "ROWS",    rows));
      void'(uvm_config_db#(int unsigned)::get(this, "", "COLUMS",  columns));
      void'(uvm_config_db#(int unsigned)::get(this, "", "PCKG_SZ", PCKG_SZ));
      void'(uvm_config_db#(int unsigned)::get(this, "", "BDCST",   BDCST));
      void'(uvm_config_db#(int unsigned)::get(this, "", "MIN_GAP", MIN_GAP));
      void'(uvm_config_db#(int unsigned)::get(this, "", "MAX_GAP", MAX_GAP));


      `uvm_info("DRIVER_CFG", $sformatf("CFG: rows=%0d colums=%0d pckg_sz=%0d bdcst=%0d gap=[%0d..%0d]", rows, columns, PCKG_SZ, BDCST, MIN_GAP, MAX_GAP), UVM_MEDIUM)

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
      `uvm_info("DRIVER", "🚀 === RUN_PHASE INICIADO ===", UVM_LOW)     
        if (vif.reset) begin
          `uvm_info("DRIVER", $sformatf("⏳ Esperando negedge reset... vif.reset=%0b (t=%0t)", vif.reset, $time), UVM_LOW)
          @(negedge vif.reset);
          `uvm_info("DRIVER", $sformatf("✅ Reset desactivado en t=%0t", $time), UVM_LOW)
        end else begin
              `uvm_info("DRIVER", "✅ Reset ya está desactivado", UVM_LOW)
        end

      // Estabilizar
      `uvm_info("DRIVER", "⏳ Esperando 1 ciclo de clock...", UVM_LOW)
      @(posedge vif.clk);
      `uvm_info("DRIVER", $sformatf("✅ 1er ciclo completado en t=%0t", $time), UVM_LOW)
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
        if (req.inject_error) begin
          pkt[hi -: 8] = 8'hFF;
          `uvm_info("DRIVER", "Error inyectado en paquete", UVM_MEDIUM)
        end

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
        repeat(10) @(posedge vif.clk);
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
      super.build_phase(phase);
      `uvm_info("MONITOR", "Iniciando build_phase", UVM_MEDIUM)
      
      void'(uvm_config_db#(virtual mesh_if)::get(this, "", "vif", vif));
      void'(uvm_config_db#(int unsigned)::get(this, "", "PCKG_SZ", PCKG_SZ));
      void'(uvm_config_db#(int unsigned)::get(this, "", "ROWS",    ROWS));
      void'(uvm_config_db#(int unsigned)::get(this, "", "COLUMS",  COLUMS));

      `uvm_info("MONITOR_CFG",
        $sformatf("CFG: rows=%0d colums=%0d pckg_sz=%0d", ROWS, COLUMS, PCKG_SZ), UVM_MEDIUM)
    endfunction

    task run_phase(uvm_phase phase);
      mesh_uvm_pkg::hdr_t h;
      bit [255:0] pkt;
      bit [255:0] pkt_slice;  
      int hi;
      int payload_width;
      bit [255:0] temp_payload;
      int pkt_count;  // Contador de paquetes detectados
      
      `uvm_info("MONITOR", "=== MONITOR RUN_PHASE INICIADO ===", UVM_LOW)
      `uvm_info("MONITOR", $sformatf("Monitoreando %0d puertos de salida", ROWS*2 + COLUMS*2), UVM_LOW)
      
      pkt_count = 0;
      
      forever begin
        @(posedge vif.clk);
        
        // ✅ Debug cada 1000 ciclos para ver que está vivo
        if ($time % 4000 == 0) begin
          `uvm_info("MONITOR", $sformatf("🔍 Monitor activo en t=%0t, paquetes detectados=%0d", $time, pkt_count), UVM_LOW)
        end
        
        // Monitoreando los puertos de salida
        for (int i = 0; i < ROWS*2 + COLUMS*2; i++) begin
          
          // ✅ Debug detallado del primer puerto
          if (i == 0 && $time % 8000 == 0) begin
            `uvm_info("MONITOR", $sformatf("Puerto[0]: pndng=%0b, data=%0h en t=%0t", 
                      vif.pndng[0], vif.data_out[0], $time), UVM_HIGH)
          end
          
          if (vif.pndng[i]) begin
            pkt_count++;
            `uvm_info("MONITOR", $sformatf("🎯 PAQUETE #%0d DETECTADO en puerto %0d en t=%0t", 
                      pkt_count, i, $time), UVM_LOW)
            
            pkt = '0;
            
            pkt_slice = vif.data_out[i];
            `uvm_info("MONITOR", $sformatf("Raw data del puerto %0d: %0h", i, pkt_slice), UVM_HIGH)
            
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

            `uvm_info("MONITOR", $sformatf("📦 Paquete desempaquetado: src=%0d, dst=(%0d,%0d), tid=%0d, mode=%0d", 
                      h.src, h.dst_r, h.dst_c, h.tid, h.mode), UVM_LOW)
            
            `uvm_info("MONITOR", "📤 Enviando a analysis_port...", UVM_HIGH)
            ap.write(h);
            `uvm_info("MONITOR", "✅ ap.write() completado", UVM_HIGH)
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
      super.build_phase(phase);
      `uvm_info("AGENT", "Iniciando build_phase", UVM_MEDIUM)
      
      // Creando componentes
      m_sequencer = mesh_sequencer::type_id::create("m_sequencer", this);
      m_driver    = mesh_driver::type_id::create("m_driver", this);
      m_monitor   = mesh_monitor::type_id::create("m_monitor", this);
      
      `uvm_info("AGENT", "Componentes creados", UVM_MEDIUM)
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info("AGENT", "Iniciando connect_phase", UVM_MEDIUM)
      
      // Conectando driver con sequencer
      m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
      
      `uvm_info("AGENT", "Driver conectado a sequencer", UVM_MEDIUM)
    endfunction

  endclass

endpackage
