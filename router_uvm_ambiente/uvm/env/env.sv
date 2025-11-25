// Package del ambiente - integra agente, scoreboard y colector de métricas
package mesh_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_agent_pkg::*;
  import mesh_scoreboard_pkg::*;
  import mesh_metrics_pkg::*;

  class mesh_env extends uvm_env;
    `uvm_component_utils(mesh_env)

    mesh_agent        m_agent;    
    mesh_scoreboard   m_sb;       
    metrics_collector m_metrics;  // recolector de métricas de rendimiento

    function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info("ENV", "Constructor ejecutado", UVM_HIGH)
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("ENV", "Iniciando build_phase", UVM_MEDIUM)
      
      m_agent   = mesh_agent::type_id::create("m_agent", this);
      m_sb      = mesh_scoreboard::type_id::create("m_sb", this);
      m_metrics = metrics_collector::type_id::create("m_metrics", this);
      
      `uvm_info("ENV", "Componentes creados", UVM_MEDIUM)
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info("ENV", "Iniciando connect_phase", UVM_MEDIUM)
      
      // Conectar monitor del agente con scoreboard
      m_agent.m_monitor.ap.connect(m_sb.imp);
      `uvm_info("ENV", "Monitor conectado a scoreboard", UVM_MEDIUM)
      
      // ✅ CORREGIR: usar analysis_imp en lugar de analysis_export
      m_agent.m_monitor.ap.connect(m_metrics.analysis_export);
      `uvm_info("ENV", "Monitor conectado a metrics collector", UVM_MEDIUM)
      
      `uvm_info("ENV", "Connect_phase completada", UVM_MEDIUM)
    endfunction

  endclass

endpackage
