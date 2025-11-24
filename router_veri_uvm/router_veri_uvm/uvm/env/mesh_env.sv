// Package del ambiente - integra agente, scoreboard y colector de métricas
package mesh_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_agent_pkg::*;
  import mesh_scoreboard_pkg::*;
  import mesh_metrics_pkg::*;

  class mesh_env extends uvm_env;
    `uvm_component_utils(mesh_env)

    mesh_agent     m_agent;    
    mesh_scoreboard   m_sb;       
    metrics_collector m_metrics;  // recolector de métricas de rendimiento

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      m_agent   = mesh_agent::type_id::create("m_agent", this);
      m_sb      = mesh_scoreboard::type_id::create("m_sb", this);
      m_metrics = metrics_collector::type_id::create("m_metrics", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      // Conectar monitor del agente con scoreboard
      m_agent.m_monitor.ap.connect(m_sb.imp);
      
      // Conectar monitor del agente con colector de métricas
      m_agent.m_monitor.ap.connect(m_metrics.analysis_export);
    endfunction

  endclass

endpackage
