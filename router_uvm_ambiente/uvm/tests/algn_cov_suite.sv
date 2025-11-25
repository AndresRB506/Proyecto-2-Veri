// Pruebas  - pruebas de alineación y cobertura
package mesh_tests_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_env_pkg::*;
  import mesh_uvm_seq_pkg::*;

  class algn_cov_suite extends uvm_test;
    `uvm_component_utils(algn_cov_suite)

    mesh_env m_env;

    function new(string name = "algn_cov_suite", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase); // ? Importante para evitar NOCOMP
      m_env = mesh_env::type_id::create("m_env", this);
    endfunction

    task run_phase(uvm_phase phase);
      timed_stress_seq tseq;
      error_injection_seq eseq;
      int unsigned err_pct;
      
      phase.raise_objection(this);

      // ========================================
      // Secuencia de estres con timing
      // ========================================
      tseq = timed_stress_seq::type_id::create("tseq");
      
      // Configurando los parámetros o usar valores por defecto
      if (!$value$plusargs("TXS_PER_TERM=%d", tseq.TXS_PER_TERM))
        tseq.TXS_PER_TERM = 50;
      
      if (!$value$plusargs("MIN_GAP=%d", tseq.MIN_GAP))
        tseq.MIN_GAP = 0;
      
      if (!$value$plusargs("MAX_GAP=%d", tseq.MAX_GAP))
        tseq.MAX_GAP = 10;

      // Ejecutar secuencia de estrés
      tseq.start(m_env.m_agent.m_sequencer);

      // ========================================
      // Secuencia de Inyeccion de errores
      // ========================================
      eseq = error_injection_seq::type_id::create("eseq");
      
      if (!$value$plusargs("ERR_RATE_PCT=%d", err_pct))
        err_pct = 5;
      eseq.ERR_RATE_PCT = err_pct;

      // Ejecutando secuencia de inyección de errores
      eseq.start(m_env.m_agent.m_sequencer);

      phase.drop_objection(this);
    endtask

  endclass

endpackage
