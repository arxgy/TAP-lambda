function uf_load_data(vaddr : vaddr_t, iter : int) : word_t;

//--------------------------------------------------------------------------//
// Utility functions for measurement theorem.                               //
//--------------------------------------------------------------------------//
procedure {:inline 1} MeasurementEnclaveComputation(iter : int)
    returns (vaddr : vaddr_t, data : word_t)

    modifies cpu_mem;
    modifies cpu_regs;
    modifies cpu_pc;
    modifies cache_valid_map, cache_tag_map, cpu_addr_valid;

    requires (tap_enclave_metadata_valid[cpu_enclave_id]);
    requires tap_addr_perm_x(cpu_addr_valid[cpu_pc]);
    requires cpu_owner_map[cpu_addr_map[cpu_pc]] == cpu_enclave_id;
{
    var r0, r1  : word_t;
    var rd      : regindex_t;
    var eid     : tap_enclave_id_t;
    var pc_pa   : wap_addr_t;
    var pc_op   : word_t;
    var l_vaddr : vaddr_t;
    var l_data  : word_t;
    var s_vaddr : vaddr_t;
    var s_data  : word_t;
    var excp    : exception_t;
    var hit     : bool;
    var way     : cache_way_index_t;
    var i_eid   : tap_enclave_id_t;
    var is_invalid_id : bool;
    var another_eid : tap_enclave_id_t;

    // Determine another trace's eid, just for validation sync.
    // Not elegant, but it's Z3-provable. Quite weird.
    another_eid := cpu_enclave_id_1;    
    assume (cpu_enclave_id_1 != cpu_enclave_id_2 && cpu_enclave_id == cpu_enclave_id_1) ==> (another_eid == cpu_enclave_id_2);
    assume (cpu_enclave_id_1 != cpu_enclave_id_2 && cpu_enclave_id == cpu_enclave_id_2) ==> (another_eid == cpu_enclave_id_1);
    assume (cpu_enclave_id_1 == cpu_enclave_id_2) ==> (another_eid == cpu_enclave_id_1);

    eid := cpu_enclave_id;
    pc_pa := cpu_addr_map[cpu_pc];
    assert tap_enclave_metadata_addr_excl[eid][cpu_pc];
    assert cpu_owner_map[pc_pa] == eid;
    havoc way; assume valid_cache_way_index(way);
    call pc_op, excp, hit := fetch_va(cpu_pc, way);
    assert excp == excp_none;

    // two register sources.
    r0 := cpu_regs[uf_cpu_r0_index(pc_op)];
    r1 := cpu_regs[uf_cpu_r1_index(pc_op)];
    
    // operation sync.
    i_eid := uf_load_selector(cpu_pc, pc_op, r0, r1);
    // strongest version.
    if (!tap_enclave_metadata_privileged[cpu_enclave_id] || i_eid == another_eid) {
        i_eid := cpu_enclave_id;
    } 
    is_invalid_id :=    ((!tap_enclave_metadata_valid[i_eid]) || 
                         (tap_enclave_metadata_privileged[cpu_enclave_id]  && i_eid != cpu_enclave_id && tap_enclave_metadata_owner_map[i_eid] != cpu_enclave_id) || 
                         (!tap_enclave_metadata_privileged[cpu_enclave_id] && i_eid != cpu_enclave_id));
    if (is_invalid_id) {
        vaddr := k0_vaddr_t;
        data  := k0_word_t;
        return;
    }

    // load address and value.
    l_vaddr := uf_mem_load_vaddr(cpu_pc, pc_op, r0, r1);
    // assume tap_addr_perm_r(cpu_addr_valid[l_vaddr]);
    assume tap_addr_perm_r(tap_enclave_metadata_addr_valid[i_eid][l_vaddr]);

    // select proper virtual address.
    assume tap_enclave_metadata_addr_excl_1[i_eid][l_vaddr] <==> tap_enclave_metadata_addr_excl_2[i_eid][l_vaddr];

    if(tap_enclave_metadata_addr_excl[i_eid][l_vaddr]) {
        // assert cpu_owner_map[cpu_addr_map[l_vaddr]] == eid;
        // havoc way; assume valid_cache_way_index(way);
        // call l_data, excp, hit := load_va(l_vaddr, way);
        
        // load from exclusive memory
        havoc way; 
        assume valid_cache_way_index(way);
        call l_data, excp, hit := load_va(i_eid, l_vaddr, way);
        assert excp == excp_none;
    } else {
        l_data := uf_load_data(l_vaddr, iter);
        excp := excp_none;
        hit := false;
    }

    // get data to store to mem.
    s_vaddr := uf_mem_store_vaddr(cpu_pc, pc_op, l_data, r0, r1);
    s_data := uf_mem_store_data(cpu_pc, pc_op, l_data, r0, r1);
    assume tap_addr_perm_w(cpu_addr_valid[s_vaddr]);
    // update mem if we are writing to private memory.
    if (tap_enclave_metadata_addr_excl[eid][s_vaddr]) {
        assert cpu_owner_map[cpu_addr_map[s_vaddr]] == eid;
        havoc way; assume valid_cache_way_index(way);
        call excp, hit := store_va(s_vaddr, s_data, way);
        assert excp == excp_none;
    }
    // if we're writing to shared memory, there's no point because
    // we can't expect the OS to "remember" what we wrote anyway.
    // but we do check that both enclaves write the same data to 
    // the same vaddr.
    vaddr := s_vaddr;
    data := s_data;

    // update pc.
    cpu_pc := uf_cpu_pc(cpu_pc, pc_op, l_data, r0, r1);
    assume tap_addr_perm_x(cpu_addr_valid[cpu_pc]);
    assume tap_enclave_metadata_addr_excl[eid][cpu_pc];
    assert cpu_owner_map[cpu_addr_map[cpu_pc]] == eid;
    // update regs.
    rd := uf_cpu_r2_index(pc_op);
    cpu_regs[rd] := uf_cpu_result(cpu_pc, pc_op, l_data, r0, r1);
}
// Boogie 2.16.4.0
//    Parameter to :inline attribute on a function must be Boolean
function is_measurement_untrusted_op(op : tap_proof_op_t) : bool
{ 
  op == tap_proof_op_resume || 
  op == tap_proof_op_enter  ||
  op == tap_proof_op_exit   || 
  op == tap_proof_op_pause
}
// enter pass, resume failed
function is_measurement_privilege_op(op : tap_proof_op_t) : bool
{
  op == tap_proof_op_enter      || 
  op == tap_proof_op_compute    ||
  op == tap_proof_op_destroy    ||
  op == tap_proof_op_exit       ||
  op == tap_proof_op_launch     ||
  op == tap_proof_op_resume     ||
  op == tap_proof_op_pause
}

function is_measurement_enclave_op(op : tap_proof_op_t) : bool
{ 
  op == tap_proof_op_compute    ||
  op == tap_proof_op_pause      ||
  op == tap_proof_op_exit
}

procedure {:inline 1} MeasurementUntrustedOp(
    /* mode      */ mode    : mode_t,
    /* operation */ op      : tap_proof_op_t, 
    /* enclave   */ eid     : tap_enclave_id_t,
    /* args      */ r_regs  : regs_t
) 
  returns (status : enclave_op_result_t, current_mode : mode_t)
  modifies cpu_mem;
  modifies cpu_regs;
  modifies cpu_pc;
  modifies cpu_enclave_id;
  modifies cpu_addr_valid;
  modifies cpu_addr_map;
  modifies cpu_owner_map;
  modifies tap_enclave_metadata_valid;
  modifies tap_enclave_metadata_addr_map;
  modifies tap_enclave_metadata_addr_valid;
  modifies tap_enclave_metadata_entrypoint;
  modifies tap_enclave_metadata_pc;
  modifies tap_enclave_metadata_regs;
  modifies tap_enclave_metadata_paused;
  modifies tap_enclave_metadata_cache_conflict;
{
    var regs    : regs_t;

    assert (is_measurement_untrusted_op(op));
    regs := cpu_regs;
    status := enclave_op_success;

    assert (cpu_enclave_id != tap_null_enc_id) ==> 
        (tap_enclave_metadata_owner_map[cpu_enclave_id] == eid);
    assert (cpu_enclave_id != tap_null_enc_id) ==> 
        (tap_enclave_metadata_privileged[tap_enclave_metadata_owner_map[cpu_enclave_id]]);

    if (op == tap_proof_op_enter) {
        call status := enter(eid);
        cpu_regs := r_regs;
        
        assert mode == mode_enclave ==> status == enclave_op_success;
        if (status == enclave_op_success) {
            current_mode := mode_enclave;
        } else {
            cpu_regs := regs;
            current_mode := mode_untrusted;
        }

    } else if (op == tap_proof_op_resume) {
        call status := resume(eid);
        assert mode == mode_enclave ==> status == enclave_op_success;
        if (status == enclave_op_success) {
            current_mode := mode_enclave;
        } else {
            current_mode := mode_untrusted;
        }

    } else if (op == tap_proof_op_exit) {
        call status := exit();
        if (status == enclave_op_success) {
           current_mode := mode_enclave;
        } else {
            current_mode := mode_untrusted;
        }
        assert mode == mode_enclave ==> status == enclave_op_success;

    } else if (op == tap_proof_op_pause) {
        call status := pause();
        if (status == enclave_op_success) {
            current_mode := mode_enclave;
        } else {
            current_mode := mode_untrusted;
        }
        assert mode == mode_enclave ==> status == enclave_op_success;

    }

}

procedure {:inline 1} MeasurementEnclaveOp(
    /* mode      */ mode  : mode_t,
    /* target    */ r_eid : tap_enclave_id_t,
    /* operation */ op    : tap_proof_op_t,
    /* iteration */ iter  : int
) 
  returns (status : enclave_op_result_t, current_mode : mode_t, vaddr : vaddr_t, word : word_t)
  modifies cpu_mem;
  modifies cpu_regs;
  modifies cpu_pc;
  modifies cpu_enclave_id;
  modifies cpu_addr_valid;
  modifies cpu_addr_map;
  modifies cpu_owner_map;
  modifies cache_valid_map, cache_tag_map;
  modifies tap_enclave_metadata_valid;
  modifies tap_enclave_metadata_addr_map;
  modifies tap_enclave_metadata_addr_valid;
  modifies tap_enclave_metadata_addr_excl;
  modifies tap_enclave_metadata_entrypoint;
  modifies tap_enclave_metadata_pc;
  modifies tap_enclave_metadata_regs;
  modifies tap_enclave_metadata_paused;
  modifies tap_enclave_metadata_cache_conflict;
  modifies tap_enclave_metadata_privileged;
  modifies tap_enclave_metadata_owner_map;
{
    var regs              : regs_t;
    var p_regs            : regs_t;
    var p_container_valid : container_valid_t;
    var p_container_data  : container_data_t;
    /* enclave launch structure */
    var r_addr_valid      : addr_valid_t;
    var r_addr_map        : addr_map_t;
    var r_excl_vaddr      : excl_vaddr_t;
    var r_excl_map        : excl_map_t;
    var r_entrypoint      : vaddr_t;
    var r_privileged      : bool;

    vaddr := k0_vaddr_t;
    word  := k0_word_t;
    regs  := cpu_regs;

    if (tap_enclave_metadata_privileged[cpu_enclave_id]) {
        assert is_measurement_privilege_op(op);
        
        if (op == tap_proof_op_enter) {
            call status := enter(r_eid);
            cpu_regs := p_regs;
            
            if (status == enclave_op_success) {
                current_mode := mode_untrusted;
            } else {
                cpu_regs  := regs;
                current_mode := mode_enclave;
            }
            // mode == mode_untrusted means we are in trace_2, sync operation.
            // sync: all eid's children must be same stage.
            assert mode == mode_untrusted ==> status == enclave_op_success;

        } else if (op == tap_proof_op_compute) {
            call vaddr, word := MeasurementEnclaveComputation(iter);
            status := enclave_op_success;
            current_mode := mode_enclave;

        } else if (op == tap_proof_op_destroy) {
            call status := destroy(r_eid);
            current_mode := mode_enclave;

        } else if (op == tap_proof_op_exit) {
            call status := exit();
            assert status == enclave_op_success;
            current_mode := mode_untrusted;

        } else if (op == tap_proof_op_launch) {
            assume !tap_enclave_metadata_valid[r_eid];
            call InitOSMem(p_container_valid, p_container_data);
            // Apr 6, 2023. add a buildup stage for launch.
            call r_addr_valid, r_addr_map, r_excl_vaddr, r_excl_map, r_entrypoint, r_privileged := LaunchHavoc(r_eid);
            call status := launch(r_eid, r_addr_valid, r_addr_map,
                                r_excl_vaddr, r_excl_map, r_entrypoint, r_privileged);
            current_mode := mode_enclave;

        } else if (op == tap_proof_op_resume) {
            call status := resume(r_eid);
            if (status == enclave_op_success) {
                current_mode := mode_untrusted;
            } else {
                current_mode := mode_enclave;
            }
            assert mode == mode_untrusted ==> status == enclave_op_success;

        } else if (op == tap_proof_op_pause) {
            call status := pause();
            assert status == enclave_op_success;
            current_mode := mode_untrusted;

        }
        
    } else {
        assert is_measurement_enclave_op(op);

        if (op == tap_proof_op_compute) {
            call vaddr, word := MeasurementEnclaveComputation(iter);
            status := enclave_op_success;
            current_mode := mode_enclave;

        } else if (op == tap_proof_op_exit) {
            call status := exit();
            assert status == enclave_op_success;
            current_mode := mode_untrusted;

        } else if (op == tap_proof_op_pause) {
            call status := pause();
            assert status == enclave_op_success;
            current_mode := mode_untrusted;

        }
    }

}

//--------------------------------------------------------------------------//
// Measurement theorem.                                                     //
//--------------------------------------------------------------------------//
procedure measurement_proof_part1()
  returns (
      /* enclave id */  eid_1, eid_2                   : tap_enclave_id_t,
      /* addr_valid */  e_addr_valid_1, e_addr_valid_2 : addr_valid_t,
      /* addr_map   */  e_addr_map_1, e_addr_map_2     : addr_map_t,
      /* excl vaddr */  e_excl_vaddr_1, e_excl_vaddr_2 : excl_vaddr_t,
      /* excl paddr */  e_excl_map_1, e_excl_map_2     : excl_map_t,
      /* entrypoint */  e_entrypoint_1, e_entrypoint_2 : vaddr_t,
      /* privileged */  e_privileged_1, e_privileged_2 : bool,
      /* mode       */  current_mode                   : mode_t
  )

  modifies cpu_mem;
  modifies cpu_regs;
  modifies cpu_pc;
  modifies cpu_enclave_id;
  modifies cpu_addr_valid;
  modifies cpu_addr_map;
  modifies cpu_owner_map;
  modifies cache_valid_map, cache_tag_map;
  modifies cache_valid_map_1, cache_tag_map_1;
  modifies cache_valid_map_2, cache_tag_map_2;
  modifies tap_enclave_metadata_valid;
  modifies tap_enclave_metadata_addr_map;
  modifies tap_enclave_metadata_addr_valid;
  modifies tap_enclave_metadata_addr_excl;
  modifies tap_enclave_metadata_entrypoint;
  modifies tap_enclave_metadata_pc;
  modifies tap_enclave_metadata_regs;
  modifies tap_enclave_metadata_paused;
  modifies tap_enclave_metadata_cache_conflict;
  modifies tap_enclave_metadata_privileged;
  modifies tap_enclave_metadata_owner_map;
  modifies cpu_mem_1;
  modifies cpu_regs_1;
  modifies cpu_pc_1;
  modifies cpu_enclave_id_1;
  modifies cpu_addr_valid_1;
  modifies cpu_addr_map_1;
  modifies cpu_owner_map_1;
  modifies tap_enclave_metadata_valid_1;
  modifies tap_enclave_metadata_addr_map_1;
  modifies tap_enclave_metadata_addr_valid_1;
  modifies tap_enclave_metadata_addr_excl_1;
  modifies tap_enclave_metadata_entrypoint_1;
  modifies tap_enclave_metadata_pc_1;
  modifies tap_enclave_metadata_regs_1;
  modifies tap_enclave_metadata_paused_1;
  modifies tap_enclave_metadata_cache_conflict_1;
  modifies tap_enclave_metadata_privileged_1;
  modifies tap_enclave_metadata_owner_map_1;
  modifies cpu_mem_2;
  modifies cpu_regs_2;
  modifies cpu_pc_2;
  modifies cpu_enclave_id_2;
  modifies cpu_addr_valid_2;
  modifies cpu_addr_map_2;
  modifies cpu_owner_map_2;
  modifies tap_enclave_metadata_valid_2;
  modifies tap_enclave_metadata_addr_map_2;
  modifies tap_enclave_metadata_addr_valid_2;
  modifies tap_enclave_metadata_addr_excl_2;
  modifies tap_enclave_metadata_entrypoint_2;
  modifies tap_enclave_metadata_pc_2;
  modifies tap_enclave_metadata_regs_2;
  modifies tap_enclave_metadata_paused_2;
  modifies tap_enclave_metadata_cache_conflict_2;
  modifies tap_enclave_metadata_privileged_2;
  modifies tap_enclave_metadata_owner_map_2;

  ensures (forall v : vaddr_t :: excl_match(e_excl_vaddr_1, e_excl_vaddr_2, v));
  ensures (forall v : vaddr_t :: addr_valid_match(e_excl_vaddr_1, e_excl_vaddr_2, e_addr_valid_1, e_addr_valid_2, v));
  ensures (forall v : vaddr_t :: private_data_match(e_excl_vaddr_1, e_excl_vaddr_2, e_addr_map_1, e_addr_map_2, cpu_mem_1, cpu_mem_2, v));
  ensures (forall ri : regindex_t :: valid_regindex(ri) ==> (cpu_regs_1[ri] == cpu_regs_2[ri]));
  ensures (e_entrypoint_1 == e_entrypoint_2);
  ensures (e_privileged_1 == e_privileged_2);
  // PE structure consistency
  ensures (forall e : tap_enclave_id_t :: encl_owner_map_match( tap_enclave_metadata_valid_1, tap_enclave_metadata_valid_2, 
                                                                tap_enclave_metadata_owner_map_1, tap_enclave_metadata_owner_map_2,
                                                                e, eid_1, eid_2));

  ensures (current_mode == mode_untrusted);
  ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid_1[e]) ==> 
                    (cpu_owner_map_1[pa] != e));
  ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
              (valid_enclave_id(e) && !tap_enclave_metadata_valid_2[e]) ==> 
                  (cpu_owner_map_2[pa] != e));
  // eid is valid.
  ensures (valid_enclave_id(eid_1) && valid_enclave_id(eid_2));
  ensures (tap_enclave_metadata_valid_1[eid_1] && tap_enclave_metadata_valid_2[eid_2]);
  // the entrypoint always has a vaddr -> paddr mapping.
  ensures tap_addr_perm_x(
              tap_enclave_metadata_addr_valid_1[eid_1][tap_enclave_metadata_entrypoint_1[eid_1]]);
  ensures tap_addr_perm_x(
              tap_enclave_metadata_addr_valid_2[eid_2][tap_enclave_metadata_entrypoint_2[eid_2]]);
  // the pc always has a vaddr -> paddr mapping. 
  ensures tap_addr_perm_x(
              tap_enclave_metadata_addr_valid_1[eid_1][tap_enclave_metadata_pc_1[eid_1]]);
  ensures tap_addr_perm_x(
              tap_enclave_metadata_addr_valid_2[eid_2][tap_enclave_metadata_pc_2[eid_2]]);
  ensures (forall v : vaddr_t :: tap_enclave_metadata_addr_excl_1[eid_1][v] ==
                                 tap_enclave_metadata_addr_excl_2[eid_2][v]);
  ensures (forall v : vaddr_t :: addr_valid_match(tap_enclave_metadata_addr_excl_1[eid_1],
                                                  tap_enclave_metadata_addr_excl_2[eid_2],
                                                  tap_enclave_metadata_addr_valid_1[eid_1],
                                                  tap_enclave_metadata_addr_valid_2[eid_2],
                                                  v));
  ensures (forall v : vaddr_t ::
              private_data_match(tap_enclave_metadata_addr_excl_1[eid_1], tap_enclave_metadata_addr_excl_2[eid_2],
                                 tap_enclave_metadata_addr_map_1[eid_1], tap_enclave_metadata_addr_map_2[eid_2], 
                                 cpu_mem_1, cpu_mem_2, v));
  ensures (forall ri : regindex_t :: valid_regindex(ri) ==> (tap_enclave_metadata_regs_1[eid_1][ri] == tap_enclave_metadata_regs_2[eid_2][ri]));
  ensures (tap_enclave_metadata_entrypoint_1[eid_1] == tap_enclave_metadata_entrypoint_2[eid_2]);
  ensures (tap_enclave_metadata_pc_1[eid_1] == tap_enclave_metadata_pc_2[eid_2]);
  // the entrypoint is always at an exclusive address.
  ensures tap_enclave_metadata_addr_excl_1[eid_1][tap_enclave_metadata_entrypoint_1[eid_1]];
  ensures tap_enclave_metadata_addr_excl_2[eid_2][tap_enclave_metadata_entrypoint_2[eid_2]];
  // the PC is always at an exclusive address.
  ensures tap_enclave_metadata_addr_excl_1[eid_1][tap_enclave_metadata_pc_1[eid_1]];
  ensures tap_enclave_metadata_addr_excl_2[eid_2][tap_enclave_metadata_pc_2[eid_2]];
  // the state of the two enclaves is the same.
  ensures (tap_enclave_metadata_paused_1[eid_1] == tap_enclave_metadata_paused_2[eid_2]);
  // ----------------------------------------------------------------------// 
  // Related enclave state and creation parameters                         // 
  // ----------------------------------------------------------------------// 
  ensures (tap_enclave_metadata_addr_valid_1[eid_1] == e_addr_valid_1);
  ensures (tap_enclave_metadata_addr_valid_2[eid_2] == e_addr_valid_2);
  ensures (tap_enclave_metadata_addr_map_1[eid_1] == e_addr_map_1);
  ensures (tap_enclave_metadata_addr_map_2[eid_2] == e_addr_map_2);
  ensures (tap_enclave_metadata_addr_excl_1[eid_1] == e_excl_vaddr_1);
  ensures (tap_enclave_metadata_addr_excl_2[eid_2] == e_excl_vaddr_2);
  // the cpu_owner_map and enclave's excl_map are consistent.

  //----------------------------------------------------------------------//
  // aliasing invariants                                                  //
  //----------------------------------------------------------------------//
  ensures (forall v1, v2 : vaddr_t ::
              !vaddr_alias(tap_enclave_metadata_addr_excl_1[eid_1],
                           tap_enclave_metadata_addr_map_1[eid_1],
                           v1, v2));
  ensures (forall v1, v2 : vaddr_t ::
              !vaddr_alias(tap_enclave_metadata_addr_excl_2[eid_2],
                           tap_enclave_metadata_addr_map_2[eid_2],
                           v1, v2));
  // enclave invariants.
  ensures (forall v : vaddr_t ::
                tap_enclave_metadata_addr_excl_1[eid_1][v] ==> 
                (cpu_owner_map_1[tap_enclave_metadata_addr_map_1[eid_1][v]] == eid_1));
  ensures (forall v : vaddr_t ::
                tap_enclave_metadata_addr_excl_2[eid_2][v] ==> 
                (cpu_owner_map_2[tap_enclave_metadata_addr_map_2[eid_2][v]] == eid_2));

  ensures !tap_enclave_metadata_privileged_1[tap_null_enc_id];
  ensures !tap_enclave_metadata_privileged_2[tap_null_enc_id];
  ensures tap_enclave_metadata_privileged_1[eid_1] == tap_enclave_metadata_privileged_2[eid_2];
  ensures tap_enclave_metadata_privileged_1[eid_1] == e_privileged_1;
  ensures tap_enclave_metadata_privileged_2[eid_2] == e_privileged_2;

  //  Apr 8, 2023
  //  privileged relationship: unique PE
  //  Apr 19, 2023
  //  privileged relationship: multiple PE
  ensures (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_privileged_1[e]) ==> 
            (tap_enclave_metadata_owner_map_1[e] == tap_null_enc_id));
  ensures (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_privileged_2[e]) ==> 
            (tap_enclave_metadata_owner_map_2[e] == tap_null_enc_id));

  // valid guarantee
  ensures tap_enclave_metadata_valid_1[tap_null_enc_id];
  ensures tap_enclave_metadata_valid_2[tap_null_enc_id];
  ensures (forall e : tap_enclave_id_t :: special_enclave_id(e) ==> 
    !tap_enclave_metadata_valid_1[e]);
  ensures (forall e : tap_enclave_id_t :: special_enclave_id(e) ==> 
    !tap_enclave_metadata_valid_2[e]);

  // enclave ownermap relationship: valid enclave's parent must be valid
  ensures (forall e : tap_enclave_id_t :: tap_enclave_metadata_valid_1[e] ==>
    (tap_enclave_metadata_valid_1[tap_enclave_metadata_owner_map_1[e]]));
  ensures (forall e : tap_enclave_id_t :: tap_enclave_metadata_valid_2[e] ==>
    (tap_enclave_metadata_valid_2[tap_enclave_metadata_owner_map_2[e]]));

  // enclave ownermap relationship: special children
  ensures tap_enclave_metadata_owner_map_1[eid_1] == tap_null_enc_id;
  ensures tap_enclave_metadata_owner_map_2[eid_2] == tap_null_enc_id;
  ensures tap_enclave_metadata_owner_map_1[tap_null_enc_id] == tap_null_enc_id;
  ensures tap_enclave_metadata_owner_map_2[tap_null_enc_id] == tap_null_enc_id;
  
  // enclave ownermap relationship: the maximal parent-tree depth is 2 
  ensures (forall e : tap_enclave_id_t :: (tap_enclave_metadata_valid_1[e]) ==> 
    (tap_enclave_metadata_owner_map_1[tap_enclave_metadata_owner_map_1[e]] == tap_null_enc_id));
  ensures (forall e : tap_enclave_id_t :: (tap_enclave_metadata_valid_2[e]) ==> 
    (tap_enclave_metadata_owner_map_2[tap_enclave_metadata_owner_map_2[e]] == tap_null_enc_id));
  
  // if the mode_untrusted is from PE's children enclave, then the 2 traces is in **one** children enclave of this PE.
  ensures ((tap_enclave_metadata_owner_map_1[cpu_enclave_id_1] == eid_1) ==> 
    (tap_enclave_metadata_valid_2[cpu_enclave_id_2]));
  ensures ((tap_enclave_metadata_owner_map_1[cpu_enclave_id_1] == eid_1) ==>
    (tap_enclave_metadata_owner_map_2[cpu_enclave_id_2] == eid_2));
  
  // enclave ownermap relationship: enclave with chidren must be privileged 
  ensures (forall e : tap_enclave_id_t :: 
    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] != tap_null_enc_id) ==> 
      (tap_enclave_metadata_privileged_1[tap_enclave_metadata_owner_map_1[e]]));
  ensures (forall e : tap_enclave_id_t :: 
    (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_owner_map_2[e] != tap_null_enc_id) ==> 
      (tap_enclave_metadata_privileged_2[tap_enclave_metadata_owner_map_2[e]]));

  // extend exclusive memory consistency and structure rules. Apr 14, 2023.
  ensures (forall e : tap_enclave_id_t, v : vaddr_t :: 
    (tap_enclave_metadata_valid_1[e] && (tap_enclave_metadata_privileged_1[e] || tap_enclave_metadata_privileged_1[tap_enclave_metadata_owner_map_1[e]]) ==> 
        (tap_enclave_metadata_addr_excl_1[e][v] <==> cpu_owner_map_1[tap_enclave_metadata_addr_map_1[e][v]] == e)));
  ensures (forall e : tap_enclave_id_t, v : vaddr_t :: 
    (tap_enclave_metadata_valid_2[e] && (tap_enclave_metadata_privileged_2[e] || tap_enclave_metadata_privileged_2[tap_enclave_metadata_owner_map_2[e]]) ==> 
        (tap_enclave_metadata_addr_excl_2[e][v] <==> cpu_owner_map_2[tap_enclave_metadata_addr_map_2[e][v]] == e)));
  // PE sync. the PE's structure must be same.
  ensures (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] == eid_1) <==> 
            (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_owner_map_2[e] == eid_2));
  // PE sync. the two (PE) enclave's children pause state must be same. 
  ensures (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] == eid_1) ==> 
            (tap_enclave_metadata_paused_1[e] == tap_enclave_metadata_paused_2[e]));

  //----------------------------------------------------------------------//
  // invariants about the states of the CPUs.                             //
  //----------------------------------------------------------------------//
  ensures (cpu_enclave_id_1 == tap_null_enc_id && cpu_enclave_id_2 == tap_null_enc_id);
  ensures (tap_addr_perm_x(cpu_addr_valid_1[cpu_pc_1]) && 
            tap_addr_perm_x(cpu_addr_valid_2[cpu_pc_2]));
{
  var status, status_1, status_2                   : enclave_op_result_t;
  var e_container_data_1, e_container_data_2       : container_data_t;
  var e_proof_op, r_proof_op                       : tap_proof_op_t;
  var measurement_1, measurement_2                 : measurement_t;
  var measurement_1p, measurement_2p               : measurement_t;
  var vaddr_1, vaddr_2                             : vaddr_t;
  var paddr_1, paddr_2                             : wap_addr_t;
  var memp_1, memp_2                               : mem_t;
  var word_1, word_2                               : word_t;
  var proof_op                                     : tap_proof_op_t;
  var regs                                         : regs_t;
  var shared_vaddr_map                             : shared_vaddr_map_t;
  var current_mode_1, current_mode_2               : mode_t;

  call initialize_tap();
  call SaveContext_1();
  call SaveContext_2();

  assume valid_enclave_id_index(eid_1) && valid_enclave_id_index(eid_2);
  // Enclave 1
  call RestoreContext_1();
  call current_mode_1 := InitialHavoc(eid_1);
  call InitOSMem(e_excl_map_1, e_container_data_1);
  call status := launch(eid_1, e_addr_valid_1, e_addr_map_1, e_excl_vaddr_1, e_excl_map_1, e_entrypoint_1, e_privileged_1);
  assume status == enclave_op_success;
  call SaveContext_1();

  // Repeat for second enclave.
  call RestoreContext_2();
  call current_mode_2 := InitialHavoc(eid_2);
  call InitOSMem(e_excl_map_2, e_container_data_2);
  call status := launch(eid_2, e_addr_valid_2, e_addr_map_2, e_excl_vaddr_2, e_excl_map_2, e_entrypoint_2, e_privileged_2);
  assume status == enclave_op_success;
  call SaveContext_2();

  call measurement_1p, measurement_2p := 
            measure_state_self_composed(eid_1,              eid_2,
                                        e_addr_valid_1,     e_addr_valid_2, 
                                        e_addr_map_1,       e_addr_map_2,
                                        e_excl_vaddr_1,     e_excl_vaddr_2,
                                        cpu_mem_1,          cpu_mem_2, 
                                        cpu_regs_1,         cpu_regs_2,
                                        e_entrypoint_1,     e_entrypoint_2,
                                        e_entrypoint_1,     e_entrypoint_2,
                                        e_privileged_1,     e_privileged_2,
                                        tap_enclave_metadata_owner_map_1, 
                                        tap_enclave_metadata_owner_map_2,
                                        tap_enclave_metadata_valid_1,
                                        tap_enclave_metadata_valid_2 );
  assert ((forall v : vaddr_t :: 
                (excl_match(e_excl_vaddr_1, e_excl_vaddr_2, v)                 &&
                 addr_valid_match(e_excl_vaddr_1, e_excl_vaddr_2, 
                                  e_addr_valid_1, e_addr_valid_2, v)           &&
                 private_data_match(e_excl_vaddr_1, e_excl_vaddr_2,
                                    e_addr_map_1, e_addr_map_2, 
                                    cpu_mem_1, cpu_mem_2, v)))                 &&
           (forall ri : regindex_t :: valid_regindex(ri) ==> 
                                        (cpu_regs_1[ri] == cpu_regs_2[ri]))    &&
           (e_entrypoint_1 == e_entrypoint_2)                                  && 
           (e_privileged_1 == e_privileged_2)                                  && 
           (forall e : tap_enclave_id_t :: 
                encl_owner_map_match( tap_enclave_metadata_valid_1, tap_enclave_metadata_valid_2, 
                                      tap_enclave_metadata_owner_map_1, tap_enclave_metadata_owner_map_2,
                                      e, eid_1, eid_2))
           )
          <==> (measurement_1p == measurement_2p);
  // Proof p1 over. Prove p2 based on p1.
  assume measurement_1p == measurement_2p;
  assert current_mode_1 == current_mode_2;
  current_mode := current_mode_1;
}

procedure measurement_proof_part2
(
  /* enclave id */  eid_1, eid_2                   : tap_enclave_id_t,
  /* addr_valid */  e_addr_valid_1, e_addr_valid_2 : addr_valid_t,
  /* addr_map   */  e_addr_map_1, e_addr_map_2     : addr_map_t,
  /* excl vaddr */  e_addr_excl_1, e_addr_excl_2   : excl_vaddr_t,
  /* excl       */  e_excl_map_1, e_excl_map_2     : excl_map_t,
  /* entrypoint */  e_entrypoint_1, e_entrypoint_2 : vaddr_t,
  /* privileged */  e_privileged_1, e_privileged_2 : bool
)
  
  modifies cpu_mem;
  modifies cpu_regs;
  modifies cpu_pc;
  modifies cpu_enclave_id;
  modifies cpu_addr_valid;
  modifies cpu_addr_map;
  modifies cpu_owner_map;
  modifies cache_valid_map, cache_tag_map;
  modifies cache_valid_map_1, cache_tag_map_1;
  modifies cache_valid_map_2, cache_tag_map_2;
  modifies tap_enclave_metadata_valid;
  modifies tap_enclave_metadata_addr_map;
  modifies tap_enclave_metadata_addr_valid;
  modifies tap_enclave_metadata_addr_excl;
  modifies tap_enclave_metadata_entrypoint;
  modifies tap_enclave_metadata_pc;
  modifies tap_enclave_metadata_regs;
  modifies tap_enclave_metadata_paused;
  modifies tap_enclave_metadata_cache_conflict;
  modifies tap_enclave_metadata_privileged;
  modifies tap_enclave_metadata_owner_map;
  modifies cpu_mem_1;
  modifies cpu_regs_1;
  modifies cpu_pc_1;
  modifies cpu_enclave_id_1;
  modifies cpu_addr_valid_1;
  modifies cpu_addr_map_1;
  modifies cpu_owner_map_1;
  modifies tap_enclave_metadata_valid_1;
  modifies tap_enclave_metadata_addr_map_1;
  modifies tap_enclave_metadata_addr_valid_1;
  modifies tap_enclave_metadata_addr_excl_1;
  modifies tap_enclave_metadata_entrypoint_1;
  modifies tap_enclave_metadata_pc_1;
  modifies tap_enclave_metadata_regs_1;
  modifies tap_enclave_metadata_paused_1;
  modifies tap_enclave_metadata_cache_conflict_1;
  modifies tap_enclave_metadata_privileged_1;
  modifies tap_enclave_metadata_owner_map_1;
  modifies cpu_mem_2;
  modifies cpu_regs_2;
  modifies cpu_pc_2;
  modifies cpu_enclave_id_2;
  modifies cpu_addr_valid_2;
  modifies cpu_addr_map_2;
  modifies cpu_owner_map_2;
  modifies tap_enclave_metadata_valid_2;
  modifies tap_enclave_metadata_addr_map_2;
  modifies tap_enclave_metadata_addr_valid_2;
  modifies tap_enclave_metadata_addr_excl_2;
  modifies tap_enclave_metadata_entrypoint_2;
  modifies tap_enclave_metadata_pc_2;
  modifies tap_enclave_metadata_regs_2;
  modifies tap_enclave_metadata_paused_2;
  modifies tap_enclave_metadata_cache_conflict_2;
  modifies tap_enclave_metadata_privileged_2;
  modifies tap_enclave_metadata_owner_map_2;

  requires (forall v : vaddr_t :: excl_match(e_addr_excl_1, e_addr_excl_2, v));
  requires (forall v : vaddr_t :: addr_valid_match(e_addr_excl_1, e_addr_excl_2, 
                                                   e_addr_valid_1, e_addr_valid_2, v));
  requires (forall v : vaddr_t :: private_data_match(
                                    e_addr_excl_1, e_addr_excl_2,
                                    e_addr_map_1, e_addr_map_2, 
                                    cpu_mem_1, cpu_mem_2, v));
  requires (forall ri : regindex_t :: valid_regindex(ri) ==> (cpu_regs_1[ri] == cpu_regs_2[ri]));
  requires (e_entrypoint_1 == e_entrypoint_2);
  requires (e_privileged_1 == e_privileged_2);
  requires  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
              (valid_enclave_id(e) && !tap_enclave_metadata_valid_1[e]) ==> 
                  (cpu_owner_map_1[pa] != e));
  requires  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
              (valid_enclave_id(e) && !tap_enclave_metadata_valid_2[e]) ==> 
                  (cpu_owner_map_2[pa] != e));
  // eid is valid.
  requires (valid_enclave_id(eid_1) && valid_enclave_id(eid_2));
  requires (tap_enclave_metadata_valid_1[eid_1] && tap_enclave_metadata_valid_2[eid_2]);
  // the entrypoint always has a vaddr -> paddr mapping.
  requires tap_addr_perm_x(
              tap_enclave_metadata_addr_valid_1[eid_1][tap_enclave_metadata_entrypoint_1[eid_1]]);
  requires tap_addr_perm_x(
              tap_enclave_metadata_addr_valid_2[eid_2][tap_enclave_metadata_entrypoint_2[eid_2]]);
  // the pc always has a vaddr -> paddr mapping. 
  requires tap_addr_perm_x(
              tap_enclave_metadata_addr_valid_1[eid_1][tap_enclave_metadata_pc_1[eid_1]]);
  requires tap_addr_perm_x(
              tap_enclave_metadata_addr_valid_2[eid_2][tap_enclave_metadata_pc_2[eid_2]]);
  requires (tap_enclave_metadata_addr_excl_1[eid_1][tap_enclave_metadata_pc_1[eid_1]]);
  requires (tap_enclave_metadata_addr_excl_2[eid_2][tap_enclave_metadata_pc_2[eid_2]]);
  requires (tap_enclave_metadata_addr_excl_1[eid_1][tap_enclave_metadata_entrypoint_1[eid_1]]);
  requires (tap_enclave_metadata_addr_excl_2[eid_2][tap_enclave_metadata_entrypoint_2[eid_2]]);
  requires (forall v : vaddr_t :: tap_enclave_metadata_addr_excl_1[eid_1][v] ==
                                  tap_enclave_metadata_addr_excl_2[eid_2][v]);
  requires (forall v : vaddr_t :: addr_valid_match(tap_enclave_metadata_addr_excl_1[eid_1],
                                                  tap_enclave_metadata_addr_excl_2[eid_2],
                                                  tap_enclave_metadata_addr_valid_1[eid_1],
                                                  tap_enclave_metadata_addr_valid_2[eid_2],
                                                  v));
  requires (forall v : vaddr_t ::
              private_data_match(tap_enclave_metadata_addr_excl_1[eid_1], tap_enclave_metadata_addr_excl_2[eid_2],
                                 tap_enclave_metadata_addr_map_1[eid_1], tap_enclave_metadata_addr_map_2[eid_2], 
                                 cpu_mem_1, cpu_mem_2, v));
  requires (forall ri : regindex_t :: valid_regindex(ri) ==> (tap_enclave_metadata_regs_1[eid_1][ri] == tap_enclave_metadata_regs_2[eid_2][ri]));
  requires (tap_enclave_metadata_entrypoint_1[eid_1] == tap_enclave_metadata_entrypoint_2[eid_2]);
  requires (tap_enclave_metadata_pc_1[eid_1] == tap_enclave_metadata_pc_2[eid_2]);
  // the paused state of the two enclaves is the same.
  requires (tap_enclave_metadata_paused_1[eid_1] == tap_enclave_metadata_paused_2[eid_2]);
  // ----------------------------------------------------------------------// 
  // Related enclave state and creation parameters                         // 
  // ----------------------------------------------------------------------// 
  requires (forall v : vaddr_t :: tap_enclave_metadata_addr_valid_1[eid_1][v] == e_addr_valid_1[v]);
  requires (forall v : vaddr_t :: tap_enclave_metadata_addr_valid_2[eid_2][v] == e_addr_valid_2[v]);
  requires (forall v : vaddr_t :: tap_enclave_metadata_addr_map_1[eid_1][v] == e_addr_map_1[v]);
  requires (forall v : vaddr_t :: tap_enclave_metadata_addr_map_2[eid_2][v] == e_addr_map_2[v]);
  // enclave invaraints.
  requires (forall v : vaddr_t ::
                tap_enclave_metadata_addr_excl_1[eid_1][v] ==> 
                    (cpu_owner_map_1[tap_enclave_metadata_addr_map_1[eid_1][v]] == eid_1));
  requires (forall v : vaddr_t ::
                tap_enclave_metadata_addr_excl_2[eid_2][v] ==> 
                    (cpu_owner_map_2[tap_enclave_metadata_addr_map_2[eid_2][v]] == eid_2));

  //----------------------------------------------------------------------//
  // aliasing invariants                                                  //
  //----------------------------------------------------------------------//
  requires (forall v1, v2 : vaddr_t ::
              !vaddr_alias(tap_enclave_metadata_addr_excl_1[eid_1],
                           tap_enclave_metadata_addr_map_1[eid_1],
                           v1, v2));
  requires (forall v1, v2 : vaddr_t ::
              !vaddr_alias(tap_enclave_metadata_addr_excl_2[eid_2],
                           tap_enclave_metadata_addr_map_2[eid_2],
                           v1, v2));
  //----------------------------------------------------------------------//
  // invariants about the states of the CPUs.                             //
  //----------------------------------------------------------------------//
  requires (cpu_enclave_id_1 == tap_null_enc_id && 
            cpu_enclave_id_2 == tap_null_enc_id);
  requires (tap_addr_perm_x(cpu_addr_valid_1[cpu_pc_1]) && 
            tap_addr_perm_x(cpu_addr_valid_2[cpu_pc_2]));
  //----------------------------------------------------------------------//
  // invariants about PE-related structure rules                          //
  //----------------------------------------------------------------------//
  requires !tap_enclave_metadata_privileged_1[tap_null_enc_id];
  requires !tap_enclave_metadata_privileged_2[tap_null_enc_id];
  requires  tap_enclave_metadata_privileged_1[eid_1] == tap_enclave_metadata_privileged_2[eid_2];
  requires  tap_enclave_metadata_privileged_1[eid_1] == e_privileged_1;
  requires  tap_enclave_metadata_privileged_2[eid_2] == e_privileged_2;
  //  Apr 19, 2023
  //  privileged relationship: multiple PE
  requires (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_privileged_1[e]) ==> 
            (tap_enclave_metadata_owner_map_1[e] == tap_null_enc_id));
  requires (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_privileged_2[e]) ==> 
            (tap_enclave_metadata_owner_map_2[e] == tap_null_enc_id));

  // valid guarantee
  requires tap_enclave_metadata_valid_1[tap_null_enc_id];
  requires tap_enclave_metadata_valid_2[tap_null_enc_id];
  requires (forall e : tap_enclave_id_t :: special_enclave_id(e) ==> 
            !tap_enclave_metadata_valid_1[e]);
  requires (forall e : tap_enclave_id_t :: special_enclave_id(e) ==> 
            !tap_enclave_metadata_valid_2[e]);
  // enclave ownermap relationship: valid enclave's parent must be valid
  requires (forall e : tap_enclave_id_t :: tap_enclave_metadata_valid_1[e] ==>
          (tap_enclave_metadata_valid_1[tap_enclave_metadata_owner_map_1[e]]));
  requires (forall e : tap_enclave_id_t :: tap_enclave_metadata_valid_2[e] ==>
          (tap_enclave_metadata_valid_2[tap_enclave_metadata_owner_map_2[e]]));
  // enclave ownermap relationship: special children
  requires tap_enclave_metadata_owner_map_1[eid_1] == tap_null_enc_id;
  requires tap_enclave_metadata_owner_map_2[eid_2] == tap_null_enc_id;
  requires tap_enclave_metadata_owner_map_1[tap_null_enc_id] == tap_null_enc_id;
  requires tap_enclave_metadata_owner_map_2[tap_null_enc_id] == tap_null_enc_id;
  // enclave ownermap relationship: the maximal parent-tree depth is 2 
  requires (forall e : tap_enclave_id_t :: (tap_enclave_metadata_valid_1[e]) ==> 
          (tap_enclave_metadata_owner_map_1[tap_enclave_metadata_owner_map_1[e]] == tap_null_enc_id));
  requires (forall e : tap_enclave_id_t :: (tap_enclave_metadata_valid_2[e]) ==> 
          (tap_enclave_metadata_owner_map_2[tap_enclave_metadata_owner_map_2[e]] == tap_null_enc_id));
  // if the mode_untrusted is from PE's children enclave, then the 2 traces is in **one** children enclave of this PE.
  requires ((tap_enclave_metadata_owner_map_1[cpu_enclave_id_1] == eid_1) ==> 
          (tap_enclave_metadata_valid_2[cpu_enclave_id_2]));
  requires ((tap_enclave_metadata_owner_map_1[cpu_enclave_id_1] == eid_1) ==>
          (tap_enclave_metadata_owner_map_2[cpu_enclave_id_2] == eid_2));
  // enclave ownermap relationship: enclave with chidren must be privileged 
  requires (forall e : tap_enclave_id_t :: 
          (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] != tap_null_enc_id) ==> 
                (tap_enclave_metadata_privileged_1[tap_enclave_metadata_owner_map_1[e]]));
  requires (forall e : tap_enclave_id_t :: 
          (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_owner_map_2[e] != tap_null_enc_id) ==> 
                (tap_enclave_metadata_privileged_2[tap_enclave_metadata_owner_map_2[e]]));
  // extend exclusive memory consistency and structure rules. Apr 14, 2023.
  requires (forall e : tap_enclave_id_t, v : vaddr_t :: 
          (tap_enclave_metadata_valid_1[e] && (tap_enclave_metadata_privileged_1[e] || tap_enclave_metadata_privileged_1[tap_enclave_metadata_owner_map_1[e]]) ==> 
                (tap_enclave_metadata_addr_excl_1[e][v] <==> cpu_owner_map_1[tap_enclave_metadata_addr_map_1[e][v]] == e)));
  requires (forall e : tap_enclave_id_t, v : vaddr_t :: 
          (tap_enclave_metadata_valid_2[e] && (tap_enclave_metadata_privileged_2[e] || tap_enclave_metadata_privileged_2[tap_enclave_metadata_owner_map_2[e]]) ==> 
                (tap_enclave_metadata_addr_excl_2[e][v] <==> cpu_owner_map_2[tap_enclave_metadata_addr_map_2[e][v]] == e)));
  // PE sync. the PE's structure must be same.
  requires (forall e : tap_enclave_id_t :: 
          (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] == eid_1) <==> 
                (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_owner_map_2[e] == eid_2));
  // PE sync. the two (PE) enclave's children pause state must be same. 
  requires (forall e : tap_enclave_id_t :: 
          (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] == eid_1) ==> 
                (tap_enclave_metadata_paused_1[e] == tap_enclave_metadata_paused_2[e]));
{
  var r_eid                                        : tap_enclave_id_t;
  var status, status_1, status_2                   : enclave_op_result_t;
  var e_container_data_1, e_container_data_2       : container_data_t;
  var e_proof_op, r_proof_op                       : tap_proof_op_t;
  var measurement_1, measurement_2                 : measurement_t;
  var measurement_1p, measurement_2p               : measurement_t;
  var vaddr_1, vaddr_2                             : vaddr_t;
  var paddr_1, paddr_2                             : wap_addr_t;
  var memp_1, memp_2                               : mem_t;
  var word_1, word_2                               : word_t;
  var proof_op                                     : tap_proof_op_t;
  var regs, r_regs                                 : regs_t;
  var shared_vaddr_map                             : shared_vaddr_map_t;
  var current_mode                                 : mode_t;
  var current_mode_1, current_mode_2               : mode_t;
  var iter                                         : int;
  
  current_mode := mode_untrusted;
  while (*)
    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    
    // privilege relationship: OS & eid
    invariant !tap_enclave_metadata_privileged_1[tap_null_enc_id];
    invariant !tap_enclave_metadata_privileged_2[tap_null_enc_id];
    invariant tap_enclave_metadata_privileged_1[eid_1] == tap_enclave_metadata_privileged_2[eid_2];
    invariant  tap_enclave_metadata_privileged_1[eid_1] == e_privileged_1;
    invariant  tap_enclave_metadata_privileged_2[eid_2] == e_privileged_2;
    //  Apr 19, 2023
    //  privileged relationship: multiple PE
    invariant (forall e : tap_enclave_id_t :: 
            (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_privileged_1[e]) ==> 
                (tap_enclave_metadata_owner_map_1[e] == tap_null_enc_id));
    invariant (forall e : tap_enclave_id_t :: 
            (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_privileged_2[e]) ==> 
                (tap_enclave_metadata_owner_map_2[e] == tap_null_enc_id));
    // valid guarantee
    invariant tap_enclave_metadata_valid_1[tap_null_enc_id];
    invariant tap_enclave_metadata_valid_2[tap_null_enc_id];
    invariant (forall e : tap_enclave_id_t :: special_enclave_id(e) ==> 
        !tap_enclave_metadata_valid_1[e]);
    invariant (forall e : tap_enclave_id_t :: special_enclave_id(e) ==> 
        !tap_enclave_metadata_valid_2[e]);

    // enclave ownermap relationship: valid enclave's parent must be valid
    invariant (forall e : tap_enclave_id_t :: tap_enclave_metadata_valid_1[e] ==>
        (tap_enclave_metadata_valid_1[tap_enclave_metadata_owner_map_1[e]]));
    invariant (forall e : tap_enclave_id_t :: tap_enclave_metadata_valid_2[e] ==>
        (tap_enclave_metadata_valid_2[tap_enclave_metadata_owner_map_2[e]]));

    // enclave ownermap relationship: special children
    invariant tap_enclave_metadata_owner_map_1[eid_1] == tap_null_enc_id;
    invariant tap_enclave_metadata_owner_map_2[eid_2] == tap_null_enc_id;
    invariant tap_enclave_metadata_owner_map_1[tap_null_enc_id] == tap_null_enc_id;
    invariant tap_enclave_metadata_owner_map_2[tap_null_enc_id] == tap_null_enc_id;
    
    // enclave ownermap relationship: the maximal parent-tree depth is 2 
    invariant (forall e : tap_enclave_id_t :: (tap_enclave_metadata_valid_1[e]) ==> 
        (tap_enclave_metadata_owner_map_1[tap_enclave_metadata_owner_map_1[e]] == tap_null_enc_id));
    invariant (forall e : tap_enclave_id_t :: (tap_enclave_metadata_valid_2[e]) ==> 
        (tap_enclave_metadata_owner_map_2[tap_enclave_metadata_owner_map_2[e]] == tap_null_enc_id));
    
    // if the mode_untrusted is from PE's children enclave, then the 2 traces is in **one** children enclave of this PE.
    invariant ((tap_enclave_metadata_owner_map_1[cpu_enclave_id_1] == eid_1) ==> 
        (tap_enclave_metadata_valid_2[cpu_enclave_id_2]));
    invariant ((tap_enclave_metadata_owner_map_1[cpu_enclave_id_1] == eid_1) ==>
        (tap_enclave_metadata_owner_map_2[cpu_enclave_id_2] == eid_2));
    
    // enclave ownermap relationship: enclave with chidren must be privileged 
    invariant (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] != tap_null_enc_id) ==> 
          (tap_enclave_metadata_privileged_1[tap_enclave_metadata_owner_map_1[e]]));
    invariant (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_owner_map_2[e] != tap_null_enc_id) ==> 
          (tap_enclave_metadata_privileged_2[tap_enclave_metadata_owner_map_2[e]]));

    // pa ownermap wouldn't point to invalid enclave.
    invariant  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid_1[e]) ==> 
                    (cpu_owner_map_1[pa] != e));
    invariant  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid_2[e]) ==> 
                    (cpu_owner_map_2[pa] != e));

    // extend exclusive memory consistency and structure rules. Apr 14, 2023.
    invariant (forall e : tap_enclave_id_t, v : vaddr_t :: 
        (tap_enclave_metadata_valid_1[e] && (tap_enclave_metadata_privileged_1[e] || tap_enclave_metadata_privileged_1[tap_enclave_metadata_owner_map_1[e]]) ==> 
            (tap_enclave_metadata_addr_excl_1[e][v] <==> cpu_owner_map_1[tap_enclave_metadata_addr_map_1[e][v]] == e)));
    invariant (forall e : tap_enclave_id_t, v : vaddr_t :: 
        (tap_enclave_metadata_valid_2[e] && (tap_enclave_metadata_privileged_2[e] || tap_enclave_metadata_privileged_2[tap_enclave_metadata_owner_map_2[e]]) ==> 
            (tap_enclave_metadata_addr_excl_2[e][v] <==> cpu_owner_map_2[tap_enclave_metadata_addr_map_2[e][v]] == e)));
    invariant (forall v : vaddr_t :: 
        ((tap_enclave_metadata_privileged_1[cpu_enclave_id_1] || tap_enclave_metadata_privileged_1[tap_enclave_metadata_owner_map_1[cpu_enclave_id_1]])) ==> 
            (tap_enclave_metadata_addr_excl_1[cpu_enclave_id_1][v] <==> cpu_owner_map_1[cpu_addr_map_1[v]] == cpu_enclave_id_1));
    invariant (forall v : vaddr_t :: 
        ((tap_enclave_metadata_privileged_2[cpu_enclave_id_2] || tap_enclave_metadata_privileged_2[tap_enclave_metadata_owner_map_2[cpu_enclave_id_2]])) ==> 
            (tap_enclave_metadata_addr_excl_2[cpu_enclave_id_2][v] <==> cpu_owner_map_2[cpu_addr_map_2[v]] == cpu_enclave_id_2));

    // eid is valid.
    invariant (valid_enclave_id(eid_1) && valid_enclave_id(eid_2));
    invariant (tap_enclave_metadata_valid_1[eid_1] && tap_enclave_metadata_valid_2[eid_2]);
    // the entrypoint always has a vaddr -> paddr mapping.
    invariant tap_addr_perm_x(
                tap_enclave_metadata_addr_valid_1[eid_1][tap_enclave_metadata_entrypoint_1[eid_1]]);
    invariant tap_addr_perm_x(
                tap_enclave_metadata_addr_valid_2[eid_2][tap_enclave_metadata_entrypoint_2[eid_2]]);
    // the pc always has a vaddr -> paddr mapping. 
    invariant tap_addr_perm_x(
                tap_enclave_metadata_addr_valid_1[eid_1][tap_enclave_metadata_pc_1[eid_1]]);
    invariant tap_addr_perm_x(
                tap_enclave_metadata_addr_valid_2[eid_2][tap_enclave_metadata_pc_2[eid_2]]);
    //----------------------------------------------------------------------//
    // The PC and entrypoint are always at exclusive addresses.             //
    //----------------------------------------------------------------------//
    invariant (tap_enclave_metadata_addr_excl_1[eid_1][tap_enclave_metadata_pc_1[eid_1]]);
    invariant (tap_enclave_metadata_addr_excl_2[eid_2][tap_enclave_metadata_pc_2[eid_2]]);
    invariant (tap_enclave_metadata_addr_excl_1[eid_1][tap_enclave_metadata_entrypoint_1[eid_1]]);
    invariant (tap_enclave_metadata_addr_excl_2[eid_2][tap_enclave_metadata_entrypoint_2[eid_2]]);
    //----------------------------------------------------------------------//
    // aliasing invariants                                                  //
    //----------------------------------------------------------------------//
    invariant (forall v1, v2 : vaddr_t ::
                !vaddr_alias(tap_enclave_metadata_addr_excl_1[eid_1],
                             tap_enclave_metadata_addr_map_1[eid_1],
                             v1, v2));
    invariant (forall v1, v2 : vaddr_t ::
                !vaddr_alias(tap_enclave_metadata_addr_excl_2[eid_2],
                             tap_enclave_metadata_addr_map_2[eid_2],
                             v1, v2));
    // enclave invariants.
    invariant (forall v : vaddr_t ::
                  tap_enclave_metadata_addr_excl_1[eid_1][v] ==> 
                      (cpu_owner_map_1[tap_enclave_metadata_addr_map_1[eid_1][v]] == eid_1));
    invariant (forall v : vaddr_t ::
                  tap_enclave_metadata_addr_excl_2[eid_2][v] ==> 
                      (cpu_owner_map_2[tap_enclave_metadata_addr_map_2[eid_2][v]] == eid_2));
    //----------------------------------------------------------------------//
    // invariants about the states of the CPUs.                             //
    //----------------------------------------------------------------------//

    // invariants about state sync between 2 traces.
    // These properties may need extension/modification for multiple PE environment.
    // OS/NE sync. (stronger than Integrity's)
    invariant (current_mode == mode_untrusted) ==> 
                  (cpu_enclave_id_1 == cpu_enclave_id_2);
    invariant (current_mode == mode_untrusted) ==> 
                  (cpu_enclave_id_1 == tap_null_enc_id) || 
                  (tap_enclave_metadata_owner_map_1[cpu_enclave_id_1] == eid_1);
    // PE sync. the PE's structure must be same.
    invariant (forall e : tap_enclave_id_t :: 
        (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] == eid_1) <==> 
            (tap_enclave_metadata_valid_2[e] && tap_enclave_metadata_owner_map_2[e] == eid_2));

    // PE sync. the two (PE) enclave's children pause state must be same. 
    // Apr 4, 2023.
    // invariant (!enclave_dead_1 && !enclave_dead_2) ==>
    //             (forall e : tap_enclave_id_t :: 
    //                 (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] == eid_1) ==> 
    //                     tap_enclave_metadata_paused_1[e] == tap_enclave_metadata_paused_2[e]);
    invariant (forall e : tap_enclave_id_t :: 
                    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_owner_map_1[e] == eid_1) ==> 
                        tap_enclave_metadata_paused_1[e] == tap_enclave_metadata_paused_2[e]);

    invariant (current_mode == mode_untrusted) ==> tap_enclave_metadata_valid_1[cpu_enclave_id_1];
    invariant (current_mode == mode_untrusted) ==> tap_enclave_metadata_valid_2[cpu_enclave_id_2];

    invariant (current_mode == mode_enclave) ==> 
                (cpu_enclave_id_1 == eid_1 && cpu_enclave_id_2 == eid_2);
    invariant (current_mode == mode_enclave) ==>
                (tap_addr_perm_x(cpu_addr_valid_1[cpu_pc_1]) && 
                 tap_addr_perm_x(cpu_addr_valid_2[cpu_pc_2]));
    //----------------------------------------------------------------------//
    // the state of the two enclaves is the same.                           //
    //----------------------------------------------------------------------//
    // the two evrange's match.
    invariant (forall v : vaddr_t :: tap_enclave_metadata_addr_excl_1[eid_1][v] ==
                                     tap_enclave_metadata_addr_excl_2[eid_2][v]);
    // the two page table permissions match.
    invariant (forall v : vaddr_t :: addr_valid_match(tap_enclave_metadata_addr_excl_1[eid_1],
                                                      tap_enclave_metadata_addr_excl_2[eid_2],
                                                      tap_enclave_metadata_addr_valid_1[eid_1],
                                                      tap_enclave_metadata_addr_valid_2[eid_2],
                                                      v));
    invariant (current_mode == mode_enclave) ==>
              (forall v : vaddr_t :: addr_valid_match(tap_enclave_metadata_addr_excl_1[eid_1],
                                                      tap_enclave_metadata_addr_excl_2[eid_2],
                                                      cpu_addr_valid_1, cpu_addr_valid_2, v));
    invariant (forall v : vaddr_t ::
                private_data_match(tap_enclave_metadata_addr_excl_1[eid_1], 
                                   tap_enclave_metadata_addr_excl_2[eid_2],
                                   tap_enclave_metadata_addr_map_1[eid_1], 
                                   tap_enclave_metadata_addr_map_2[eid_2], 
                                   cpu_mem_1, cpu_mem_2, v));
    invariant (current_mode == mode_enclave) ==> 
                (forall v : vaddr_t ::
                     private_data_match(tap_enclave_metadata_addr_excl_1[eid_1], 
                                        tap_enclave_metadata_addr_excl_2[eid_2],
                                        cpu_addr_map_1, cpu_addr_map_2, 
                                        cpu_mem_1, cpu_mem_2, v));
    invariant (forall ri : regindex_t :: valid_regindex(ri) ==> 
                    (tap_enclave_metadata_regs_1[eid_1][ri] == tap_enclave_metadata_regs_2[eid_2][ri]));
    invariant (current_mode == mode_enclave) ==> 
                (forall ri : regindex_t :: valid_regindex(ri) ==> (cpu_regs_1[ri] == cpu_regs_2[ri]));
    invariant (tap_enclave_metadata_entrypoint_1[eid_1] == tap_enclave_metadata_entrypoint_2[eid_2]);
    invariant (tap_enclave_metadata_pc_1[eid_1] == tap_enclave_metadata_pc_2[eid_2]);
    invariant (current_mode == mode_enclave) ==> (cpu_pc_1 == cpu_pc_2);
    invariant (current_mode == mode_enclave) ==> (tap_enclave_metadata_addr_excl_1[eid_1][cpu_pc_1]);
    invariant (current_mode == mode_enclave) ==> (tap_enclave_metadata_addr_excl_2[eid_2][cpu_pc_2]);
    invariant (tap_enclave_metadata_paused_1[eid_1] == tap_enclave_metadata_paused_2[eid_2]);
    invariant (forall va : vaddr_t ::
                (current_mode == mode_enclave) ==>
                    tap_addr_perm_eq(tap_enclave_metadata_addr_valid_1[eid_1][va], cpu_addr_valid_1[va]));
    invariant (forall va : vaddr_t ::
                (current_mode == mode_enclave) ==>
                    tap_addr_perm_eq(tap_enclave_metadata_addr_valid_2[eid_2][va], cpu_addr_valid_2[va]));
    invariant (current_mode == mode_enclave) ==>
                    (tap_enclave_metadata_addr_map_1[eid_1] == cpu_addr_map_1);
    invariant (current_mode == mode_enclave) ==>
                    (tap_enclave_metadata_addr_map_2[eid_2] == cpu_addr_map_2);
    invariant (current_mode == mode_enclave || current_mode == mode_untrusted);
  {
    havoc r_eid, proof_op, r_regs;
    if (current_mode == mode_untrusted) {

      assume is_measurement_untrusted_op(proof_op);
      call RestoreContext_1();
      call status_1, current_mode_1 := MeasurementUntrustedOp(current_mode, proof_op, eid_1, r_regs);
      call SaveContext_1();

      call RestoreContext_2();
      call status_2, current_mode_2 := MeasurementUntrustedOp(current_mode, proof_op, eid_2, r_regs);
      call SaveContext_2();

      assert status_1 == status_2;
      assert current_mode_1 == current_mode_2;

    } else if (current_mode == mode_enclave) {

      havoc iter;
      if (e_privileged_1) {
        assume is_measurement_privilege_op(proof_op);
      } else {
        assume is_measurement_enclave_op(proof_op);
      }
      assume r_eid != eid_1 && r_eid != eid_2;
      
      call RestoreContext_1();
      call status_1, current_mode_1, vaddr_1, word_1 := MeasurementEnclaveOp(current_mode, r_eid, proof_op, iter);
      call SaveContext_1();

      call RestoreContext_2();
      call status_2, current_mode_2, vaddr_2, word_2 := MeasurementEnclaveOp(current_mode, r_eid, proof_op, iter);
      call SaveContext_2();

      assert vaddr_1 == vaddr_2;
      assert word_1 == word_2;
    }
    current_mode := current_mode_1;
  }
}

procedure measurement_proof()
  modifies cpu_mem;
  modifies cpu_regs;
  modifies cpu_pc;
  modifies cpu_enclave_id;
  modifies cpu_addr_valid;
  modifies cpu_addr_map;
  modifies cpu_owner_map;
  modifies cache_valid_map, cache_tag_map;
  modifies cache_valid_map_1, cache_tag_map_1;
  modifies cache_valid_map_2, cache_tag_map_2;
  modifies tap_enclave_metadata_valid;
  modifies tap_enclave_metadata_addr_map;
  modifies tap_enclave_metadata_addr_valid;
  modifies tap_enclave_metadata_addr_excl;
  modifies tap_enclave_metadata_entrypoint;
  modifies tap_enclave_metadata_pc;
  modifies tap_enclave_metadata_regs;
  modifies tap_enclave_metadata_paused;
  modifies tap_enclave_metadata_cache_conflict;
  modifies tap_enclave_metadata_privileged;
  modifies tap_enclave_metadata_owner_map;
  modifies cpu_mem_1;
  modifies cpu_regs_1;
  modifies cpu_pc_1;
  modifies cpu_enclave_id_1;
  modifies cpu_addr_valid_1;
  modifies cpu_addr_map_1;
  modifies cpu_owner_map_1;
  modifies tap_enclave_metadata_valid_1;
  modifies tap_enclave_metadata_addr_map_1;
  modifies tap_enclave_metadata_addr_valid_1;
  modifies tap_enclave_metadata_addr_excl_1;
  modifies tap_enclave_metadata_entrypoint_1;
  modifies tap_enclave_metadata_pc_1;
  modifies tap_enclave_metadata_regs_1;
  modifies tap_enclave_metadata_paused_1;
  modifies tap_enclave_metadata_cache_conflict_1;
  modifies tap_enclave_metadata_privileged_1;
  modifies tap_enclave_metadata_owner_map_1;
  modifies cpu_mem_2;
  modifies cpu_regs_2;
  modifies cpu_pc_2;
  modifies cpu_enclave_id_2;
  modifies cpu_addr_valid_2;
  modifies cpu_addr_map_2;
  modifies cpu_owner_map_2;
  modifies tap_enclave_metadata_valid_2;
  modifies tap_enclave_metadata_addr_map_2;
  modifies tap_enclave_metadata_addr_valid_2;
  modifies tap_enclave_metadata_addr_excl_2;
  modifies tap_enclave_metadata_entrypoint_2;
  modifies tap_enclave_metadata_pc_2;
  modifies tap_enclave_metadata_regs_2;
  modifies tap_enclave_metadata_paused_2;
  modifies tap_enclave_metadata_cache_conflict_2;
  modifies tap_enclave_metadata_privileged_2;
  modifies tap_enclave_metadata_owner_map_2;
{
  var eid_1, eid_2                   : tap_enclave_id_t;
  var e_addr_valid_1, e_addr_valid_2 : addr_valid_t;
  var e_addr_map_1, e_addr_map_2     : addr_map_t;
  var e_excl_map_1, e_excl_map_2     : excl_map_t;
  var e_excl_vaddr_1, e_excl_vaddr_2 : excl_vaddr_t;
  var e_entrypoint_1, e_entrypoint_2 : vaddr_t;
  var e_privileged_1, e_privileged_2 : bool;
  var current_mode                   : mode_t;

  // proof stage 1.
  call eid_1, eid_2,
       e_addr_valid_1, e_addr_valid_2,
       e_addr_map_1, e_addr_map_2, 
       e_excl_vaddr_1, e_excl_vaddr_2,
       e_excl_map_1, e_excl_map_2,
       e_entrypoint_1, e_entrypoint_2,
       e_privileged_1, e_privileged_2,
       current_mode                     := measurement_proof_part1();
  // proof stage 2.
  call measurement_proof_part2(
         eid_1, eid_2,
         e_addr_valid_1, e_addr_valid_2,
         e_addr_map_1, e_addr_map_2,
         e_excl_vaddr_1, e_excl_vaddr_2,
         e_excl_map_1, e_excl_map_2,
         e_entrypoint_1, e_entrypoint_2,
         e_privileged_1, e_privileged_2);
}
