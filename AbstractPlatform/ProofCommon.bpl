var cpu_mem_1                             : mem_t;
var cpu_mem_2                             : mem_t;
var cpu_regs_1                            : regs_t;
var cpu_regs_2                            : regs_t;
var cpu_pc_1                              : vaddr_t;
var cpu_pc_2                              : vaddr_t;
var cpu_enclave_id_1                      : tap_enclave_id_t;
var cpu_enclave_id_2                      : tap_enclave_id_t;
var cpu_addr_valid_1                      : addr_valid_t;
var cpu_addr_valid_2                      : addr_valid_t;
var cpu_addr_map_1                        : addr_map_t;
var cpu_addr_map_2                        : addr_map_t;
var cpu_owner_map_1                       : owner_map_t;
var cpu_owner_map_2                       : owner_map_t;
var cache_valid_map_1                     : cache_valid_map_t;
var cache_valid_map_2                     : cache_valid_map_t;
var cache_tag_map_1                       : cache_tag_map_t;
var cache_tag_map_2                       : cache_tag_map_t;
var tap_enclave_metadata_valid_1          : tap_enclave_metadata_valid_t;
var tap_enclave_metadata_valid_2          : tap_enclave_metadata_valid_t;
var tap_enclave_metadata_addr_map_1       : tap_enclave_metadata_addr_map_t;
var tap_enclave_metadata_addr_map_2       : tap_enclave_metadata_addr_map_t;
var tap_enclave_metadata_addr_valid_1     : tap_enclave_metadata_addr_valid_t;
var tap_enclave_metadata_addr_valid_2     : tap_enclave_metadata_addr_valid_t;
var tap_enclave_metadata_addr_excl_1      : tap_enclave_metadata_addr_excl_t;
var tap_enclave_metadata_addr_excl_2      : tap_enclave_metadata_addr_excl_t;
var tap_enclave_metadata_entrypoint_1     : tap_enclave_metadata_entrypoint_t;
var tap_enclave_metadata_entrypoint_2     : tap_enclave_metadata_entrypoint_t;
var tap_enclave_metadata_pc_1             : tap_enclave_metadata_pc_t;
var tap_enclave_metadata_pc_2             : tap_enclave_metadata_pc_t;
var tap_enclave_metadata_regs_1           : tap_enclave_metadata_regs_t;
var tap_enclave_metadata_regs_2           : tap_enclave_metadata_regs_t;
var tap_enclave_metadata_paused_1         : tap_enclave_metadata_paused_t;
var tap_enclave_metadata_paused_2         : tap_enclave_metadata_paused_t;
var tap_enclave_metadata_cache_conflict_1 : tap_enclave_metadata_cache_conflict_t;
var tap_enclave_metadata_cache_conflict_2 : tap_enclave_metadata_cache_conflict_t;

var tap_enclave_metadata_privileged_1     : tap_enclave_metadata_privileged_t;
var tap_enclave_metadata_privileged_2     : tap_enclave_metadata_privileged_t;
var tap_enclave_metadata_owner_map_1      : tap_enclave_metadata_owner_map_t;
var tap_enclave_metadata_owner_map_2      : tap_enclave_metadata_owner_map_t;


procedure {:inline 1} RestoreContext_1()
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
    cpu_mem                             := cpu_mem_1;
    cpu_regs                            := cpu_regs_1;
    cpu_pc                              := cpu_pc_1;
    cpu_enclave_id                      := cpu_enclave_id_1;
    cpu_addr_valid                      := cpu_addr_valid_1;
    cpu_addr_map                        := cpu_addr_map_1;
    cpu_owner_map                       := cpu_owner_map_1;
    cache_valid_map                     := cache_valid_map_1;
    cache_tag_map                       := cache_tag_map_1;
    tap_enclave_metadata_valid          := tap_enclave_metadata_valid_1;
    tap_enclave_metadata_addr_map       := tap_enclave_metadata_addr_map_1;
    tap_enclave_metadata_addr_valid     := tap_enclave_metadata_addr_valid_1;
    tap_enclave_metadata_addr_excl      := tap_enclave_metadata_addr_excl_1;
    tap_enclave_metadata_entrypoint     := tap_enclave_metadata_entrypoint_1;
    tap_enclave_metadata_pc             := tap_enclave_metadata_pc_1;
    tap_enclave_metadata_regs           := tap_enclave_metadata_regs_1;
    tap_enclave_metadata_paused         := tap_enclave_metadata_paused_1;
    tap_enclave_metadata_cache_conflict := tap_enclave_metadata_cache_conflict_1;
    tap_enclave_metadata_privileged     := tap_enclave_metadata_privileged_1;
    tap_enclave_metadata_owner_map      := tap_enclave_metadata_owner_map_1;
}

procedure {:inline 1} SaveContext_1()
    modifies cpu_mem_1;
    modifies cpu_regs_1;
    modifies cpu_pc_1;
    modifies cpu_enclave_id_1;
    modifies cpu_addr_valid_1;
    modifies cpu_addr_map_1;
    modifies cpu_owner_map_1;
    modifies cache_valid_map_1, cache_tag_map_1;
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
{
    cpu_mem_1                             := cpu_mem;
    cpu_regs_1                            := cpu_regs;
    cpu_pc_1                              := cpu_pc;
    cpu_enclave_id_1                      := cpu_enclave_id;
    cpu_addr_valid_1                      := cpu_addr_valid;
    cpu_addr_map_1                        := cpu_addr_map;
    cpu_owner_map_1                       := cpu_owner_map;
    cache_valid_map_1                     := cache_valid_map;
    cache_tag_map_1                       := cache_tag_map;
    tap_enclave_metadata_valid_1          := tap_enclave_metadata_valid;
    tap_enclave_metadata_addr_map_1       := tap_enclave_metadata_addr_map;
    tap_enclave_metadata_addr_valid_1     := tap_enclave_metadata_addr_valid;
    tap_enclave_metadata_addr_excl_1      := tap_enclave_metadata_addr_excl;
    tap_enclave_metadata_entrypoint_1     := tap_enclave_metadata_entrypoint;
    tap_enclave_metadata_pc_1             := tap_enclave_metadata_pc;
    tap_enclave_metadata_regs_1           := tap_enclave_metadata_regs;
    tap_enclave_metadata_paused_1         := tap_enclave_metadata_paused;
    tap_enclave_metadata_cache_conflict_1 := tap_enclave_metadata_cache_conflict;
    tap_enclave_metadata_privileged_1     := tap_enclave_metadata_privileged;
    tap_enclave_metadata_owner_map_1      := tap_enclave_metadata_owner_map;
}

procedure {:inline 2} RestoreContext_2()
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
    cpu_mem                             := cpu_mem_2;
    cpu_regs                            := cpu_regs_2;
    cpu_pc                              := cpu_pc_2;
    cpu_enclave_id                      := cpu_enclave_id_2;
    cpu_addr_valid                      := cpu_addr_valid_2;
    cpu_addr_map                        := cpu_addr_map_2;
    cpu_owner_map                       := cpu_owner_map_2;
    cache_valid_map                     := cache_valid_map_2;
    cache_tag_map                       := cache_tag_map_2;
    tap_enclave_metadata_valid          := tap_enclave_metadata_valid_2;
    tap_enclave_metadata_addr_map       := tap_enclave_metadata_addr_map_2;
    tap_enclave_metadata_addr_valid     := tap_enclave_metadata_addr_valid_2;
    tap_enclave_metadata_addr_excl      := tap_enclave_metadata_addr_excl_2;
    tap_enclave_metadata_entrypoint     := tap_enclave_metadata_entrypoint_2;
    tap_enclave_metadata_pc             := tap_enclave_metadata_pc_2;
    tap_enclave_metadata_regs           := tap_enclave_metadata_regs_2;
    tap_enclave_metadata_paused         := tap_enclave_metadata_paused_2;
    tap_enclave_metadata_cache_conflict := tap_enclave_metadata_cache_conflict_2;
    tap_enclave_metadata_privileged     := tap_enclave_metadata_privileged_2;
    tap_enclave_metadata_owner_map      := tap_enclave_metadata_owner_map_2;
}

procedure {:inline 2} SaveContext_2()
    modifies cpu_mem_2;
    modifies cpu_regs_2;
    modifies cpu_pc_2;
    modifies cpu_enclave_id_2;
    modifies cpu_addr_valid_2;
    modifies cpu_addr_map_2;
    modifies cpu_owner_map_2;
    modifies cache_valid_map_2, cache_tag_map_2;
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
    cpu_mem_2                             := cpu_mem;
    cpu_regs_2                            := cpu_regs;
    cpu_pc_2                              := cpu_pc;
    cpu_enclave_id_2                      := cpu_enclave_id;
    cpu_addr_valid_2                      := cpu_addr_valid;
    cpu_addr_map_2                        := cpu_addr_map;
    cpu_owner_map_2                       := cpu_owner_map;
    cache_valid_map_2                     := cache_valid_map;
    cache_tag_map_2                       := cache_tag_map;
    tap_enclave_metadata_valid_2          := tap_enclave_metadata_valid;
    tap_enclave_metadata_addr_map_2       := tap_enclave_metadata_addr_map;
    tap_enclave_metadata_addr_valid_2     := tap_enclave_metadata_addr_valid;
    tap_enclave_metadata_addr_excl_2      := tap_enclave_metadata_addr_excl;
    tap_enclave_metadata_entrypoint_2     := tap_enclave_metadata_entrypoint;
    tap_enclave_metadata_pc_2             := tap_enclave_metadata_pc;
    tap_enclave_metadata_regs_2           := tap_enclave_metadata_regs;
    tap_enclave_metadata_paused_2         := tap_enclave_metadata_paused;
    tap_enclave_metadata_cache_conflict_2 := tap_enclave_metadata_cache_conflict;
    tap_enclave_metadata_privileged_2     := tap_enclave_metadata_privileged;
    tap_enclave_metadata_owner_map_2      := tap_enclave_metadata_owner_map;
}

procedure HavocOSMem(excl_map : excl_map_t);
    modifies cpu_mem;
    ensures (forall p : wap_addr_t ::
                    (cpu_owner_map[p] != tap_null_enc_id || !excl_map[p])
                        ==> (cpu_mem[p] == old(cpu_mem)[p]));

procedure InitOSMem(container_valid : container_valid_t, container_data : container_data_t);
    modifies cpu_mem;
    ensures (forall p : wap_addr_t ::
                    if (cpu_owner_map[p] == tap_null_enc_id && container_valid[p])
                        then cpu_mem[p] == container_data[p]
                        else cpu_mem[p] == old(cpu_mem)[p]);

procedure InitialHavoc(eid: tap_enclave_id_t)
    returns (current_mode : mode_t);

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
    modifies tap_enclave_metadata_owner_map;
    modifies tap_enclave_metadata_privileged;
    
    ensures (current_mode == mode_untrusted);
    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    ensures (cpu_enclave_id == tap_null_enc_id);
    
    // corner cases, precondition for launch
    ensures (!tap_enclave_metadata_privileged[tap_null_enc_id]);
    ensures (tap_enclave_metadata_owner_map[tap_null_enc_id] == tap_null_enc_id);
    // cut branches: all enclaves are NE
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    !tap_enclave_metadata_privileged[e]);

    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    // current pc invariants
    ensures (tap_addr_perm_x(cpu_addr_valid[cpu_pc]));
    ensures (cpu_owner_map[cpu_addr_map[cpu_pc]] == cpu_enclave_id);

    // enclave invariants.
    ensures tap_enclave_metadata_valid[tap_null_enc_id];
    ensures (forall e : tap_enclave_id_t :: 
                special_enclave_id(e) ==> !tap_enclave_metadata_valid[e]);
    // eid cannot be valid at init stage.
    ensures !tap_enclave_metadata_valid[eid];
    // randomness control: differrent traces have same ownermap at beginning.
    // cut branches: those ensures will cost a lot

    // ensures (forall e : tap_enclave_id_t :: tap_enclave_metadata_valid[e] ==> 
    //             (tap_enclave_metadata_valid[tap_enclave_metadata_owner_map[e]]));
    // ensures (forall e : tap_enclave_id_t :: 
    //             (tap_enclave_metadata_owner_map[e] != eid));
    // ensures (forall e : tap_enclave_id_t :: 
    //             !valid_enclave_id(e) ==> 
    //                 !tap_enclave_metadata_valid[e]);

    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid[e][tap_enclave_metadata_pc[e]]));
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid[e][tap_enclave_metadata_entrypoint[e]]));
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_enclave_metadata_addr_excl[e][tap_enclave_metadata_pc[e]]);
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_enclave_metadata_addr_excl[e][tap_enclave_metadata_entrypoint[e]]);
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    cpu_owner_map[tap_enclave_metadata_addr_map[e][tap_enclave_metadata_pc[e]]] == e);
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    cpu_owner_map[tap_enclave_metadata_addr_map[e][tap_enclave_metadata_entrypoint[e]]] == e);
    
    // for those valid & active enclave when init, its owner is OS by default
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_enclave_metadata_owner_map[e] == tap_null_enc_id);
    
    // CPU/Enclave address map invariants.
    // mapping & addr_valid sync
    ensures (forall va : vaddr_t :: 
                (cpu_addr_map[va] == tap_enclave_metadata_addr_map[cpu_enclave_id][va]));
    ensures (forall va : vaddr_t :: 
                (tap_addr_perm_eq(cpu_addr_valid[va], tap_enclave_metadata_addr_valid[cpu_enclave_id][va])));
    
    //  Feb 16, 2023.
    //  initial state: all are NE
    ensures (forall e : tap_enclave_id_t :: 
                tap_enclave_metadata_valid[e] ==> 
                    !tap_enclave_metadata_privileged[e]);
    //  Apr 7, 2023.
    //  initial state: exclusive memory consistency
    ensures (forall e : tap_enclave_id_t, v : vaddr_t :: 
        tap_enclave_metadata_valid[e] ==> 
            (tap_enclave_metadata_addr_excl[e][v] <==> cpu_owner_map[tap_enclave_metadata_addr_map[e][v]] == e));
    

// launch startup stage.
procedure LaunchHavoc(eid : tap_enclave_id_t) 
    returns (addr_valid : addr_valid_t, 
             addr_map : addr_map_t, 
             excl_vaddr : excl_vaddr_t, 
             excl_map : excl_map_t, 
             entrypoint : vaddr_t, 
             privilege : bool);
             
    ensures tap_addr_perm_x(addr_valid[entrypoint]);
    ensures excl_map[addr_map[entrypoint]];
    ensures excl_vaddr[entrypoint];
    ensures (forall pa : wap_addr_t :: 
        (excl_map[pa] ==> cpu_owner_map[pa] == tap_null_enc_id));
    ensures (forall v : vaddr_t :: 
        (excl_vaddr[v] ==> tap_addr_perm_v(addr_valid[v])));
    ensures (forall v : vaddr_t :: 
        (excl_vaddr[v] ==> excl_map[addr_map[v]]));
    ensures (forall v1, v2 : vaddr_t :: 
        !vaddr_alias(excl_vaddr, addr_map, v1, v2)); 
    ensures !privilege;

procedure LaunchInputHavoc(eid : tap_enclave_id_t)
    returns (addr_valid : addr_valid_t, 
             addr_map : addr_map_t, 
             excl_vaddr : excl_vaddr_t, 
             excl_map : excl_map_t, 
             entrypoint : vaddr_t, 
             privilege : bool);
    ensures tap_addr_perm_x(addr_valid[entrypoint]);
    ensures excl_map[addr_map[entrypoint]];
    ensures excl_vaddr[entrypoint];
    ensures (forall pa : wap_addr_t :: 
        (excl_map[pa] ==> cpu_owner_map_1[pa] == tap_null_enc_id));
    ensures (forall pa : wap_addr_t :: 
        (excl_map[pa] ==> cpu_owner_map_2[pa] == tap_null_enc_id));
    ensures !excl_map[cpu_addr_map_1[cpu_pc_1]];
    ensures !excl_map[cpu_addr_map_2[cpu_pc_2]];
    ensures (forall v : vaddr_t :: 
        (excl_vaddr[v] ==> tap_addr_perm_v(addr_valid[v])));
    ensures (forall v : vaddr_t :: 
        (excl_vaddr[v] ==> excl_map[addr_map[v]]));
    ensures (forall v1, v2 : vaddr_t :: 
        !vaddr_alias(excl_vaddr, addr_map, v1, v2)); 
    ensures !privilege;

procedure LoadHavoc(eid : tap_enclave_id_t)
    returns (i_eid : tap_enclave_id_t);

    ensures tap_enclave_metadata_valid[i_eid];
    ensures tap_enclave_metadata_privileged[eid] ==> 
        (i_eid == eid || tap_enclave_metadata_owner_map[i_eid] == eid);
    ensures !tap_enclave_metadata_privileged[eid] ==>
        (i_eid == eid);

// mapping interface privided by PE.
procedure AcquireMapping(eid : tap_enclave_id_t)
    returns (r_vaddr : vaddr_t, r_paddr : wap_addr_t, r_valid : addr_perm_t);
    ensures tap_enclave_metadata_privileged[tap_enclave_metadata_owner_map[eid]] ==>
        tap_enclave_metadata_addr_excl[eid][r_vaddr] <==> cpu_owner_map[r_paddr] == eid;

// Uninterpreted functions to model deterministic computation.
function uf_cpu_r0_index(opcode : word_t) : regindex_t;
function uf_cpu_r1_index(opcode : word_t) : regindex_t;
function uf_cpu_r2_index(opcode : word_t) : regindex_t;
axiom (forall w : word_t :: valid_regindex(uf_cpu_r0_index(w)));
axiom (forall w : word_t :: valid_regindex(uf_cpu_r1_index(w)));
axiom (forall w : word_t :: valid_regindex(uf_cpu_r2_index(w)));

function uf_mem_load_vaddr(pc : vaddr_t, op : word_t, r1 : word_t, r2 : word_t) : vaddr_t;

function uf_mem_load_eid (pc : vaddr_t, op : word_t, r1 : word_t, r2 : word_t) : tap_enclave_id_t;

function uf_mem_store_vaddr(pc : vaddr_t, op : word_t, l_data : word_t, r1 : word_t, r2 : word_t) : vaddr_t;
function uf_mem_store_data(pc : vaddr_t, op : word_t, l_data : word_t, r1 : word_t, r2 : word_t) : word_t;
function uf_cpu_pc(pc : vaddr_t, op : word_t, l_data : word_t, r1 : word_t, r2 : word_t) : vaddr_t;
function uf_cpu_result(pc : vaddr_t, op : word_t, l_data : word_t, r1 : word_t, r2 : word_t) : word_t;
function uf_observation(cpu_pc : vaddr_t, l_word : word_t, r_word : word_t, hit1 : bool, hit2 : bool, r_valid : addr_perm_t, r_paddr : wap_addr_t) : word_t;
function uf_observation_mem(cpu_pc : vaddr_t, l_word : word_t, r_word : word_t) : word_t;
function uf_observation_cache(hit1 : bool, hit2 : bool) : word_t;
function uf_observation_pt(r_valid : addr_perm_t, r_paddr : wap_addr_t) : word_t;

function uf_load_selector(pc : vaddr_t, op : word_t, r1 : word_t, r2 : word_t) : tap_enclave_id_t;

// axiom (forall i_eid : tap_enclave_id_t, r1 : word_t, r2 : word_t :: 
//     tap_enclave_metadata_valid[uf_load_selector(i_eid, r1, r2)]);
// axiom (forall i_eid : tap_enclave_id_t, r1 : word_t, r2 : word_t :: 
//     tap_enclave_metadata_privileged[i_eid] ==> 
//         uf_load_selector(i_eid, r1, r2) == i_eid || tap_enclave_metadata_owner_map[uf_load_selector(i_eid, r1, r2)] == i_eid);
// axiom (forall i_eid : tap_enclave_id_t, r1 : word_t, r2 : word_t :: 
//     !tap_enclave_metadata_privileged[i_eid] ==> 
//         uf_load_selector(i_eid, r1, r2) == i_eid);