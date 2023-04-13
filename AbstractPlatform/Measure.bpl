function addrperm2int(p : addr_perm_t) : int;
axiom (forall v1, v2 : addr_perm_t :: (v1 != v2) ==> (addrperm2int(v1) != addrperm2int(v2)));
axiom (forall w : addr_perm_t :: addrperm2int(w) >= 0 && addrperm2int(w) <= kmax_addr_perm_t_as_int);

// add privileged into measurement
function privileged2int (p : bool) : int;
axiom (forall v1, v2 : bool :: (v1 != v2) ==> (privileged2int(v1) != privileged2int(v2)));
axiom (forall w : bool :: privileged2int(w) >= 0 && privileged2int(w) <= kmax_privileged_t_as_int);

function valid_regindex_le(ri : regindex_t, rmax : regindex_t) : bool 
{ LE_ri(k0_regindex_t, ri) && LE_ri(ri, rmax) }

//--------------------------------------------------------------------------//
// Helper fns in order to state measurement invariants.                     //
//--------------------------------------------------------------------------//
// valid PE structure: be same
// notice case that eid == root1/2
function {:inline} encl_owner_map_match(valid1 : tap_enclave_metadata_valid_t,
                                        valid2 : tap_enclave_metadata_valid_t,
                                        map1 : tap_enclave_metadata_owner_map_t, 
                                        map2 : tap_enclave_metadata_owner_map_t, 
                                        eid : tap_enclave_id_t,
                                        root1 : tap_enclave_id_t, 
                                        root2 : tap_enclave_id_t) : bool
{ (valid1[eid] && map1[eid] == root1) <==> (valid2[eid] && map2[eid] == root2) }


function {:inline} excl_match(ev1 : excl_vaddr_t, ev2 : excl_vaddr_t, v : vaddr_t) : bool
{ ev1[v] == ev2[v] }

function {:inline} addr_valid_match(
    /* is this private? */ ev1 : excl_vaddr_t, ev2 : excl_vaddr_t, 
    /* addr permissions */ av1 : addr_valid_t, av2 : addr_valid_t, 
    v : vaddr_t
) : bool
{ (ev1[v] && ev2[v]) ==> tap_addr_perm_eq(av1[v], av2[v]) }

function {:inline} private_data_match(
     /* private?   */ ev1 : excl_vaddr_t     , ev2 : excl_vaddr_t, 
     /* addr map   */ am1 : addr_map_t       , am2 : addr_map_t       , 
     /* memory     */ m1  : mem_t            , m2  : mem_t            ,
     /* address    */ v   : vaddr_t
) : bool
{ 
  (ev1[v] && ev2[v]) ==> (m1[am1[v]] == m2[am2[v]])
}

function {:inline} shared_data_match(
     /* enclaves   */ e1  : tap_enclave_id_t , e2  : tap_enclave_id_t , 
     /* addr valid */ av1 : addr_valid_t     , av2 : addr_valid_t     , 
     /* addr map   */ am1 : addr_map_t       , am2 : addr_map_t       , 
     /* owner map  */ o1  : owner_map_t      , o2  : owner_map_t      ,
     /* memory     */ m1  : mem_t            , m2  : mem_t            ,
     /* address    */ v   : vaddr_t
) : bool
{ 
  (tap_addr_perm_v(av1[v]) && tap_addr_perm_v(av2[v]) && 
   o1[am1[v]] != e1 && o2[am2[v]] != e2) 
    ==> (m1[am1[v]] == m2[am2[v]])
}

//--------------------------------------------------------------------------//
// Measurement helper functions.                                            //
//--------------------------------------------------------------------------//
function {:inline} update_digest_virt_addr(
  /* valid      */ addr_valid : addr_valid_t,
  /* map        */ addr_map   : addr_map_t,
  /* excl       */ excl_vaddr : excl_vaddr_t,
  /* mem        */ mem        : mem_t,
  /* index      */ va         : vaddr_t,
  /* input hash */ s          : measurement_t
) : measurement_t
{
  if (excl_vaddr[va])
      then update_digest(1+word2int(mem[addr_map[va]]),
                         update_digest(1+addrperm2int(
                                            tap_addr_perm_bits(addr_valid[va])), s))
      else
           update_digest(0, update_digest(0, s))
}

  //if (tap_addr_perm_v(addr_valid[va]))
  //  then 
  //    (if owner_map[addr_map[va]] == eid
  //       then update_digest(2+word2int(mem[addr_map[va]]), s)
  //       else update_digest(1, s))
  //  else update_digest(k0_measurement_t, s)

// int(2)
const kbias_cpu_measurement_index : int;
axiom kbias_cpu_measurement_index == 2;

const kbias_privil_measurement_index : int;
axiom kbias_privil_measurement_index == 1;

// int(2 + 512)
const kmax_cpu_regs_bound_index : int;
axiom kmax_cpu_regs_bound_index == kbias_cpu_measurement_index + kN_regindex_t_as_int;

// int(2 + 512 + 1)
const kmax_cpu_privil_bound_index : int;
axiom kmax_cpu_privil_bound_index == kbias_privil_measurement_index + kmax_cpu_regs_bound_index;

// int(2 + 512 + 1 + 512)
const kmax_cpu_measurement_index : int;
axiom kmax_cpu_measurement_index == kmax_cpu_privil_bound_index + kN_enclave_id_t;

/* append metadata: privileged */ 
procedure {:inline 1} measure_cpu_state_at_index(
   /* eid        */ eid        : tap_enclave_id_t ,
   /* regs       */ regs       : regs_t           , 
   /* pc         */ pc         : vaddr_t          , 
   /* entrypoint */ entrypoint : vaddr_t          ,
   /* index      */ index      : int              ,
   /* privileged */ privileged : bool             ,
   /* owner_map  */ ownermap   : tap_enclave_metadata_owner_map_t,
   /* encl valid */ valid      : tap_enclave_metadata_valid_t,
   /* meas in    */ s          : measurement_t
)
  returns (t : measurement_t)
  requires (index >= 0 && index < kmax_cpu_measurement_index);
  
{
  var ri : regindex_t;
  var vi : int;
  var iter_eid : tap_enclave_id_t;

  if (index == 0) {
    t := update_digest(vaddr2int(pc), s);
  }
  else if (index == 1) {
    t := update_digest(vaddr2int(entrypoint), s);
  } 
  else if (index >= kbias_cpu_measurement_index && index < kmax_cpu_regs_bound_index) {
    ri := index - kbias_cpu_measurement_index;
    assert valid_regindex(ri);
    t := update_digest(word2int(regs[ri]), s);
  } 
  else if (index >= kmax_cpu_regs_bound_index && index < kmax_cpu_privil_bound_index) {
    t := update_digest(bool2int(privileged), s); 
  }
  else if (index >= kmax_cpu_privil_bound_index && index < kmax_cpu_measurement_index) {
    iter_eid := index - kmax_cpu_privil_bound_index;
    assert valid_enclave_id_index(eid);
    if (valid[iter_eid] && ownermap[iter_eid] == eid) {
      // iter_eid cannot be tap_null_enc_id, avoid default value
      t := update_digest(iter_eid, s);
    } else {
      t := update_digest(k0_int_t, s);
    }
  }
}

//--------------------------------------------------------------------------//
// Self-composed version of the measurement fn.                             //
// The self-composition is required to state the 2-safety properties of     //
// measurement.                                                             //
//--------------------------------------------------------------------------//
procedure measure_state_self_composed(
     /* enclave id */ e1          , e2          : tap_enclave_id_t , 
     /* addr valid */ av1         , av2         : addr_valid_t     , 
     /* addr map   */ am1         , am2         : addr_map_t       , 
     /* excl vaddr */ ev1         , ev2         : excl_vaddr_t     ,
     /* mem        */ m1          , m2          : mem_t            , 
     /* regs       */ regs1       , regs2       : regs_t           , 
     /* pc         */ pc1         , pc2         : vaddr_t          , 
     /* entrypoint */ entrypoint1 , entrypoint2 : vaddr_t          ,
     /* privileged */ privileged1 , privileged2 : bool             ,
     /* ownermap   */ ownermap1   , ownermap2   : tap_enclave_metadata_owner_map_t,
     /* encl valid */ valid1      , valid2      : tap_enclave_metadata_valid_t
)
  returns (t1 : measurement_t, t2 : measurement_t)
  // some additional requirement on ownermap structure.
  // These 2 judge conditions could be merged.
  requires (valid_enclave_id_index(e1) && valid_enclave_id_index(e2));
  requires (valid_enclave_id(e1) && valid_enclave_id(e2));
  requires (ownermap1[tap_null_enc_id] == tap_null_enc_id);
  requires (ownermap2[tap_null_enc_id] == tap_null_enc_id);

  ensures ((forall v : vaddr_t :: (LT_va(v, kmax_vaddr_t)) ==>
              (excl_match(ev1, ev2, v)                                                 &&
               addr_valid_match(ev1, ev2, av1, av2, v)                                 &&
               private_data_match(ev1, ev2, am1, am2, m1, m2, v)))                     &&
           (forall ri : regindex_t :: valid_regindex(ri) ==> (regs1[ri] == regs2[ri])) &&
           (pc1 == pc2 && entrypoint1 == entrypoint2 && privileged1 == privileged2)    &&
           (forall e : tap_enclave_id_t :: valid_enclave_id_index(e) ==>
              encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))
          <==> (t1 == t2);
  ensures ((exists v : vaddr_t :: (LT_va(v, kmax_vaddr_t)) &&
              (!excl_match(ev1, ev2, v)                                               ||
               !addr_valid_match(ev1, ev2, av1, av2, v)                               ||
               !private_data_match(ev1, ev2, am1, am2, m1, m2, v)))                   ||
           (exists ri : regindex_t :: valid_regindex(ri) && (regs1[ri] != regs2[ri])) ||
           (pc1 != pc2 || entrypoint1 != entrypoint2 || privileged1 != privileged2)   || 
           (exists e : tap_enclave_id_t :: valid_enclave_id_index(e) &&
              !encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))
          ==> (t1 != t2);
{
  var index : int;
  var va    : vaddr_t;
  // Loop 1. update digest/measurement by cpu state and metadata.
  // A stronger assume: e1 == e2 ==> digest1 == digest2
  t1 := 0; t2 := 0; index := 0;
  while (index < kmax_cpu_measurement_index)
    invariant (index >= 0 && index <= kmax_cpu_measurement_index);
    invariant ((pc1 == pc2 && entrypoint1 == entrypoint2 && e1 == e2 && privileged1 == privileged2) &&
               (forall ri : regindex_t :: valid_regindex(ri) ==> regs1[ri] == regs2[ri]) &&
               (forall v : vaddr_t :: av1[v] == av2[v] && am1[v] == am2[v]) &&
               (forall e : tap_enclave_id_t :: valid_enclave_id_index(e) ==> 
                  encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))
              ==> (t1 == t2);
    // Step by step.
    // 1 step over: pc
    invariant (index >= 1) ==> ((pc1 != pc2) ==> (t1 != t2));
    invariant (index <= 1) ==> ((pc1 == pc2) ==> (t1 == t2));
    // 2 steps over: entry
    invariant (index >= kbias_cpu_measurement_index) ==> ((entrypoint1 != entrypoint2) ==> (t1 != t2));
    invariant (index <= kbias_cpu_measurement_index) ==> (((pc1 == pc2) && (entrypoint1 == entrypoint2)) ==> (t1 == t2));
    // 2+n (n<=512) steps over: regs
    invariant (index > kbias_cpu_measurement_index && index <= kmax_cpu_regs_bound_index) ==> 
                ((pc1 == pc2) && (entrypoint1 == entrypoint2) && 
                 (forall ri : regindex_t :: 
                      (valid_regindex(ri) && ri < index - kbias_cpu_measurement_index) ==> regs1[ri] == regs2[ri]) 
                          ==> (t1 == t2));
    invariant (index > kbias_cpu_measurement_index) ==> 
              ((exists ri : regindex_t :: 
                  (valid_regindex(ri) && ri < (index - kbias_cpu_measurement_index) && (regs1[ri] != regs2[ri]))) 
                      ==> (t1 != t2));
    invariant (index >= kmax_cpu_regs_bound_index) ==> 
                ((exists ri : regindex_t :: valid_regindex(ri) && 
                  regs1[ri] != regs2[ri]) ==> (t1 != t2));
    // 2+512+1 steps over: privilege tag
    invariant (index > kmax_cpu_regs_bound_index && index <= kmax_cpu_privil_bound_index) ==> 
                ((pc1 == pc2) && (entrypoint1 == entrypoint2) && (privileged1 == privileged2) && 
                 (forall ri : regindex_t :: 
                       valid_regindex(ri) ==> regs1[ri] == regs2[ri]) 
                          ==> (t1 == t2));    
    invariant (index > kmax_cpu_regs_bound_index) ==> 
              ((privileged1 != privileged2) ==> (t1 != t2));
    // 2+512+1+n (n<=512) steps over: ownermap
    invariant (index > kmax_cpu_privil_bound_index && index <= kmax_cpu_measurement_index) ==> 
                ((pc1 == pc2) && (entrypoint1 == entrypoint2) && (privileged1 == privileged2) && 
                 (forall ri : regindex_t :: 
                       valid_regindex(ri) ==> regs1[ri] == regs2[ri]) &&
                 (forall e : tap_enclave_id_t :: 
                      (valid_enclave_id_index(e) && e < index - kmax_cpu_privil_bound_index) ==> 
                          encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)) 
                              ==> (t1 == t2));
    invariant (index > kmax_cpu_privil_bound_index) ==> 
              ((exists e : tap_enclave_id_t :: 
                      ( valid_enclave_id_index(e) && 
                        e < index - kmax_cpu_privil_bound_index && 
                       !encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2))) 
                          ==> (t1 != t2));
  {
    call t1 := measure_cpu_state_at_index(e1, regs1, pc1, entrypoint1, index, privileged1, ownermap1, valid1, t1);
    call t2 := measure_cpu_state_at_index(e2, regs2, pc2, entrypoint2, index, privileged2, ownermap2, valid2, t2);
    index := index + 1;
  }
  assert ((forall ri : regindex_t :: valid_regindex(ri) ==> (regs1[ri] == regs2[ri])) &&
          pc1 == pc2 && entrypoint1 == entrypoint2 && privileged1 == privileged2 && 
          (forall e : tap_enclave_id_t :: valid_enclave_id_index(e) ==> 
              encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))
         <==> (t1 == t2);
  assert ((exists ri : regindex_t :: valid_regindex(ri) && (regs1[ri] != regs2[ri])) ||
          pc1 != pc2 || entrypoint1 != entrypoint2 || privileged1 != privileged2 || 
          (exists e : tap_enclave_id_t :: valid_enclave_id_index(e) && 
              !encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))
         <==> (t1 != t2);
  
  // Loop 2. update digest/measurement by v
  // assume t1 == t2;
  // va := k0_vaddr_t;
  // while (LT_va(va, kmax_vaddr_t)) 
  //   invariant ((forall ri : regindex_t :: valid_regindex(ri) ==> (regs1[ri] == regs2[ri])) &&
  //              pc1 == pc2 && entrypoint1 == entrypoint2 && privileged1 == privileged2      &&
  //              (forall e : tap_enclave_id_t :: valid_enclave_id_index(e) ==>
  //                 encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))  &&
  //              (forall v : vaddr_t :: 
  //                 (LT_va(v, va) && LT_va(v, kmax_vaddr_t)) ==> 
  //                     (excl_match(ev1, ev2, v) &&
  //                     addr_valid_match(ev1, ev2, av1, av2, v) &&
  //                     private_data_match(ev1, ev2, am1, am2, m1, m2, v)))                  
  //              ==> (t1 == t2);
  //   invariant ((exists ri : regindex_t :: valid_regindex(ri) && (regs1[ri] != regs2[ri])) ||
  //              pc1 != pc2 || entrypoint1 != entrypoint2 || privileged1 != privileged2 ||
  //              (exists v : vaddr_t :: 
  //                  (LT_va(v, va) && LT_va(v, kmax_vaddr_t)) && 
  //                     (!excl_match(ev1, ev2, v) ||
  //                      !addr_valid_match(ev1, ev2, av1, av2, v) ||
  //                      !private_data_match(ev1, ev2, am1, am2, m1, m2, v)))                 ||
  //              (exists e : tap_enclave_id_t :: valid_enclave_id_index(e) &&
  //                 !encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))
  //              ==> (t1 != t2);
  // {
  //   t1 := update_digest_virt_addr(av1, am1, ev1, m1, va, t1);
  //   t2 := update_digest_virt_addr(av2, am2, ev2, m2, va, t2);
  //   if (t1 != t2) { return; }
  //   va := PLUS_va(va, k1_vaddr_t);
  // }
  // Deprecated appendant
  // t1 := update_digest_virt_addr(av1, am1, ev1, m1, va, t1);
  // t2 := update_digest_virt_addr(av2, am2, ev2, m2, va, t2);

  // Loop 2 with assumption.
  assume t1 == t2;
  va := k0_vaddr_t;
  while (LT_va(va, kmax_vaddr_t))
    invariant (forall v : vaddr_t :: 
                  (LT_va(v, va) && LT_va(v, kmax_vaddr_t)) ==> 
                      (excl_match(ev1, ev2, v) &&
                      addr_valid_match(ev1, ev2, av1, av2, v) &&
                      private_data_match(ev1, ev2, am1, am2, m1, m2, v)))                  
               ==> (t1 == t2);
    invariant (exists v : vaddr_t :: 
                   (LT_va(v, va) && LT_va(v, kmax_vaddr_t)) && 
                      (!excl_match(ev1, ev2, v) ||
                       !addr_valid_match(ev1, ev2, av1, av2, v) ||
                       !private_data_match(ev1, ev2, am1, am2, m1, m2, v))) 
               ==> (t1 != t2);
  {
    t1 := update_digest_virt_addr(av1, am1, ev1, m1, va, t1);
    t2 := update_digest_virt_addr(av2, am2, ev2, m2, va, t2);
    va := PLUS_va(va, k1_vaddr_t);
    // if (t1 != t2) {
    //   return;
    // }
  }
}

//--------------------------------------------------------------------------//
// Measurement API                                                          //
//--------------------------------------------------------------------------//
// Deprecated in measurement proof. Use measurement-self-composed instead.
procedure {:inline 1} measure()
    returns (status : enclave_op_result_t, measurement : measurement_t)
{
    var temp : measurement_t;
    measurement := 0;
    if (!valid_enclave_id(cpu_enclave_id)        ||
        !tap_enclave_metadata_valid[cpu_enclave_id]) {
        status := enclave_op_invalid_arg;
        return;
    }
    call measurement, temp := measure_state_self_composed(
                                    cpu_enclave_id, cpu_enclave_id,
                                    cpu_addr_valid, cpu_addr_valid, 
                                    cpu_addr_map, cpu_addr_map,
                                    tap_enclave_metadata_addr_excl[cpu_enclave_id], 
                                    tap_enclave_metadata_addr_excl[cpu_enclave_id],
                                    cpu_mem, cpu_mem, cpu_regs, cpu_regs,
                                    tap_enclave_metadata_pc[cpu_enclave_id], 
                                    tap_enclave_metadata_pc[cpu_enclave_id], 
                                    tap_enclave_metadata_entrypoint[cpu_enclave_id],
                                    tap_enclave_metadata_entrypoint[cpu_enclave_id],
                                    tap_enclave_metadata_privileged_1[cpu_enclave_id],
                                    tap_enclave_metadata_privileged_2[cpu_enclave_id],
                                    tap_enclave_metadata_owner_map_1,
                                    tap_enclave_metadata_owner_map_2,
                                    tap_enclave_metadata_valid_1,
                                    tap_enclave_metadata_valid_2);
    assert measurement == temp;
    status := enclave_op_success;
}
