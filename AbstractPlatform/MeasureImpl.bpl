implementation measure_state_self_composed(
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
  // assume false;
  // Loop 2. update digest/measurement by v
  va := k0_vaddr_t;
  while (LT_va(va, kmax_vaddr_t)) 
    invariant ((forall ri : regindex_t :: valid_regindex(ri) ==> (regs1[ri] == regs2[ri])) &&
               pc1 == pc2 && entrypoint1 == entrypoint2 && privileged1 == privileged2      &&
               (forall e : tap_enclave_id_t :: valid_enclave_id_index(e) ==>
                  encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))  &&
               (forall v : vaddr_t :: 
                  LT_va(v, va) ==> 
                      (excl_match(ev1, ev2, v) &&
                      addr_valid_match(ev1, ev2, av1, av2, v) &&
                      private_data_match(ev1, ev2, am1, am2, m1, m2, v)))                  
               ==> (t1 == t2);
    invariant ((exists ri : regindex_t :: valid_regindex(ri) && (regs1[ri] != regs2[ri])) ||
               pc1 != pc2 || entrypoint1 != entrypoint2 || privileged1 != privileged2 ||
               (exists v : vaddr_t :: 
                   LT_va(v, va) && 
                      (!excl_match(ev1, ev2, v) ||
                       !addr_valid_match(ev1, ev2, av1, av2, v) ||
                       !private_data_match(ev1, ev2, am1, am2, m1, m2, v)))                 ||
               (exists e : tap_enclave_id_t :: valid_enclave_id_index(e) &&
                  !encl_owner_map_match(valid1, valid2, ownermap1, ownermap2, e, e1, e2)))
               ==> (t1 != t2);
  {
    t1 := update_digest_virt_addr(av1, am1, ev1, m1, va, t1);
    t2 := update_digest_virt_addr(av2, am2, ev2, m2, va, t2);
    va := PLUS_va(va, k1_vaddr_t);
  }
  t1 := update_digest_virt_addr(av1, am1, ev1, m1, va, t1);
  t2 := update_digest_virt_addr(av2, am2, ev2, m2, va, t2);

  // // Loop 2 with assumption.
  // assume t1 == t2;
  // va := k0_vaddr_t;
  // while (LT_va(va, kmax_vaddr_t))
  //   invariant (forall v : vaddr_t :: 
  //                 (LT_va(v, va) && LT_va(v, kmax_vaddr_t)) ==> 
  //                     (excl_match(ev1, ev2, v) &&
  //                     addr_valid_match(ev1, ev2, av1, av2, v) &&
  //                     private_data_match(ev1, ev2, am1, am2, m1, m2, v)))                  
  //              ==> (t1 == t2);
  //   invariant (exists v : vaddr_t :: 
  //                  (LT_va(v, va) && LT_va(v, kmax_vaddr_t)) && 
  //                     (!excl_match(ev1, ev2, v) ||
  //                      !addr_valid_match(ev1, ev2, av1, av2, v) ||
  //                      !private_data_match(ev1, ev2, am1, am2, m1, m2, v))) 
  //              ==> (t1 != t2);
  // {
  //   t1 := update_digest_virt_addr(av1, am1, ev1, m1, va, t1);
  //   t2 := update_digest_virt_addr(av2, am2, ev2, m2, va, t2);
  //   va := PLUS_va(va, k1_vaddr_t);
  // }
  // t1 := update_digest_virt_addr(av1, am1, ev1, m1, va, t1);
  // t2 := update_digest_virt_addr(av2, am2, ev2, m2, va, t2);

}