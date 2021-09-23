open AST
open Relation
open EventStructure
open Common

let lookup k xs =
  List.find (fun (k', _) -> k = k') xs

let filter_by_ordering orderings events =
  List.filter (fun (_, lab) ->
      try List.mem (strength lab) orderings
      with Invalid_argument _ -> false
    ) events

let intern po rel = rel <&> (po <|> inv po)

let extern po rel = rel <-> (po <|> inv po)

let imm_bob les =
  let po = order les in
  let reads = List.filter is_read (events les) in
  let writes = List.filter is_write (events les) in
  let write_ids = List.map fst writes in
  let release_writes = filter_by_ordering [Release] writes in
  let release_write_ids = List.map fst release_writes in
  let fences = List.filter is_fence (events les) in
  let fence_ids = List.map fst fences in
  let acquire_reads = filter_by_ordering [Acquire] reads in
  let acquire_read_ids = List.map fst acquire_reads in
  let imm_po_loc po = List.filter (fun (a, b) ->
                          let e1 = lookup a (events les) in
                          let e2 = lookup b (events les) in
                          same_location e1 e2
                        ) po in


  let bob_a = seq po (rel_of_set release_write_ids) in
  let bob_b = seq (rel_of_set acquire_read_ids) po in
  let bob_c = seq po (rel_of_set fence_ids) in
  let bob_d = seq (rel_of_set fence_ids) po in
  let bob_e = seq (rel_of_set release_write_ids) (seq (imm_po_loc po) (rel_of_set write_ids)) in
  bob_a <|> bob_b <|> bob_c <|> bob_d <|> bob_e

let imm_deps les po dep casdep =
  let reads = List.filter is_read (events les) in
  let ids = List.map fst (events les) in
  let addr = [] in
  let deps_a = dep in
  let deps_b = seq addr (opt ids po) in
  let deps_c = casdep in

  let exclusive_reads = List.filter (function _, R (_, _, _, _, Exclusive) -> true | _ -> false) reads in
  let exclusive_read_ids = List.map fst exclusive_reads in

  let deps_d = seq (rel_of_set exclusive_read_ids) po in
  
  deps_a <|> deps_b <|> deps_c <|> deps_d

let imm_ppo les po rf dep casdep =
  let reads = List.filter is_read (events les) in
  let read_ids = List.map fst reads in
  let writes = List.filter is_write (events les) in
  let write_ids = List.map fst writes in
  let rfi = intern po rf in
  let imm_ppo_inner = tc ((imm_deps les po dep casdep) <|> rfi) in
  seq (rel_of_set read_ids) (seq imm_ppo_inner (rel_of_set write_ids))

                  
let apply_axioms (les, exns, jst, ppo, rmw, data, addr, ctrl, casdep, jst_hist) =
  let reads = List.filter is_read (events les) in
  let read_ids = List.map fst reads in
  let writes = List.filter is_write (events les) in
  let write_ids = List.map fst writes in
  let write_rel = rel_of_set write_ids in
  let imm_po_loc po = List.filter (fun (a, b) ->
                          let e1 = lookup a (events les) in
                          let e2 = lookup b (events les) in
                          same_location e1 e2
                        ) po in

  let rs ids po rf =
    let rs_a =  seq write_rel  (seq (imm_po_loc po) write_rel) in
    let rs_b = seq (rel_of_set write_ids) (rtc ids (seq (imm_po_loc po) (seq rf rmw))) in
    rs_a <|> rs_b
  in

  let release_writes = filter_by_ordering [Release] writes in
  let release_write_ids = List.map fst release_writes in

  let fences = List.filter is_fence (events les) in
  let rel_sc_fences = filter_by_ordering [Release; SC] fences in
  let rel_sc_fence_ids = List.map fst rel_sc_fences in
  
  
  let release ids po rf =
    let release_a = (rel_of_set release_write_ids) <|> seq (rel_of_set rel_sc_fence_ids) po in
    seq release_a (rs ids po rf)
  in
  
  let r_acqs = filter_by_ordering [Acquire] reads in
  let r_acq_ids = List.map fst r_acqs in

  let sw ids po rf =
    let acq_sc_fences = filter_by_ordering [Acquire; SC] fences in
    let acq_sc_fence_ids = List.map fst acq_sc_fences in
    
    let rfi = intern po rf in
    let rfe = extern po rf in
    
    let sw_a = release ids po rf in
    let sw_b = rfi <|> seq (opt ids (imm_po_loc po)) rfe in
    let sw_c = (rel_of_set r_acq_ids) <|> seq po (rel_of_set acq_sc_fence_ids) in

    seq sw_a (seq sw_b sw_c)
  in

  let imm_hb ids po rf =
    let sw = sw ids po rf in
    tc (po <|> sw)
  in
  
  let imm_fr rf co = seq (inv rf) co in

  let imm_eco ids rf co =
    let eco_a = rf in
    let eco_b = seq co (opt ids rf) in
    let eco_c = seq (imm_fr rf co) (opt ids rf) in
    eco_a <|> eco_b <|> eco_c    
  in

  let acquire_reads = filter_by_ordering [Acquire] reads in
  let acquire_read_ids = List.map fst acquire_reads in
  let fence_ids = List.map fst fences in
  
  let imm_bob po =
    let bob_a = seq po (rel_of_set release_write_ids) in
    let bob_b = seq (rel_of_set acquire_read_ids) po in
    let bob_c = seq po (rel_of_set fence_ids) in
    let bob_d = seq (rel_of_set fence_ids) po in
    let bob_e = seq (rel_of_set release_write_ids) (seq (imm_po_loc po) (rel_of_set write_ids)) in
    bob_a <|> bob_b <|> bob_c <|> bob_d <|> bob_e
  in

  let imm_deps ids po dep casdep =
    let addr = [] in
    let deps_a = dep in
    let deps_b = seq addr (opt ids po) in
    let deps_c = casdep in

    let exclusive_reads = List.filter (function _, R (_, _, _, _, Exclusive) -> true | _ -> false) reads in
    let exclusive_read_ids = List.map fst exclusive_reads in

    let deps_d = seq (rel_of_set exclusive_read_ids) po in
    
    deps_a  <|> deps_b <|> deps_c <|> deps_d
  in
  

  let imm_ppo ids po rf dep casdep =
    let rfi = intern po rf in
    let imm_ppo_inner = tc ((imm_deps ids po dep casdep) <|> rfi) in
    seq (rel_of_set read_ids) (seq imm_ppo_inner (rel_of_set write_ids))
  in

  let imm_detour po rf co =
    let coe = extern po co in
    let rfe = extern po rf in
    (seq coe rfe) <&> (order les)
  in

  let sc_fences = filter_by_ordering [SC] fences in
  let sc_fence_ids = List.map fst sc_fences in
  let imm_psc ids po rf co =
    let f = rel_of_set sc_fence_ids in
    let hb = imm_hb ids po rf in
    seq f (seq hb (seq (imm_eco ids rf co) (seq hb f)))
  in
  
  let imm_ar ids po co rf dep casdep =
    let rfe = extern po rf in
    let strong_writes = List.filter (function _, W (_, _, _, Strong) -> true | _ -> false) writes in
    let s = rel_of_set (List.map fst strong_writes) in
    let ws_po_w = seq s (seq po (rel_of_set write_ids)) in
    let bob = imm_bob po in
    let ppo = imm_ppo ids po rf dep casdep in
    let detour = imm_detour po rf co in
    let psc = imm_psc ids po rf co in
    rfe <|> bob <|> ppo <|> detour <|> psc <|> ws_po_w
  in
  
  let rf_completeness rf reads =
    equal_set (=) (List.map (fun (_, r) -> r) rf) reads
  in
  
  let gen_cos writes =
    let write_labels = List.map (fun i -> snd @@ lookup i (events les)) writes in
    let locations = BatList.unique ~eq:(=) @@ List.map location write_labels in
    let sloc_writes : id list list =
      List.map (fun loc ->
          List.filter (fun i -> location (snd @@ lookup i (events les)) = loc) writes
        ) locations
    in
    let sloc_write_orders =
      List.map (fun (sloc_writes : id list) ->
          List.map Util.order_of_list (Util.permutations sloc_writes)
        ) sloc_writes
    in

    let co_tuple = Util.n_cartesian_product sloc_write_orders in
    List.map List.flatten co_tuple
  in

  let coherence ids po co rf =
    let hb = imm_hb ids po rf in
    let eco = imm_eco ids rf co in
(*    Format.fprintf fmt "hb = %a\n" (pp_list (pp_pair pp_id)) hb;
    Format.fprintf fmt "eco = %a\n" (pp_list (pp_pair pp_id)) eco;*)
    irreflexive (seq hb (opt ids eco))
  in

  let atomiciy po rf co rmw =
    let fre = extern po (imm_fr rf co) in
    let coe = extern po co in
    equal_set (=) (rmw <&> (seq fre coe)) []
  in

  let no_thin_air ids po co rf dep casdep =
    let ar =  (imm_ar ids po co rf dep casdep) in
    acyclic ar
  in
  
  let exns =
    List.fold_right (fun (ids, rf, dep, lck, _co, _) acc ->
        let po = List.filter (fun (a, b) -> List.mem a ids && List.mem b ids) (order les) in
        let writes = List.filter (fun i -> is_write (lookup i (events les))) ids in
        let reads = List.filter (fun i -> is_read (lookup i (events les))) ids in
        let cos = gen_cos writes in
        let co_cands =
          List.filter (fun co ->
              let r =  rf_completeness rf reads
                       && coherence ids po co rf
                       && atomiciy po rf co rmw
                       && no_thin_air ids po co rf (ctrl <|> addr <|> data) casdep
              in
              r
            ) cos
        in
        (*        Format.fprintf fmt "\n";**)
        List.map (fun co' -> (ids, rf, dep, lck, co', [])) co_cands @ acc
      ) exns []
  in
  (les, exns, jst, ppo, rmw, data, addr, ctrl, casdep, jst_hist)
