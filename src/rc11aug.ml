open AST
open Relation
open EventStructure

let lookup k xs =
  List.find (fun (k', _) -> k = k') xs

let filter_by_ordering orderings events =
  List.filter (fun (_, lab) ->
      try List.mem (strength lab) orderings
      with Invalid_argument _ -> false
    ) events

let intern po rel = rel <&> (po <|> inv po)

let extern po rel = rel <-> (po <|> inv po)

let apply_axioms (les, exns, jst, ppo, rmw, data, addr, ctrl, casdep, jst_hist) =
  let identity ids = List.map (fun id -> (id, id)) ids in
  let reads = List.filter is_read (events les) in
  let writes = List.filter is_write (events les) in
  let write_ids = List.map fst writes in
  let write_rel = rel_of_set write_ids in
  let nas = List.filter is_nonatomic (events les) in
  let na_ids = List.map fst nas in
  let imm_po_loc po = List.filter (fun (a, b) ->
                          let e1 = lookup a (events les) in
                          let e2 = lookup b (events les) in
                          same_location e1 e2
                        ) po in

  let rs_rc11 ids po rf rmw =
    let rs_a = seq write_rel (opt ids (imm_po_loc po)) in
    let rs_b = rtc ids (seq rf rmw) in
    seq rs_a rs_b
  in

  let release_writes = filter_by_ordering [Release] writes in
  let release_write_ids = List.map fst release_writes in

  let fences = List.filter is_fence (events les) in
  let rel_sc_fences = filter_by_ordering [Release; SC] fences in
  let rel_sc_fence_ids = List.map fst rel_sc_fences in
  
  
  let release_rc11 ids po rf rmw =
    let release_a = (rel_of_set release_write_ids) <|> seq (rel_of_set rel_sc_fence_ids) po in
    seq release_a (rs_rc11 ids po rf rmw)
  in
  
  let r_acqs = filter_by_ordering [Acquire] reads in
  let r_acq_ids = List.map fst r_acqs in

  let sw_rc11 ids po rf rmw =
    let acq_sc_fences = filter_by_ordering [Acquire; SC] fences in
    let acq_sc_fence_ids = List.map fst acq_sc_fences in

    let sw_a = seq (release_rc11 ids po rf rmw) rf in
    let sw_b = (rel_of_set r_acq_ids) <|> seq (order les) (rel_of_set acq_sc_fence_ids) in

    seq sw_a sw_b
  in

  let imm_hb_rc11 ids po rf rmw =
    let sw = sw_rc11 ids po rf rmw in
    tc (po <|> sw)
  in
  
  let imm_fr rf co = seq (inv rf) co in

  let imm_eco ids rf co =
    let eco_a = rf in
    let eco_b = seq co (opt ids rf) in
    let eco_c = seq (imm_fr rf co) (opt ids rf) in
    eco_a <|> eco_b <|> eco_c    
  in
  
  let sc_fences = filter_by_ordering [SC] fences in
  let sc_fence_ids = List.map fst sc_fences in

  let imm_psc_rc11 ids po rf co rmw =
    let f = rel_of_set sc_fence_ids in
    let hb = imm_hb_rc11 ids po rf rmw in
    let psc_a = f in
    let psc_b = hb <|> (seq hb (seq (imm_eco ids rf co) hb)) in
    let psc_c = f in

    seq psc_a (seq psc_b psc_c)
  in

  let sloc ids =
    List.filter (fun (a, b) ->
      let e1 = lookup a (events les) in
      let e2 = lookup b (events les) in
      same_location e1 e2) (cross ids ids)
  in

  let race ids po rf rmw =
    let hb = imm_hb_rc11 ids po rf rmw in
    let domain = cross write_ids ids <|> cross ids write_ids in
    let hb' = hb <|> inv hb in
    let na_dom = cross na_ids ids <|> cross ids na_ids in
    (((sloc ids <&> domain) <-> hb') <&> na_dom) <-> (identity ids)
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

  let coherence ids po co rf rmw =
    let hb = imm_hb_rc11 ids po rf rmw in
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

  let no_thin_air po rf =
    acyclic (po <|> rf)
  in

  let rc11_sc ids po rf co rmw =
    acyclic (imm_psc_rc11 ids po rf co rmw)
  in

  let exns =
    List.fold_right (fun (ids, rf, dep, lck, _co, _) acc ->
        (*        Format.fprintf fmt "Execution: %a\n" (pp_list pp_id) ids;*)
        let po = List.filter (fun (a, b) -> List.mem a ids && List.mem b ids) (order les) in
        let writes = List.filter (fun i -> is_write (lookup i (events les))) ids in
        let reads = List.filter (fun i -> is_read (lookup i (events les))) ids in
        let cos = gen_cos writes in
        let co_cands =
          List.fold_right (fun co acc ->
              let r =  rf_completeness rf reads
                       && coherence ids po co rf rmw
                       && atomiciy po rf co rmw
                       (* NOTE: This is our augmentation, replacing po
                       (or 'sb') with dep in the no thin air axiom *)
                       && no_thin_air dep rf
                       && rc11_sc ids po rf co rmw
              in
              if r
              then (co, [
                "hb", transitive_reduction @@ imm_hb_rc11 ids po rf rmw;
                "sw", transitive_reduction @@ sw_rc11 ids po rf rmw;
                "psc", transitive_reduction @@ imm_psc_rc11 ids po rf co rmw;
                "race", race ids po rf rmw
              ]) :: acc
              else acc
            ) cos []
        in
        (*        Format.fprintf fmt "\n";**)
        List.map (fun (co', calc) -> (ids, rf, dep, lck, co', calc)) co_cands @ acc
      ) exns []
  in
  (les, exns, jst, ppo, rmw, data, addr, ctrl, casdep, jst_hist)
