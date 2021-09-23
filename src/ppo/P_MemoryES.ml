open AST
open Relation
open EventStructure
open Common

type justification = (event set, event) relation [@@deriving to_yojson]

(* Reads from order *)
type rf = (id, id) relation [@@deriving to_yojson]

(* Dependency order *)
type dep = (id, id) relation [@@deriving to_yojson]

(* Lock order *)
type lck = (id, id) relation [@@deriving to_yojson]

(* Coherence order *)
type co = (id, id) relation [@@deriving to_yojson]

(* Calculated relations *)
type calculated_relations = (string * (id, id) relation) list [@@deriving to_yojson]

(* Execution *)
type exn = (id set * rf * dep * lck * co * calculated_relations)

type rmw = (id, id) relation
type data = (id, id) relation
type addr = (id, id) relation
type ctrl = (id, id) relation
type casdep = (id, id) relation
type jst_hist = justification
         
type t = les * exn set * justification * rmw * data * addr * ctrl * casdep * jst_hist

type continuation = (register, value) env -> (register, id) env -> id set -> t

let label_isomorphism l1 l2 =
  match l1, l2 with
    (R (x1, v1, _, o1, e1)), (R (x2, v2, _, o2, e2)) -> x1 = x2 && v1 = v2 && e1 = e2 && o1 = o2
  | (W (x1, v1, o1, s1)), (W (x2, v2, o2, s2)) -> x1 = x2 && v1 = v2 && s1 = s2 && o1 = o2
  | _ -> false

let lookup k xs =
  List.find (fun (k', _) -> k = k') xs

let empty_justification = []
let empty_execution = ([],[],[],[],[], [])
let empty : t = (empty_les, [empty_execution], empty_justification, [], [], [], [], [], [])
let empty_continuation _ _ _ = empty
let empty_environment _ = 0

let freeze_just writes (j : justification) : dep =
  (* For each justification edge C ⊢ e', build a relation with edges
  (r→e') for all reads (r) in C *)
  List.filter
    (fun (a, _) -> not (List.mem a writes))
    (List.flatten (List.map (fun (c, e') -> List.map (fun e -> (id e, id e')) c) j))

let static_ar les casdep =
  let ppo = Imm.imm_ppo les (order les) [] [] casdep in
  let bob = Imm.imm_bob les in
  
  let writes = List.filter is_write (events les) in
  let write_ids = List.map fst writes in
  let strong_writes = List.filter (function _, W (_, _, _, Strong) -> true | _ -> false) writes in
  let s = rel_of_set (List.map fst strong_writes) in
  let ws_po_w = seq s (seq (order les) (rel_of_set write_ids)) in
  
  tc (ppo <|> bob <|> ws_po_w)

  
let covers jst writes : justification list =
  List.map (fun w -> List.filter (fun (_, w') -> w = w') jst) writes

let eq_exn (evs1, rf1, dep1, lck1, co1, _) (evs2, rf2, dep2, lck2, co2, _) =
  List.sort compare evs1 = List.sort compare evs2
  && List.sort compare rf1 = List.sort compare rf2
  && List.sort compare dep1 = List.sort compare dep2
  && List.sort compare lck1 = List.sort compare lck2
  && List.sort compare co1 = List.sort compare co2

let freeze ((es, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist) : t) : t = 
  let execution ((evs, rf, dep, lck, co, _) : exn) : exn list =
    let writes =
      let evs = List.map (fun id -> lookup id (EventStructure.events es)) evs in
      List.filter is_write evs
    in

    
    let ppo_lk = List.filter (fun (a, b) ->
                     is_lock (lookup a (events es)) ||
                       is_unlock (lookup a (events es)) ||
                         is_lock (lookup b (events es)) ||
                           is_unlock (lookup b (events es))
                              
                   ) (order es) in
    
    let covered = List.filter (fun (w, _) -> not(List.exists (fun (_, b) -> w = b) ppo_lk)) writes in

    let (jsts : justification list) = Util.n_cartesian_product (covers jst covered) in
    
    let new_deps =
      List.map (fun jst ->
          freeze_just (List.map fst writes) jst
        ) jsts
    in

    (* If we do not have any new dep edges to build then we'd end up building an [] of executions which is bad. 
       The sensible solution is when we have no augmentations of dep, keep the old exn
     *)
    let r = List.map (fun d' -> (evs, rf, dep <|> d', lck, co, [])) new_deps in
    if r = [] then [evs, rf, dep, lck, co, []] else r
  in
  
  let new_exns = BatList.unique ~eq:eq_exn (List.flatten @@ List.map execution exns) in
  (es, new_exns, empty_justification, rmw, data, addr, ctrl, casdep, jst@jst_hist)

(* Find all events with the same location in the event structure *)
let sloc_events e events =
  List.filter (fun e' -> same_location e e') events

let pre_compose regs psi gamma c (es1, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist) : event -> t = function
  | (i, R _) as r ->
     let es = EventStructure.prefix_event es1 r in
     let exns = List.map (fun (evs, lock, rf, dep, co, _) -> (i::evs, lock, rf, dep, co, [])) exns in
     let iso_reads = List.filter (fun r' -> same_location r r' && same_value r r')
                                 (reads (events es1)) in

     let sar = static_ar es casdep in
     let lb_reads =
       List.filter (fun r' ->
             not (List.exists
                  (fun b -> List.mem (id r, id b) sar && List.mem (id b, id r') sar)
                  (events es)
               )
         ) iso_reads
     in

     let jst = List.map (fun (c, e) -> (r :: (c <-> lb_reads), e)) jst in
     
     let data = (List.fold_right (fun r acc ->
                     try (i, psi r) :: acc
                     with  Not_found -> acc
                   ) regs []) <|> data in

     let casdep_right = List.fold_right (fun r acc -> try psi r :: acc with Not_found -> acc) regs [] in
     let casdep = (BatList.cartesian_product c casdep_right) <|> casdep in
     
     (es, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist)
     
  | (i, W _) as w ->
     let es = EventStructure.prefix_event es1 w in
     let iso_reads = List.filter (fun r -> same_location w r && same_value w r) (reads (events es)) in
     let exns = List.map (fun (evs, lock, rf, dep, co, _) ->
                    (i::evs, lock, rf, dep, co, [])
                  ) exns in
     
     let sar = static_ar es casdep in

     let sb_reads =
       List.filter (fun r' ->
             not (List.exists
                  (fun b -> List.mem (id w, id b) sar && List.mem (id b, id r') sar)
                  (events es)
               )
         ) iso_reads
     in
     
     let ind_just : justification = [([], w)] in
     (* let jst' = List.map (fun (c, e) -> (w :: (List.filter (fun r -> not(List.mem r ppo_reads)) c), e)) jst in *)
     let jst' =
       List.map (fun (c, e) ->
           let c' = c <-> sb_reads in
           c, c', e
         ) jst in

     
     let jst'' = List.map (fun (c, c', e) ->
                     if List.exists (fun e' -> List.mem (id w, id e') sar) c
                     then (w :: c', e)
                     else (c', e)
                   ) jst' in

     let data = (List.fold_right (fun r acc ->
                     try (psi r, i) :: acc
                     with  Not_found -> acc
                   ) regs []) <|> data in
     let ctrl = List.map (fun r -> (r, i)) gamma <|> ctrl in
     
     (es, exns, ind_just <|> jst'', rmw, data, addr, ctrl, casdep, jst_hist)

  | (i, U) | (i, L) as l ->
     let den = es1, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist in
     let es = EventStructure.prefix_event es1 l in
     let (_es1', exn1', _jst1', _rmw, _data, _addr, _ctrl, _casdep, _jst_hist)  = freeze den in
     let exns =
       List.map (fun (evs, _rf, dep, _lck, co, _) ->
           ((i :: evs), [], dep, [], co, [])
         ) exn1'
     in
     (es, exns, empty_justification, rmw, data, addr, ctrl, casdep, jst_hist)

  | (i, F _) as f ->
     let es = prefix_event es1 f in
     let exns = List.map (fun (ids, dep, rf, lck, co, _) -> (i :: ids, dep, rf, lck, co, [])) exns in
     (es, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist)
     
  | _ -> empty


let upclosure es ppo c =
  let candidate_events = events es <-> c in
  let candidate_extensions = powerset candidate_events in (* !! *)
  let candidate_closures = List.map ((<|>) c) candidate_extensions in
  let lock_free =
    List.filter (fun es ->
        List.for_all (function (_, L) |(_,  U) -> false
                               | _ -> true) es
      ) candidate_closures
  in

  let ppo_closed =
    List.filter (fun c ->        
        List.for_all (fun (e'', e') ->
            let idl = List.map fst c in
            if List.mem e' idl then List.mem e'' idl
            else true
          ) ppo
      ) lock_free
  in
  
  let conflict_free =
    List.filter (fun c ->
        List.for_all (fun (e, e') ->
            let idl = List.map fst c in
            not (List.mem e idl) || not(List.mem e' idl)
          ) (cnf es)
      ) ppo_closed
  in

  conflict_free

let restricted_uc (idr, ev) r js =
  match ev with
  | R _ ->
     let ppo_restricted =
       List.filter (fun (c, _e, _, _, _, _, _, _, _) ->
           not (List.exists (fun (ide', _) ->
                  List.mem (idr, ide') r
                ) c)
         ) js
     in
     ppo_restricted
  | _ -> failwith "applying restricted upward closure with a non-read prefixed event! (jkzmf)"

let ctx_label_iso a b =
    List.for_all (fun (_, a') ->
        List.exists (fun (_, b') ->
            label_isomorphism a' b'
          ) b
      ) a

let event_isomorphism (_, l) (_, l') = label_isomorphism l l'

let ap_isomorphism m r =
  try
    let ap r x = snd @@ List.find (fun (a, _) -> a = x) r in
    List.map (fun (x, y) -> ap m x, ap m y) r
  with _ -> []

let is_bijection rel domain range =
  (* There is exactly one edge from each member of the domain, similar with range *)
    List.for_all (fun d -> List.length (List.filter (fun (d', r') -> d = d' && List.mem r' range) rel) = 1) domain
  && List.for_all (fun r -> List.length (List.filter (fun (d', r') -> r = r' && List.mem d' domain) rel) = 1) range

  
let ctx_iso bob bob' c c' =
  let iso_candidates = Util.n_cartesian_product @@ List.map (fun e -> List.map (fun e' -> (e, e')) c') c in
  let isos =
    List.exists (fun iso ->
        List.for_all (fun (a, b) -> event_isomorphism a b) iso
        && (let idl_iso = List.map (fun ((i, _), (i', _)) -> (i, i')) iso in
           ap_isomorphism idl_iso bob = bob')
        && is_bijection iso c c'
      ) iso_candidates
    || equal_set (=) c c'
  in
  isos
  
(* Append a read of location l and prefix a read for each value in the value set onto the continuation *)
(*  val coproduct : value list -> register -> global -> (register, value) env -> continuation -> t *)

let lifting t continuations =
  let _les, _exns, jsts, _rmw, _data, _addr, _ctrl, _casdep, _jst_hist = t in
  let xjustifications =
    Util.n_cartesian_product (
        List.map (fun (ev, (les, _, j, rmw, data, addr, ctrl, casdep, jst_hist)) ->
            List.map (fun (c, e) -> (c, e, ev, les, rmw, data, addr, ctrl, casdep, jst_hist)) j
          ) continuations)
  in

  (* Filters justifications for matched justified events: i.e. 
  { D₁ ⊢₁ e, D₂ ⊢₂ e' | D₁ ⊢ e ∧ D₂ ⊢ e' ∧ e ≅ e'}
   *)
  
  let xjustifications' =
    List.filter (fun js ->
        let (_c, x, _ev, _les, _rmw, _data, _addr, _ctrl, _casdep, _jst_hist) = List.hd js in
        List.for_all (fun (_c', y, _ev, _les, _rmw, _data, _addr, _ctrl, _casdep, _jst_hist) ->
            event_isomorphism x y
          ) js
      ) xjustifications
  in

  (* TODO: this uses the full new coproduced ES rather than the sub ES
  for each branch of the read. This in ineffecient! *)
  let xjustifications'' =
    List.fold_right (fun js acc ->
        let uc_ctxs =
          List.map (fun (c, e, ev, les, rmw, data, addr, ctrl, casdep, jst_hist) ->
              let c = c <-> [ev] in

              (* Note: we take the statically calculable parts of ar here and use them as our ppo
                 relation. This has the effect of ignoring ar edges that would be in place due to
                 rfi and detour. Our semantics does take some account of these edges because it
                 forwards writes in the places where there might be rfi (or detour same value).

                 We argue that the semantics is similar, because we know that where we do write
                 forwarding we can construct an rfi edge, and where we don't write forward there
                 must be some reason not to (e.g. a bob edge, or an intervening read event which
                 would invalidate the irreflexive(hb;eco) axiom.
               *)

              let r = static_ar les casdep in
              let ctxs = upclosure les r c in
              let edges = List.map (fun c -> c, e, les, rmw, data, addr, ctrl, casdep, jst_hist) ctxs in
              restricted_uc ev r edges
            ) js
        in
        let xuc_ctxs = Util.n_cartesian_product uc_ctxs in
        let xuc_ctxs =
          List.filter (fun js ->
              match js with
                (c, _x, les, _, _data, _addr, _ctrl, casdep, _jst_hist) :: js ->
                let r = static_ar les casdep in
                let idl = List.map fst c in
                let r = List.filter (fun (a, b) -> List.mem a idl && List.mem b idl) r in

                List.for_all (fun (c', _y, les', _, _data', _addr', _ctrl', casdep', _jst_hist') ->
                    let r' = static_ar les' casdep' in
                    let idl' = List.map fst c' in
                    let r' = List.filter (fun (a, b) -> List.mem a idl' && List.mem b idl') r' in
                    ctx_iso r r' c c'
                  ) js
              | _ -> true
            ) xuc_ctxs
        in      
        xuc_ctxs <|> acc
      ) xjustifications' [] in

  
  let jsts' = List.fold_right (fun j acc -> j <|> acc) xjustifications'' [] in
  jsts <|> List.map (fun (jst, e, _, _, _, _, _, _, _) -> jst, e) jsts'

let coproduct vs r g o p regs psi gamma c k : t =  
  assert (List.length vs > 1);  
  (* Associates a read event with it's continuation, and the continuation prefixed with the write  *)
  let continuations : (event * t) list =
    List.map (fun v ->
        let ev = fresh_id (), R (g, v, r, o, NotExclusive) in
        let p' = fun r' -> if r = r' then v else p r' in
        let psi' = fun r' -> if r = r' then fst ev else  psi r' in
        let cont = k p' psi' gamma in
        ev, pre_compose regs psi gamma c cont ev
      ) vs
  in
  let (les, exns, _jsts, rmw, data, addr, ctrl, casdep, jst_hist) as t =
    List.fold_right (fun (_, (es, exn, jst, rmw, data, addr, ctrl, casdep, jst_hist))
                       (ess, exns, jsts, rmws, datas, addrs, ctrls, casdeps, jst_hist') ->
        let ess = es_coproduct es ess in
        let exns = exn <|> exns in
        let jsts = jst <|> jsts in
        let rmw = rmw <|> rmws in
        let data = data <|> datas in
        let addr = addr <|> addrs in
        let ctrl = ctrl <|> ctrls in
        let casdep = casdep <|> casdeps in
        let jst_hist = jst_hist @ jst_hist' in
        ess, exns, jsts, rmw, data, addr, ctrl, casdep, jst_hist
      ) continuations (empty_les, [], [], [], [], [], [], [], [])
  in
  let jsts = lifting t continuations in
  (les, exns, jsts, rmw, data, addr, ctrl, casdep, jst_hist)
  
let fadd (w_g, e, w_o, s) vs r g o p regs psi gamma c k : t =
  assert (List.length vs > 1);

  let continuations : (event * rmw * t) list =
    List.map (fun v ->
        let p' = function r' -> if r' = r then v else p r in
        let w_v = v + eval_expr p' e in
        let w_regs = registers_of_expr e in
        let (w_id, _) as write = fresh_id (), W (w_g, w_v, w_o, s) in
        let psi' = function r' -> if r' = r then w_id else psi r in
        (* Denotation with write prefixed *)
        let wp_den = pre_compose w_regs psi' gamma [] (k p psi gamma) write in

        let (r_id, _) as read = fresh_id (), R (g, v, r, o, Exclusive) in
        let psi'' = fun r' -> if r = r' then r_id else psi' r' in
        read, [(r_id, w_id)], pre_compose regs psi'' gamma c wp_den read
      ) vs
  in
  let (les, exns, _jsts, rmw, data, addr, ctrl, casdep, jst_hist) as t =
    List.fold_right (fun (_, rmw', (es, exn, jst, rmw, data, addr, ctrl, casdep, jst_hist))
                       (ess, exns, jsts, rmws, datas, addrs, ctrls, casdeps, jst_hist') ->
        let ess = es_coproduct es ess in
        let exns = exn <|> exns in
        let jsts = jst <|> jsts in
        let rmw = rmw <|> rmw' <|> rmws in
        let data = data <|> datas in
        let addr = addr <|> addrs in
        let ctrl = ctrl <|> ctrls in
        let casdep = casdep <|> casdeps in
        let jst_hist = jst_hist @ jst_hist' in
        ess, exns, jsts, rmw, data, addr, ctrl, casdep, jst_hist
      ) continuations (empty_les, [], [], [], [], [], [], [], [])
  in

  (* Discard the rmw annotation now we're done with it *)
  let continuations = List.map (fun (ev, _, t) -> (ev, t)) continuations in
  let jsts = lifting t continuations in
  (les, exns, jsts, rmw, data, addr, ctrl, casdep, jst_hist)
  
let cas (w_g, e1, e2, w_o, s) vs r g o p regs psi gamma c k =
  let continuations : (event * rmw * casdep * t) list =
    List.map (fun v ->
        let p' = function r' -> if r' = r then v else p r in
        let w_v =  eval_expr p e1 in
        if w_v = eval_expr p e2 then
          let w_regs = registers_of_expr e1 in
          let (w_id, _) as write = fresh_id (), W (w_g, w_v, w_o, s) in
          let psi' = function r' -> if r' = r then w_id else psi r in
          (* Denotation with write prefixed *)
          let wp_den = pre_compose w_regs psi' gamma [] (k p' psi gamma) write in

          let (r_id, _) as read = fresh_id (), R (g, v, r, o, Exclusive) in
          let psi'' = fun r' -> if r = r' then r_id else psi' r' in
          read, [(r_id, w_id)], [(r_id, w_id)], pre_compose regs psi'' gamma c wp_den read

        else
          let (r_id, _) as read = fresh_id (), R (g, v, r, o, Exclusive) in
          let psi' = fun r' -> if r = r' then r_id else psi r' in
          let cont = k p' psi gamma in
          read, [], [], pre_compose regs psi' gamma c cont read
      ) vs
  in
  let (les, exns, _jsts, rmw, data, addr, ctrl, casdep, jst_hist) as t =
    List.fold_right (fun (_, rmw', cas', (es, exn, jst, rmw, data, addr, ctrl, casdep, jst_hist))
                       (ess, exns, jsts, rmws, datas, addrs, ctrls, casdeps, jst_hist') ->
        let ess = es_coproduct es ess in
        let exns = exn <|> exns in
        let jsts = jst <|> jsts in
        let rmw = rmw <|> rmw' <|> rmws in
        let data = data <|> datas in
        let addr = addr <|> addrs in
        let ctrl = ctrl <|> ctrls in
        let casdep = casdep <|> cas' <|> casdeps in
        let jst_hist = jst_hist @ jst_hist' in
        ess, exns, jsts, rmw, data, addr, ctrl, casdep, jst_hist
      ) continuations (empty_les, [], [], [], [], [], [], [], [])
  in

  (* Discard the rmw annotation now we're done with it *)
  let continuations = List.map (fun (ev, _, _, t) -> (ev, t)) continuations in
  let jsts = lifting t continuations in
  (les, exns, jsts, rmw, data, addr, ctrl, casdep, jst_hist)

let product d1 d2 =
  let (es1, exns1, _, rmw1, data1, addr1, ctrl1, casdep1, jst_hist1) = freeze d1 in
  let (es2, exns2, _, rmw2, data2, addr2, ctrl2, casdep2, jst_hist2) = freeze d2 in
  let es = es_product es1 es2 in
  let x1 = List.map (fun (x, _, dep, _, _, _) -> x, dep) exns1 in
  let x2 = List.map (fun (x, _, dep, _, _, _) -> x, dep) exns2 in
  let sf_pairs = BatList.cartesian_product x1 x2 in
  let exns = List.map (fun ((x1, d1), (x2, d2)) -> (x1 <|> x2, [], d1 <|> d2, [], [], [])) sf_pairs in
  (es, exns, empty_justification,
   rmw1 <|> rmw2, data1 <|> data2, addr1 <|> addr2,
   ctrl1 <|> ctrl2, casdep1 <|> casdep2, jst_hist1 @ jst_hist2)

let products (ds : t list) : t =
  let project_es (es, _, _, _, _, _, _, _, _) = es in
  let project_exns ((_, exns, _, _, _, _, _, _, _) : t) = exns in
  let project_jst_hist ((_, _, _, _, _, _, _, _, jst_hist) : t) = jst_hist in
  let frozen = List.map freeze ds in
  let es = List.fold_right es_product (List.map project_es frozen) empty_les in
  let project_exn (x, _, dep, _, _, _) = x, dep in
  let x_d_pairs = List.map (List.map project_exn) (List.map project_exns frozen) in
  let sf_sets = BatList.n_cartesian_product x_d_pairs in
  let exns =
    List.map (fun sf_set ->
        List.fold_right
          (fun (x, d) (xacc, _, dacc, _, _, _) -> x <|> xacc, [], d <|> dacc, [], [], [])
          sf_set
          ([],[],[],[],[],[])
      ) sf_sets
  in
  let jst_hist = List.fold_right (@) (List.map project_jst_hist frozen) [] in
  let rmw, data, addr, ctrl, casdep =
    List.fold_right (fun (_, _, _, rmw, data, addr, ctrl, casdep, _)
                       (rmws, datas, addrs, ctrls, casdeps) ->
        rmw <|> rmws,
        data <|> datas,
        addr <|> addrs,
        ctrl <|> ctrls,
        casdep <|> casdeps
      ) frozen ([], [], [], [], []) in
  (es, exns, empty_justification, rmw, data, addr, ctrl, casdep, jst_hist)

let quantified_rf_lck ((les, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist) : t) : t =
  let lock_order_candidates =
    List.fold_right (fun (ids, rf, dep, _lck, co, _) acc ->
        (* Lock/unlock event ids *)
        let lus = List.filter (fun i ->
                      let ev = lookup i (events les) in
                      is_lock ev || is_unlock ev                                           
                    ) ids in
        let lck_orders = List.map Util.order_of_list (Util.permutations lus) in
        List.map (fun lck -> (ids, rf, dep, lck, co, [])) lck_orders @ acc
      ) exns []
  in

  let rf_candidates =
    List.fold_right (fun (ids, _rf, dep, lock, co, _) acc ->
        let reads =
          List.fold_right (fun i acc ->
              let ev = lookup i (events les) in
              if is_read ev then ev :: acc
              else acc
            ) ids []
        in
        let writes =
          List.fold_right (fun i acc ->
              let ev = lookup i (events les) in
              if is_write ev then ev :: acc
              else acc
            ) ids []
        in

        let wr_sloc_sval = List.fold_right (fun ((id, _lab) as r) acc ->
                let sloc_sval_writes = List.filter (fun w -> same_location r w && same_value r w) writes in
                let res = List.map (fun (id', _lab') -> (id', id)) sloc_sval_writes in
                res :: acc
              ) reads []
        in

        let rf_candidates = List.fold_right (<|>) (List.map (fun rf -> powerset rf) (Util.n_cartesian_product wr_sloc_sval)) [[]] in
        (List.map (fun rf' -> (ids, rf', dep, lock, co, [])) rf_candidates) @ acc
      ) lock_order_candidates [] in
    (les, rf_candidates, jst, rmw, data, addr, ctrl, casdep, jst_hist)

let apply_axioms ((les, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist) : t) : t =
  let _evs, po, conf = les in
  let coherent_executions =
    List.fold_right (fun (ids, rf, dep, lck, _co, _) acc ->
        (* should be conflict free, can probably remove <|> conf *)
        let rfe = List.filter (fun (a, b) -> not(List.mem (a, b) (po <|> conf) || List.mem (b, a) (po <|> conf))) rf in
        let ppo_lk =
          List.filter (fun (a, b) ->
              let eva = lookup a (events les) in
              let evb = lookup b (events les) in 
              ( is_lock eva || is_unlock eva ) && ( is_lock evb || is_unlock evb )
            ) (static_ar les casdep)
        in
        let tc_check = Relation.transitive_closure (dep <|> lck <|> ppo_lk <|> rfe) in
        let com_consistent = List.for_all (fun (a, b) -> a <> b) tc_check in
        let hb = Relation.transitive_closure ~reflexive:true (po <|> lck) in
        let hb_consistent =
          List.for_all (fun (w, r) ->
              not (List.exists (fun r' ->
                     let w_ev = lookup w (events les) in
                     let r_ev = lookup r (events les) in
                     let r'_ev = lookup r' (events les) in
                     same_location w_ev r_ev && same_value w_ev r_ev
                     && same_location r_ev r'_ev
                     && List.mem (w, r') hb
                     && List.mem (r', r) hb
                     && (not (same_value r_ev r'_ev))
                   ) ids)
            ) rf
        in
        if (com_consistent && hb_consistent)
        then (ids, rf, dep, lck, _co, [("hb", hb)])::acc
        else acc
      ) exns []
  in      
  (les, coherent_executions, jst, rmw, data, addr, ctrl, casdep, jst_hist)

let run_map m id =
  try m id with _ -> id
  
let join (es1, exns1, jst1, rmw1, data1, addr1, ctrl1, casdep1, jst_hist1)
         (es2, exns2, _jst2, rmw2, data2, addr2, ctrl2, casdep2, jst_hist2) : t =
  let maps, es = es_sequence es1 es2 in
  let x1 = List.map (fun (x, _, dep, _, _, _) -> x, dep) exns1 in
  let x2 =
    List.flatten @@
      List.map (fun m ->
          let m = run_map m in
          List.map (fun (x, _, dep, _, _, _) ->
              (List.map m x),
              (List.map (fun (a, b) -> m a, m b) dep)
            ) exns2
        ) maps in
  let sf_pairs = BatList.cartesian_product x1 x2 in
  let exns = List.map (fun ((x1, d1), (x2, d2)) -> (x1 <|> x2, [], d1 <|> d2, [], [], [])) sf_pairs in
  
  let order_consistent =
    List.filter (fun (evs, _, _, _, _, _) ->
        List.for_all (fun e ->
            let later = (List.map snd (List.filter (fun (a, _) -> a = e) (order es))) in
            (List.exists (fun e' -> List.mem e' evs) later) || (later = [])
          ) evs
      ) exns in                               
  
  (es, order_consistent, jst1,
   rmw1 <|> rmw2,
   data1 <|> data2,
   addr1 <|> addr2,
   ctrl1 <|> ctrl2,
   casdep1 <|> casdep2,
   jst_hist1 @ jst_hist2
  )

let closed_exns les (exns : exn list) =
  List.filter (fun (exn, rf, _, _, _, _) ->
      let evs = List.map (fun id -> lookup id (EventStructure.events les)) exn in
      List.for_all (fun (rid,_) -> List.exists (fun (_, r') -> rid = r') rf) (reads evs)
    ) exns

  
let check closed outcome (les, exns, _, _, _, _, _, _, _) =
  (* Build a map of read events and ids *)
  let m =
    List.fold_right (fun ev m ->
        match ev with
          id, R (_, v, r, _, _) -> Satisfaction_map.add id (r, v) m
        | _ -> m
      ) (reads (events les)) Satisfaction_map.empty
  in
  
  let contradicting = match outcome with
      Allowed (b, _, _) 
    | Forbidden (b, _, _) -> fun (exec, _, _, _, _, _) -> AST.satisfies exec m b
  in

  if closed
  then closed_exns les (List.filter contradicting exns)
  else List.filter contradicting exns
