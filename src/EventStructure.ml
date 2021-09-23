open AST
open Relation
open Common

type id = int
[@@deriving show, eq, to_yojson]

(* λ ≅ id -> label *)
type event = id * label
[@@deriving show, eq, to_yojson]

let project_id = fst
let project_label = snd

(* ε ⊆ (E, ⊑, #, λ) *)
(* Note that the event set is a list of pairs, id×label. *)
type les = event set * (id, id) relation * (id, id) relation
[@@deriving show]

let empty_les = ([], [], [])

let pp_label fmt = function
    R (g, v, _, o,  _) -> Format.fprintf fmt "(R_%a %a %a)" pp_ordering o pp_global g pp_value v
  | W (g, v, o, _) -> Format.fprintf fmt "(W_%a %a %a)" pp_ordering o pp_global g pp_value v
  | F o -> Format.fprintf fmt "(F %a)" pp_ordering o
  | O v -> Format.fprintf fmt "print(%a)" pp_value v
  | L -> Format.fprintf fmt "lock"
  | U -> Format.fprintf fmt "unlock"

let pp_event fmt (id, lab) = Format.fprintf fmt "[%a: %a]" pp_id id pp_label lab

let fresh_id =
  let id = ref 0 in
  function () -> incr id; !id

let events (es, _, _) = es
let order (_, ord, _) = ord
let cnf (_, _, cnf) = cnf

let location = function
    R (l, _, _, _, _)
  | W (l, _, _, _) -> l
  | F _ -> raise (Invalid_argument "fences do not have a location (qltpm)")
  | O _ -> raise (Invalid_argument "observables do not have a location (zwjxx)")
  | L | U -> raise (Invalid_argument "locks and unlocks do not have a location (zpcub)")
          
let value = function
    R (_, v, _, _, _)
  | W (_, v, _, _)
  | O v -> v
  | F _ | L | U -> raise (Invalid_argument "fences/locks/unlocks do not have a value (cglvz)")

let strength = function
    O _ | L | U ->
   raise (Invalid_argument "obervables/locks/unlocks do not have a strength (awfnj)")
  | F o | R (_, _, _, o, _) | W (_, _, o, _) -> o
        
let is_write = function _, (W _) -> true | _ -> false
let is_read = function _, (R _) -> true | _ -> false
let is_fence = function _, (F _) -> true | _ -> false
let is_lock = function _, L -> true | _ -> false
let is_unlock = function _, U -> true | _ -> false
let is_nonatomic = function _, (W (_, _, NonAtomic, _)) -> true | _, (R (_, _, _, NonAtomic, _)) -> true | _ -> false

let same_value (_, a) (_, b) = value a = value b
let same_location a b =
  if (is_write a || is_read a) && (is_write b || is_read b)
  then (location (snd a) = location (snd b))
  else false

let writes = List.filter is_write
let reads = List.filter is_read

(* config ∈ Con(E) *)
let con ((_es, _ord, cnf): les) (config: event set) : bool =
  let config = List.rev_map fst config in
  not(List.exists (fun x -> List.mem x cnf) (cross config config))

let max_con (es: les) c =
  let ids = (List.rev_map fst (events es)) in
  not(List.exists (fun x -> List.mem x (cnf es)) (cross c c)) &&
  List.for_all (fun (x,y) ->
      List.mem x c ||
      List.mem y c ||
      List.exists (fun z -> List.mem (x,z) (cnf es)) c
    ) (cross ids ids)

let label (es, _, _) id =
  let (_, label) = List.find (fun (id', _) -> id' = id) es in
  label

let id (id, _lab) = id

let es_product (es1, ord1, cnf1) (es2, ord2, cnf2) =
  (es1 <|> es2, ord1 <|> ord2, cnf1 <|> cnf2)

let es_products less = List.fold_right es_product less empty_les

let es_coproduct (es1, ord1, cnf1) (es2, ord2, cnf2) =
  let ids1 = List.rev_map fst es1 in
  let ids2 = List.rev_map fst es2 in
  let cnf' = cnf1 <|> cnf2 <|> (cross ids1 ids2) <|> (cross ids2 ids1) in
  (es1 <|> es2, ord1 <|> ord2, cnf')
  
let mk_idmap ids : id -> id =
  List.fold_left (fun acc x ->
      let new_id = fresh_id () in
      (fun id -> if id = x then new_id else acc id)
    ) (fun _ -> raise Not_found) ids

let es_relabel ((evs, ord, cnf) : les) : ((id -> id) * les)  =
  let idmap = mk_idmap (List.rev_map fst evs) in
  let evs' = List.rev_map (fun (id, lab) -> idmap id, lab) evs in
  let ord' = List.rev_map (fun (l, r) -> idmap l, idmap r) ord in
  let cnf' = List.rev_map (fun (l, r) -> idmap l, idmap r) cnf in
  idmap, (evs', ord', cnf')

let es_products (ess: les list) : les =
  Util.fold_left_pairwise es_product ess

let prefix_event ((evs, ord, cnf): les) ev =
  assert (not (List.mem ev evs));
  let eids = List.rev_map fst evs in
  (evs <|> [ev], ord <|> (cross [fst ev] eids), cnf)

let maximal d rs =
  List.filter (fun e -> not(List.mem e (List.rev_map fst rs))) d

let test_maximal _ = 
  let data = [
    (1,2); (2,3); (3,4)
    ; (2,5); (5,6)
  ] in
  OUnit2.assert_bool "maximal data" (equal_set (=) [4;6] (maximal [1;2;3;4;5;6] data))

let leaves (evs, ord, _) = maximal (List.map fst evs) ord

(* Make a list of all elements each set member is related to, sort
   those lists, then de-dupe *)
(** Note: eq_rel is assumed to be reflexive, transitive & symmetric *)
let partition_by_rel (eq_rel : ('a, 'a) relation) (xs: 'a set) =  
  let equivs: int list list = List.fold_left (fun acc x ->
      acc @ [List.rev_map snd (List.filter (fun (y, _) -> x = y) eq_rel)]
    ) [] xs in
  let equivs = List.rev_map (List.sort compare) equivs in
  let equivs = List.filter (fun l -> List.length l > 0) equivs in
  let singletons =
    List.map (fun x -> [x]) @@
    List.filter (fun x -> not (List.exists (fun (e, e') -> e = x || e' = x) eq_rel)) xs in
  BatList.unique (equivs <|> singletons)

let es_sequence (es1 : les) (es2 : les) =
  let es1_leaves = List.sort compare @@ leaves es1 in
  let conflicted_parts = partition_by_rel (Relation.transitive_closure (cnf es1)) (es1_leaves) in
  let conflicted_parts = List.map ((<&>) es1_leaves) conflicted_parts in
  
  (* Represents all the conflict-free sets you could construct from
  the leaves of es1 *)
  let cf_subsets = BatList.n_cartesian_product conflicted_parts in
  
  (* For each member of the new_edges set, build a relabeled es2 and
  associate it with the conflict free subset *)
  let new_ess = List.rev_map (fun cf_subset -> (cf_subset, es_relabel es2)) cf_subsets in

  let es3 = Util.fold_left_pairwise es_coproduct (List.map (fun (_, (_, es)) -> es) new_ess) in
  let id_maps = List.map (fun (_, (m, _)) -> m) new_ess in

  let cf_ords = List.fold_right (fun (cf_subset, (_, es2)) acc ->
                    BatList.cartesian_product cf_subset (List.map fst (events es2)) @ acc
                  ) new_ess [] in

  
  let e3 = (events es1) <|> (events es3) in
  let ord3 : (id * id) set = transitive_closure (cf_ords <|> (order es1) <|> (order es3)) in
  let cnf3 = (cnf es1) <|> (cnf es3) in
  id_maps, (e3, ord3, cnf3)
  
let es_configurations es =
  List.filter (fun c -> max_con es c) (powerset (List.rev_map fst (events es)))

let test_partition_by_rel _ =
  let rel =
    [ (1,1); (2,2); (3,3); (4,4); (5,5); (6,6)
    ; (1,2)
    ; (2,1)
    ; (3,4); (4,5); (3,5)
    ; (4,3); (5,4); (5,3) ]
  in
  let expected : id set set = [[1;2]; [3;4;5]; [6]] in
  let result = partition_by_rel rel [1;2;3;4;5;6] in
  OUnit2.assert_bool "partition result" (equal_set (equal_set equal_id) expected result)

let suite = OUnit2.(
  "event structure tests" >:::
  [ "maximal operator" >:: test_maximal
  ; "parition by equivilence relation" >:: test_partition_by_rel
  ]
  )

let test () = OUnit2.run_test_tt_main suite

let final_register_values = fun les ->
  let (_, po, _) = les in
  let l =
    List.fold_right (fun ev l ->
      match ev with
      | id, R (_, v, r, _, _) ->
        (* Don't add event if it's proceeded by (according to po) an existing event which reads to the same register *)
        if List.exists (fun (id', r', _) -> r' = r && List.exists (fun (a, b) -> a = id && b =id') po) l
        then l
        else
          let l' =
            List.filter (fun (id', r', _) ->
              (* Filter out events that read to the same register and which precede the matched event according to po *)
              not (r' = r && (List.exists (fun (a, b) -> a = id' && b = id) po))
            ) l
          in (id, r, v)::l'
      | _ -> l
    ) (reads (events les)) []
  in l