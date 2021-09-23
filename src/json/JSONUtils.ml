open AST
open Relation
open EventStructure

type les_record = {
    event_list : event list;
    po_relation : (id, id) relation;
    conflict_relation : (id, id) relation;
} [@@deriving to_yojson]

type exn_record = {
    event_id_list : id set;
    relations : (string * (id, id) relation) list;
    final_reg_vals : (id * register * value) set;
} [@@deriving to_yojson]

(* type justification_history = ((id list) * id) list [@@deriving to_yojson] *)

let remove_symmetric xs =
  List.fold_left (fun acc (x, y) -> if List.mem (y,x) acc then acc else (x,y) :: acc) [] xs

let pc_filter order conflict =
  List.filter (fun (x, y) ->
      let preds_x = List.rev_map fst (List.filter (fun e -> snd e = x) order) in
      let preds_y = List.rev_map fst (List.filter (fun e -> snd e = y) order) in
      List.for_all (fun x' -> not(List.mem (x', y) conflict)) preds_x &&
      List.for_all (fun y' -> not(List.mem (x, y') conflict)) preds_y
  ) conflict

let les_to_les_record (es, ord, cnf) = {
    event_list = es;
    po_relation = Relation.transitive_reduction ord;
    conflict_relation = Relation.transitive_reduction @@ remove_symmetric @@ pc_filter ord cnf;
    }

let exn_to_exn_record (ids, rf, dep, lck, co, calculated_rel) les = 
    let reg_states = final_register_values les in
    let exn_filtered_reg_states = List.filter (fun (id, _, _) -> List.exists (fun id' -> id = id') ids) reg_states in
    {
        event_id_list = ids;
        relations = [
            ("rf", rf);
            ("dep", dep);
            ("lck", lck);
            ("co", co)
        ] @ calculated_rel;
        final_reg_vals = exn_filtered_reg_states;
    }


