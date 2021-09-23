open AST
open EventStructure
open Relation

(* let acceptable es rf ctx_ord = *)

(* { (id, id') | id' ∈ d } *)
let prefix_rel id d = List.map (fun (id', _) -> (id, id')) d

let order_extension es e tri weak =
  let evs = events es in
  match e with
    id, R (x, v) ->
    let tri_before = List.filter (function
        | _, F SC -> true
        | _, F _ -> false
        | (_, ev) -> location ev = x) evs in
    let tri'= prefix_rel id tri_before in

    let weak_before = List.filter (function
        | _, F Release
        | _, F Acquire -> true
        | _ -> false
      ) evs in
    let weak'= prefix_rel id weak_before in
    (tri <|> tri', weak <|> weak')

  | id, W (x, v) ->
    let tri_before = List.filter (function
          _, F SC -> true
        | _, F _ -> false
        | (_, ev) -> location ev = x) evs in
    let tri'= prefix_rel id tri_before in

    let weak_before = List.filter (function
        | _, F Release -> true
        | _ -> false) evs in
    let weak'= prefix_rel id weak_before in
    (tri <|> tri', weak <|> weak')

  | id, F Release | id, F Acquire ->
    let weak_before = List.filter (function
        | _, W _ -> true
        | _ -> false) evs in
    let weak'= prefix_rel id weak_before in
    (tri, weak <|> weak')

  | id, F SC ->
    let tri' = prefix_rel id evs in
    (tri <|> tri', weak)

  | _, O _ -> (tri, weak)
