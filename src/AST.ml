type value = int [@@deriving show, eq, to_yojson]

type register = string [@@deriving eq, to_yojson]
let show_register r = r
let pp_register fmt r = Format.fprintf fmt "%s" r

type global = string [@@deriving eq, to_yojson]
let show_global g = g
let pp_global fmt g = Format.fprintf fmt "%s" g

type comment = string
let pp_comment fmt c = Format.fprintf fmt "``%s''" c

module Satisfaction_map =
  Map.Make (
      struct
        type t = int
        let compare = Stdlib.compare
      end
    )

type ordering =
    NonAtomic
  | Relaxed
  | Acquire
  | Release
  | SC
[@@deriving eq, to_yojson]

let show_ordering = function
    NonAtomic -> "na"
  | Relaxed -> "rlx"
  | Acquire -> "acq"
  | Release -> "rel"
  | SC -> "sc"

type expr =
    Number of value
  | Register of register
  | Multiplication of expr * expr
  | Division of expr * expr
  | Addition of expr * expr
  | Subtraction of expr * expr

type boolean_expr =
    Equality of expr * expr
  | Gt of expr * expr
  | Lt of expr * expr
  | Gte of expr * expr
  | Lte of expr * expr
  | Conjunction of boolean_expr * boolean_expr
  | Disjunction of boolean_expr * boolean_expr
  | Negation of boolean_expr

(* Required for IMM *)
type exclusivity = Exclusive | NotExclusive [@@deriving eq, to_yojson]

let show_exclusivity = function
    Exclusive -> "ex"
  | NotExclusive -> ""

type rmw_strength = Normal | Strong [@@deriving eq, to_yojson]

let show_rmw_strength = function
    Normal -> "normal"
  | Strong -> "strong"

type ast =
    Skip
  | Assign of register * expr
  | Load of register * global * ordering * exclusivity
  | Store of global * expr * ordering * rmw_strength
  | Fadd of register * global * rmw_strength * ordering * ordering * expr
  | Cas of register * global * ordering * ordering * expr * expr
  | Sequence of ast * ast
  | Parallel of ast * ast
  | Conditional of boolean_expr * ast * ast
  | While of boolean_expr * ast
  | Fence of ordering
  | Print of expr
  | Lock
  | Unlock

type expected_outcome =
  Allow of string
| Forbid of string

type outcome =
  Allowed of boolean_expr * expected_outcome list * comment option
| Forbidden of boolean_expr * expected_outcome list * comment option

let rec show_expr = function
    Number n -> string_of_int n
  | Register r ->
     let reg_no = String.split_on_char 'r' r in
     if List.length reg_no > 1
     then Format.sprintf "\\reg{%s}" (List.nth reg_no 1)
     else Format.sprintf "\\texttt{%s}" r
  | Multiplication (l, r) ->
     Format.sprintf "%s * %s" (show_expr l) (show_expr r)
  | Division (l, r) ->
     Format.sprintf "%s / %s" (show_expr l) (show_expr r)
  | Addition (l, r) ->
     Format.sprintf "(%s + %s)" (show_expr l) (show_expr r)
  | Subtraction (l, r) ->
     Format.sprintf "(%s - %s)" (show_expr l) (show_expr r)


let rec pp_expr fmt = function
    Number n -> Format.fprintf fmt "%d" n
  | Register r -> Format.fprintf fmt "\\texttt{%s}" r
  | Multiplication (l, r) -> Format.fprintf fmt "%a * %a" pp_expr l pp_expr r
  | Division (l, r) -> Format.fprintf fmt "%a / %a" pp_expr l pp_expr r
  | Addition (l, r) -> Format.fprintf fmt "(%a + %a)" pp_expr l pp_expr r
  | Subtraction (l, r) -> Format.fprintf fmt "(%a - %a)" pp_expr l pp_expr r

let rec pp_bexpr fmt = function
    Equality (e1, e2) ->
    Format.fprintf fmt "%a = %a" pp_expr e1 pp_expr e2
  | Gt (e1, e2) ->
    Format.fprintf fmt "%a > %a" pp_expr e1 pp_expr e2
  | Lt (e1, e2) ->
    Format.fprintf fmt "%a < %a" pp_expr e1 pp_expr e2
  | Gte (e1, e2) ->
    Format.fprintf fmt "%a \\geq %a" pp_expr e1 pp_expr e2
  | Lte (e1, e2) ->
    Format.fprintf fmt "%a \\leq %a" pp_expr e1 pp_expr e2
  | Conjunction (b1, b2) ->
    Format.fprintf fmt "(%a \\wedge %a)" pp_bexpr b1 pp_bexpr b2
  | Disjunction (b1, b2) ->
    Format.fprintf fmt "(%a \\vee %a)" pp_bexpr b1 pp_bexpr b2
  | Negation b ->
    Format.fprintf fmt "\neg (%a)" pp_bexpr b

let pp_outcome fmt = function
    Allowed (b, _, _) -> Format.fprintf fmt "allowed: $%a$" pp_bexpr b
  | Forbidden (b, _, _) -> Format.fprintf fmt "forbidden: $%a$" pp_bexpr b

let rec eval_expr p = function
    Number n -> n
  | Register r -> p r
  | Multiplication (l, r) -> eval_expr p l * eval_expr p r
  | Division (l, r) -> eval_expr p l / eval_expr p r
  | Addition (l, r) -> eval_expr p l + eval_expr p r
  | Subtraction (l, r) -> eval_expr p l - eval_expr p r

let rec registers_of_expr = function
    Number _ -> []
  | Register r -> [r]
  | Multiplication (l, r)
    | Division (l, r)
    | Addition (l, r)
    | Subtraction (l, r) ->
     registers_of_expr l @ registers_of_expr r

let rec eval_bexpr p = function
    Equality (e1, e2) -> (eval_expr p e1) = (eval_expr p e2)
  | Gt (e1, e2) -> (eval_expr p e1) > (eval_expr p e2)
  | Lt (e1, e2) -> (eval_expr p e1) < (eval_expr p e2)
  | Gte (e1, e2) -> (eval_expr p e1) >= (eval_expr p e2)
  | Lte (e1, e2) -> (eval_expr p e1) <= (eval_expr p e2)
  | Conjunction (b1, b2) -> eval_bexpr p b1 && eval_bexpr p b2
  | Disjunction (b1, b2) -> eval_bexpr p b1 || eval_bexpr p b2
  | Negation b -> not (eval_bexpr p b)

let rec registers_of_bexpr = function
    Equality (e1, e2)
  | Gt (e1, e2)
    | Lt (e1, e2)
    | Gte (e1, e2)
    | Lte (e1, e2) ->
     registers_of_expr e1 @ registers_of_expr e2
  | Conjunction (b1, b2)
    | Disjunction (b1, b2) ->
     registers_of_bexpr b1 @ registers_of_bexpr b2
  | Negation b -> registers_of_bexpr b

let ntab fmt n =
  let tab_size = 2 in
  Format.fprintf fmt "%*s" (n*tab_size) ""

let pp_ordering fmt o = Format.fprintf fmt "%s" (show_ordering o)
let pp_exclusivity fmt = function
    NotExclusive -> Format.fprintf fmt "not-ex"
  | Exclusive -> Format.fprintf fmt "ex"
let pp_rmw_strength fmt = function
    Normal -> Format.fprintf fmt "normal"
  | Strong -> Format.fprintf fmt "strong"

let rec pp_boolean_expr fmt = function
    Equality (e1, e2) -> Format.fprintf fmt "%a == %a" pp_expr e1 pp_expr e2
  | Gt (e1, e2) -> Format.fprintf fmt "%a > %a" pp_expr e1 pp_expr e2
  | Lt (e1, e2) -> Format.fprintf fmt "%a < %a" pp_expr e1 pp_expr e2
  | Gte (e1, e2) -> Format.fprintf fmt "%a >= %a" pp_expr e1 pp_expr e2
  | Lte (e1, e2) -> Format.fprintf fmt "%a <= %a" pp_expr e1 pp_expr e2
  | Conjunction (e1, e2) -> Format.fprintf fmt "%a ∧ %a" pp_boolean_expr e1 pp_boolean_expr e2
  | Disjunction (e1, e2) -> Format.fprintf fmt "%a ∨ %a" pp_boolean_expr e1 pp_boolean_expr e2
  | Negation e -> Format.fprintf fmt "¬%a" pp_boolean_expr e

let rec show_boolean_expr = function
    Equality (e1, e2) ->
     Format.sprintf "%s = %s" (show_expr e1) (show_expr e2)
  | Gt (e1, e2) ->
     Format.sprintf "%s > %s" (show_expr e1) (show_expr e2)
  | Lt (e1, e2) ->
     Format.sprintf "%s < %s" (show_expr e1) (show_expr e2)
  | Gte (e1, e2) ->
     Format.sprintf "%s \\geq %s" (show_expr e1) (show_expr e2)
  | Lte (e1, e2) ->
     Format.sprintf "%s \\leq %s" (show_expr e1) (show_expr e2)
  | Conjunction (e1, e2) ->
     Format.sprintf "%s \\wedge %s" (show_boolean_expr e1) (show_boolean_expr e2)
  | Disjunction (e1, e2) ->
     Format.sprintf "%s \\vee %s" (show_boolean_expr e1) (show_boolean_expr e2)
  | Negation e -> Format.sprintf "\\neg %s" (show_boolean_expr e)


let rec pp_ast' n fmt = function
    Skip -> Format.fprintf fmt "skip"
  | Assign (r, e) ->
     Format.fprintf fmt "%a%a := %a" ntab n pp_register r pp_expr e
  | Load (r, g, a, e) ->
     Format.fprintf fmt "%a%a := %a.load(%a, %a)"
                    ntab n
                    pp_register r
                    pp_global g
                    pp_ordering a
                    pp_exclusivity e
  | Store (g, e, a, s) ->
     Format.fprintf fmt "%a%a.store(%a, %a, %a)"
                    ntab n
                    pp_global g
                    pp_expr e
                    pp_ordering a
                    pp_rmw_strength s
  | Fadd (r, g, rs, o_r, o_w, e) ->
     Format.fprintf fmt "%a%a := FADD(%a, %a, %a, %a, %a)"
                    ntab n
                    pp_register r
                    pp_global g
                    pp_rmw_strength rs
                    pp_ordering o_r
                    pp_ordering o_w
                    pp_expr e
  | Cas (r, g, o_r, o_w, e1, e2) ->
          Format.fprintf fmt "%a%a := CAS(%a, %a, %a, %a, %a)"
                    ntab n
                    pp_register r
                    pp_global g
                    pp_ordering o_r
                    pp_ordering o_w
                    pp_expr e1
                    pp_expr e2
  | Sequence (a1, a2) -> Format.fprintf fmt "%a;\n%a" (pp_ast' n) a1 (pp_ast' n) a2
  | Parallel (a1, a2) ->
    Format.fprintf fmt "%a{\n%a\n%a} ||| {\n%a\n%a}"
      ntab n
      (pp_ast' (n+1)) a1
      ntab n
      (pp_ast' (n+1)) a2
      ntab n
  | Conditional (c, a1, a2) ->
    Format.fprintf fmt "%aif(%a) {\n%a\n%a}\n%aelse\n%a{\n%a\n%a}"
      ntab n
      pp_boolean_expr c
      (pp_ast' (n+1)) a1
      ntab n  ntab n ntab n
      (pp_ast' (n+1)) a2
      ntab n
  | While (b, a) ->
    Format.fprintf fmt "%awhile(%a) {\n%a\n%a}"
      ntab n
      pp_boolean_expr b
      (pp_ast' (n+1)) a
      ntab n
  | Fence o -> Format.fprintf fmt "%afence(%a)" ntab n pp_ordering o
  | Print e -> Format.fprintf fmt "%aprint(%a)" ntab n pp_expr e
  | Lock -> Format.fprintf fmt "%alock" ntab n
  | Unlock -> Format.fprintf fmt "%aunlock" ntab n

let pp_ast fmt ast = pp_ast' 0 fmt ast

let list_of_pars p =
  let rec go acc = function
    | Parallel (Parallel (p1, p2), p3) ->
       go (p1 :: p2 :: acc) p3
    | Parallel (p1, (Parallel (a, b))) ->
       go (p1 :: acc) (Parallel (a, b))
    | Parallel (p1, p2) ->
       p1 :: p2 :: acc
    | program -> program :: acc
  in
  go [] p

let rec satisfies exec m = function
    Conjunction (b1, b2) -> satisfies exec m b1 && satisfies exec m b2
  | Disjunction (b1, b2)  -> satisfies exec m b1 || satisfies exec m b2
  | Negation b -> not (satisfies exec m b)
  | Equality (Register r, Number v) ->
     Satisfaction_map.exists (fun id' (r', v') ->
         r' = r && v' = v && List.exists (fun id -> id = id') exec
       ) m
  | Gt (Register r, Number v) ->
     Satisfaction_map.exists (fun id' (r', v') ->
         r' = r && v > v' && List.exists (fun id -> id = id') exec
       ) m
  | Gte (Register r, Number v) ->
     Satisfaction_map.exists (fun id' (r', v') ->
         r' = r && v >= v' && List.exists (fun id -> id = id') exec
       ) m
  | Lt (Register r, Number v) ->
     Satisfaction_map.exists (fun id' (r', v') ->
         r' = r && v < v' && List.exists (fun id -> id = id') exec
       ) m
  | Lte (Register r, Number v) ->
     Satisfaction_map.exists (fun id' (r', v') ->
         r' = r && v <= v' && List.exists (fun id -> id = id') exec
       ) m
  | _ -> failwith "todo (apyfu)"
