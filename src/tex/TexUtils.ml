open AST
open Relation
open Common

module type Structure = sig 
  type event 
  val id : event -> int 
  val label : event -> label 
end 

module Make (ES : Structure) = struct 

let pp_id fmt id = Format.fprintf fmt "%d" id 

let remove_symmetric xs =
  List.fold_left (fun acc (x, y) -> if List.mem (y,x) acc then acc else (x,y) :: acc) [] xs

let pc_filter order conflict =
  List.filter (fun (x, y) ->
      let preds_x = List.rev_map fst (List.filter (fun e -> snd e = x) order) in
      let preds_y = List.rev_map fst (List.filter (fun e -> snd e = y) order) in
      List.for_all (fun x' -> not(List.mem (x', y) conflict)) preds_x &&
      List.for_all (fun y' -> not(List.mem (x, y') conflict)) preds_y
  ) conflict

let pp_event jst fmt event =
  let ev_str = match ES.label event with
      R (g, v, _, Relaxed, NotExclusive) -> Format.sprintf "\\readcmd{%s}{%i}" g v
    | R (g, v, _, o, e) ->
      Format.sprintf "\\rocmd{%s}{%s}{%s}{%i}"
                     (show_ordering o)
                     (show_exclusivity e)
                     g
                     v
    | W (g, v, Relaxed, Normal) -> Format.sprintf "\\writecmd{%s}{%i}" g v
    | W (g, v, o, s) ->
       Format.sprintf
         "\\wocmd{%s}{%s}{%s}{%i}" (show_ordering o) (show_rmw_strength s)g v
    | O v -> Format.sprintf "\\printcmd{}{%i}" v
    | F o -> Format.sprintf "\\fencecmd{%s}{}" (show_ordering o)
    | L -> "\\texttt{L}"
    | U -> "\\texttt{U}"
  in
  let style = if List.mem ([], event) jst then "indep" else "basic" in
  Format.fprintf fmt "\\node (%a) [style=%s,label={[style=lab]%d}] {$%s$};\n"
    pp_id (ES.id event) style (ES.id event) ev_str

let pp_edge style pp_a pp_b fmt (a, b) =
  Format.fprintf fmt "  (%a) -- [style=%s] (%a),\n" pp_a a style pp_b b

let pp_tikz_diagram fmt pp_diagram d =
  Format.fprintf fmt "\\begin{center}\n";
  Format.fprintf fmt "\\begin{tikzpicture}[binary tree layout]\n";
  Format.fprintf fmt "%a" pp_diagram d;
  Format.fprintf fmt "\\end{tikzpicture}\n";
  Format.fprintf fmt "\\end{center}\n"

let display_order r = List.sort compare @@ transitive_reduction @@ List.rev r

let display_conf ord cnf  = transitive_reduction @@ remove_symmetric @@ pc_filter ord cnf

let pp_tikz_edge style fmt (a, b) =
  Format.fprintf fmt "\\draw (%a) edge[-,style=%s] (%a);\n" pp_id a style pp_id b



let pp_cnf = pp_tikz_edge "conf"
let pp_rf fmt (a, b) =
  Format.fprintf fmt "\\draw (%a) edge[-,style=rf] node[above]{\\rf} (%a);\n" pp_id a pp_id b

let pp_rmw fmt (a, b) =
  Format.fprintf fmt "\\draw (%a) edge[-,style=rmw, bend left] node[right]{\\rmw} (%a);\n" pp_id a pp_id b

let pp_dep = pp_tikz_edge "dep"
let pp_lck = pp_tikz_edge "lck"
let pp_co = pp_tikz_edge "co"

let pp_just fmt (c, e) =
  List.iter (fun x ->
      Format.fprintf fmt "\\draw (%a) edge[->,style=just, bend left] (%a);\n"
        pp_id (fst x)
        pp_id (fst e)
    ) c

let pp_ppo fmt (a, b) =
  Format.fprintf fmt "\\draw (%a) edge[->,style=ppo, bend left] (%a);\n"
                 pp_id (a)
                 pp_id (b)


let pp_tikz_order fmt r =
  Format.fprintf fmt "\\graph [binary tree layout] {\n";
  List.iter (pp_edge "po" pp_id pp_id fmt) r;
  Format.fprintf fmt "};\n"
end