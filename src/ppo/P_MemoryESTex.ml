open EventStructure
open Relation
module TU = TexUtils.Make(struct
  type event = EventStructure.event
  let id = EventStructure.project_id
  let label = EventStructure.project_label
end)

let lookup k xs =
  List.find (fun (k', _) -> k = k') xs

let string_of_reln = function
    [] -> "\\emptyset"
  | r -> Format.sprintf "\\{%s\\}" (String.concat ", " (List.map (fun (a, b) -> Format.sprintf "(%d, %d)" a b) r))
          
let pp_jst fmt (_les, exns, jst, rmw, _, _, _, _, _) =
  let jst = List.filter (fun (c, e) -> not(List.mem e c)) jst in
  List.iter (fun (c, e) ->
      let cs =
        List.map (fun (x, _) ->
            string_of_int x
          ) c
      in
      Format.fprintf fmt "$$\\{%s\\} \\vdash %d$$ \n" (String.concat ", " cs) (fst e)
    ) jst;
  Format.fprintf fmt "\\subsection*{Executions}\n";
  let notlock (a, b) =
    let a = lookup a (events _les) in
    let b = lookup b (events _les) in
    (not (is_lock a || is_unlock a)) && (not (is_lock b || is_unlock b))
  in
  List.iter (fun (ids, rf, dep, lck, co, _) ->
      let ss = List.map string_of_int ids in
      let lck = List.filter notlock lck in
      Format.fprintf fmt "$$\n";
      Format.fprintf fmt "\\begin{aligned}\n";
      Format.fprintf fmt "E = \\{%s\\} \\qquad " (String.concat ", " ss);
      Format.fprintf fmt "& \\rf = %s \\\\\ \n " (string_of_reln rf);
      Format.fprintf fmt "& \\dep = %s \\\\ \n" (string_of_reln dep);
      Format.fprintf fmt "& \\lck = %s \\\\ \n" (string_of_reln lck);
      Format.fprintf fmt "& \\co = %s \\\\ \n" (string_of_reln (Relation.transitive_reduction co));
      Format.fprintf fmt "& \\rmw = %s \\\\ \n" (string_of_reln rmw);
      Format.fprintf fmt "\\end{aligned}\n";
      Format.fprintf fmt "$$\n"
    ) exns

let pp_tex' fmt (es, _, jst, rmw, _, _, _, _, _) =
  List.iter (TU.pp_event jst fmt) (List.sort (fun (x, _) (y, _) ->  compare x y) (events es));
  Format.fprintf fmt "%a" TU.pp_tikz_order (TU.display_order (order es));
  (*
  let ppo =
    List.filter (fun (a, b) ->
        let a = lookup a (events es) in
        let b = lookup b (events es) in
        (not (is_lock a || is_unlock a)) && (not (is_lock b || is_unlock b))
      ) ppo
  in
  List.iter (TU.pp_ppo fmt) (Relation.transitive_reduction ppo); *)
  List.iter (TU.pp_rmw fmt) rmw;
  List.iter (TU.pp_cnf fmt) (TU.display_conf (order es) (cnf es))

let pp_tex fmt es =
  TU.pp_tikz_diagram fmt pp_tex' es;
  let _, _, _, _, data, _, ctrl, _, _ = es in
  Format.fprintf fmt "$$data \\cup ctrl = \\{ %a \\}$$"
                 (pp_list (pp_pair pp_id)) (data <|> ctrl)


let pp_con_tex' fmt ((es, _, jst, rmw, _, _, _, _, _), con) =
  let pp_just fmt (c, ((id_e, _) as e)) =	
    List.iter (fun ((id_x, _) as x) ->	
        if List.mem id_x con && List.mem id_e con	
        then Format.fprintf fmt "\\draw (%a) edge[->,style=just, bend left] (%a);\n"
            pp_id (fst x)	
            pp_id (fst e)	
      ) c;	
  in	
  List.iter (TU.pp_event jst fmt)
    (List.sort (fun (x, _) (y, _) ->  compare x y)
       (List.filter (fun (x, _) -> List.mem x con) (events es)));
  TU.pp_tikz_order fmt
    (List.filter
       (fun (x, y) -> List.mem x con && List.mem y con)
       (TU.display_order (order es)));
  List.iter (pp_just fmt) jst;
  List.iter (TU.pp_rmw fmt) rmw;
  List.iter (TU.pp_cnf fmt)
    (List.filter
       (fun (x, y) -> List.mem x con && List.mem y con)
       (TU.display_conf (order es) (cnf es)))

let pp_con_tex fmt es con =
  TU.pp_tikz_diagram fmt pp_con_tex' (es, con);
  let _, _, _, _, data, _, ctrl, _, _ = es in
  Format.fprintf fmt "$$data \\cup ctrl = \\{ %a \\}$$"
                 (pp_list (pp_pair pp_id)) (data <|> ctrl)

let pp_exn_tex' fmt ((es, _, jst, _, _, _, _, _, _), (evs, rf, dep, lck, co, _)) =
  let pp_just fmt (c, ((id_e, _) as e)) =	
    List.iter (fun ((id_x, _) as x) ->	
        if List.mem id_x evs && List.mem id_e evs
        then Format.fprintf fmt "\\draw (%a) edge[->,style=just, bend left] (%a);\n"
            pp_id (fst x)	
            pp_id (fst e)	
      ) c;	
  in	
  List.iter (TU.pp_event jst fmt)
    (List.sort (fun (x, _) (y, _) ->  compare x y)
       (List.filter (fun (x, _) -> List.mem x evs) (events es)));
  TU.pp_tikz_order fmt
    (List.filter
       (fun (x, y) -> List.mem x evs && List.mem y evs)
       (TU.display_order (order es)));
  List.iter (pp_just fmt) jst;
  List.iter (TU.pp_cnf fmt)
    (List.filter
       (fun (x, y) -> List.mem x evs && List.mem y evs)
       (TU.display_conf (order es) (cnf es)));
  List.iter (TU.pp_rf fmt) rf;
  List.iter (TU.pp_dep fmt) dep;
  List.iter (TU.pp_lck fmt) lck;
  List.iter (TU.pp_co fmt) co
                         
let pp_exn_tex fmt es exn = TU.pp_tikz_diagram fmt pp_exn_tex' (es, exn)
                          
let pp_begin_tex fmt =
  Format.fprintf fmt "\\begin{document}\n"

let pp_end_tex fmt =
  Format.fprintf fmt "\\end{document}\n"
