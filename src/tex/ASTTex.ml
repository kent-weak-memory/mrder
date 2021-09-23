open AST

let rec repeat x = function
    0 -> []
  | n -> x :: repeat x (n-1)

let rec show_ast_tex ast =
  let rec go = function
    Skip -> "& \\done"
  | Assign (r, e) ->
     Format.sprintf "& \\assign[]{%s}{%s}" (show_register r) (show_expr e)
  | Load (r, g, a, _) ->
     Format.sprintf "& \\assign[%s]{%s}{%s}"
                    (show_ordering a)
                    (show_register r)
                    (show_global g)
  | Store (r, e, a, _) ->
     Format.sprintf "& \\assign[%s]{%s}{%s}"
                    (show_ordering a)
                    (show_register r)
                    (show_expr e)
  | Fadd (r, g, rs, o_r, o_w, e) ->
     Format.sprintf "& \\assign[]{%s}\\texttt{FADD}(%s, %s, %s, %s, %s)"
                    (show_register r)
                    (show_global g)
                    (show_rmw_strength rs)
                    (show_ordering o_r)
                    (show_ordering o_w)
                    (show_expr e)
  | Cas (r, g, o_r, o_w, e1, e2) ->
     Format.sprintf "& \\assign[]{%s}\\texttt{CAS}(%s, %s, %s, %s, %s)"
                    (show_register r)
                    (show_global g)
                    (show_ordering o_r)
                    (show_ordering o_w)
                    (show_expr e1)
                    (show_expr e2)
  | Sequence (p1, p2) ->
     Format.sprintf "%s \\sequencing \\\\ \n %s"
                    (go p1)
                    (go p2)
  | Parallel (_,_) as prog ->
     let ps = list_of_pars prog in
     let cols = (List.length ps * 2) - 1 in
     let cols_spec = String.concat "" (repeat "c" cols) in
     let cols_content =
       String.concat
         "\n& || &\n"
         (
           List.map show_ast_tex ps
         )
     in
     Format.sprintf "\\begin{array}{%s}\n%s\n\\end{array}"
                      cols_spec
                      cols_content

  | Conditional (c, p1, p2) ->
    (match p2 with
        Skip ->
         Format.sprintf "& \\ifthen{%s}{%s}"
           (show_boolean_expr c) (show_ast_tex p1)
      | _ ->
         Format.sprintf "& \\ifthenelse{%s}{%s}{%s}"
           (show_boolean_expr c)
           (show_ast_tex p1)
           (show_ast_tex p2)
    )
  | While (c, p) ->
     Format.sprintf "& \\while{%s}{%s}" (show_boolean_expr c) (show_ast_tex p)
  | Fence (o) -> Format.sprintf "& fence(%s)" (show_ordering o)
  | Lock -> "lock"
  | Unlock -> "unlock"
  | Print (e) -> Format.sprintf "& print(%s)" (show_expr e)
  in
  Format.sprintf "\\begin{aligned}\n%s\n\\end{aligned}" (go ast)

let pp_ast_tex' fmt ast =
  let rec go fmt = function
    Skip -> Format.fprintf fmt "\\done"
  | Assign (r, e) -> Format.fprintf fmt "\\assign[]{%a}{%a}" pp_register r pp_expr e
  (* TODO : Print rmw_strength / exclusivity *)
  | Load (r, g, a, _) -> Format.fprintf fmt "\\assign[%a]{%s}{%s}" pp_ordering a r g
  | Store (r, e, a, _) -> Format.fprintf fmt "\\assign[%a]{%s}{%a}" pp_ordering a r pp_expr e
  | Fadd (r, g, rs, o_r, o_w, e) ->
     Format.fprintf fmt "\\assign[]{%a}\\texttt{FADD}(%a, %a, %a, %a, %a)"
                                       pp_register r
                                       pp_global g
                                       pp_rmw_strength rs
                                       pp_ordering o_r
                                       pp_ordering o_w
                                       pp_expr e
  | Cas (r, g, o_r, o_w, e1, e2) ->
     Format.fprintf fmt "\\assign[]{%a}\\texttt{CAS}(%a, %a, %a, %a, %a)"
                    pp_register r
                    pp_global g
                    pp_ordering o_r
                    pp_ordering o_w
                    pp_expr e1
                    pp_expr e2

  | Sequence (p1, p2) ->
     Format.fprintf fmt "%a \\sequencing \\\\ \n %a" go p1 go p2

  | Parallel _ as prog ->
     let ps = list_of_pars prog in
     let cols = (List.length ps * 2) - 1 in
     let cols_spec = String.concat "" (repeat "c" cols) in
     let cols_content =
       String.concat
         "\n& || &\n"
         (
           List.map show_ast_tex ps
         )
     in

     Format.fprintf fmt "\\begin{array}{%s}\n" cols_spec;
     Format.fprintf fmt "%s\n" cols_content;
     Format.fprintf fmt "\\end{array}"
  | Conditional (c, p1, p2) -> (
    match p2 with
        Skip -> Format.fprintf fmt "\\ifthen{%a}{%a}" pp_boolean_expr c go p1
      | _ -> Format.fprintf fmt "\\ifthenelse{%a}{%a}{%a}" pp_boolean_expr c go p1 go p2)
  | While (c, p1) ->
    Format.fprintf fmt "\\while{%a}{%a}" pp_boolean_expr c go p1
  | Fence o -> Format.fprintf fmt "\\fencecmd{\\textsc{%a}}" pp_ordering o
  | Print e -> Format.fprintf fmt "print\ %a" pp_expr e
  | Lock -> Format.fprintf fmt "\\texttt{lock}"
  | Unlock -> Format.fprintf fmt "\\texttt{unlock}"
  in
  Format.fprintf fmt "%a" go ast

let pp_ast_tex fmt ast =
  Format.fprintf fmt "\\begin{equation}\n";
  Format.fprintf fmt "\\begin{gathered}\n";
  Format.fprintf fmt "%a\n" pp_ast_tex' ast;
  Format.fprintf fmt "\\end{gathered}\n";
  Format.fprintf fmt "\\end{equation}\n"
