open AST
open EventStructure
open P_MemoryES
open Common

let bind p k v = fun k' -> if k = k' then v else p k'

let empty_psi _ =  raise Not_found 
let empty_gamma : id list = []
                      
let rec denote vs n p psi gamma k = function
    _ when n = 1 -> empty
    
  | Skip ->
     k p psi gamma

  | Assign (r, e) ->
     let p' r' = if r' = r then eval_expr p e else p r' in
     k p' psi gamma
    
  | Load (r, x, o, NotExclusive) ->
     coproduct vs r x o p [r] psi gamma [] k

  | Store (g, e, o, s) ->
     let v = eval_expr p e in
     let regs = registers_of_expr e in
     pre_compose regs psi gamma [] (k p psi gamma) (fresh_id (), W (g, v, o, s))

  | Load _ ->
     failwith "model only supports non-exclusive loads (vdlqx)"

  | Fadd (r, g, rs, o_r, o_w, e) ->
     fadd (g, e, o_w, rs) vs r g o_r p [] psi gamma [] k

  | Cas (r, g, o_r, o_w, e1, e2) ->
     cas (g, e1, e2, o_w, Strong) vs r g o_r p [] psi gamma [] k
    
  | Sequence (p1, p2) ->
     denote vs n p psi gamma (fun p' psi' gamma' -> denote vs n p' psi' gamma' k p2) p1

  | Parallel (p1, p2) ->
     let ps = list_of_pars (Parallel (p1, p2)) in
     (* let k' p = join (products (List.map (denote vs n p empty_continuation) ps)) (denote vs n p k (Sequence (Lock, Unlock))) in *)
     (* Hack to improve the tool performance and printing *)
     let k' p psi gamma = products (List.map (denote vs n p psi gamma empty_continuation) ps) in
     (* denote vs n p psi gamma k' (Sequence (Lock, Unlock))  *)
     P_MemoryES.freeze @@ k' p psi gamma

  | Conditional (pred, pt, pf) ->
     let gamma =
       List.fold_right
         (fun r acc ->
           try (psi r) :: acc
           with Not_found -> acc
         )
         (registers_of_bexpr pred) []
     in
     if eval_bexpr p pred
     then denote vs n p psi gamma k pt 
     else denote vs n p psi gamma k pf

  | While (pred, prog) ->
     let gamma = List.map psi (registers_of_bexpr pred) in
     if eval_bexpr p pred
     then denote vs (n - 1) p psi gamma k (Sequence (prog, While (pred, prog)))
     else denote vs n p psi gamma k Skip

  | Fence o -> pre_compose [] psi gamma [] (k p psi gamma) (fresh_id (), F o)

  | Print e -> pre_compose [] psi gamma [] (k p psi gamma) (fresh_id (), O (eval_expr p e))

  | Lock -> pre_compose [] psi gamma [] (k p psi gamma) (fresh_id (), L)

  | Unlock -> pre_compose [] psi gamma [] (k p psi gamma) (fresh_id (), U)

let denote_program vs n e =
  denote vs n empty_environment empty_psi empty_gamma empty_continuation e

