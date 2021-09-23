open Relation

let execution_time =
  let start_time = Sys.time () in
  function () -> Sys.time () -. start_time

module type MM = sig
  type denotation
  type label
  type event_structure
  type justification
  type execution
  type event

  val denote : AST.value set -> int -> AST.ast -> denotation
  val p_les : denotation -> event_structure
  val p_jst : denotation -> justification
  val p_exns : denotation -> execution list
    
  val events : event_structure -> event set
  val lookup : 'a -> ('a, 'b) relation -> 'a * 'b

  val apply_axioms : denotation -> (string * denotation) list
  val es_configurations : event_structure -> int set set
  val check : bool -> AST.outcome -> denotation -> execution set

  val pp_denotation : Format.formatter -> denotation -> unit
  val pp_con_tex : Format.formatter -> denotation -> int set -> unit
  val pp_exn_tex : Format.formatter -> denotation -> execution -> unit
  val pp_denotation_tex : Format.formatter -> denotation -> unit
  val pp_jst : Format.formatter -> denotation -> unit
  val denotation_json : denotation -> Yojson.Safe.t
end

module Model_implementation (X : MM) (C : RunConfig.Configuration) =
  struct
    let go (texfmt, fmt) ast outcome =
    if not C.go then [`Null] else begin
    if C.pp_tex then (
      Format.fprintf texfmt "\\section*{%s}\n" (C.name);
      ASTTex.pp_ast_tex texfmt ast;
    );

    if C.pp_ast then Format.fprintf fmt "%a\n" AST.pp_ast ast;
    if C.verbose then Format.fprintf fmt "Values: %a\n" (Relation.pp_set AST.pp_value) (C.values);
    if C.verbose then Format.fprintf fmt "Max steps: %d\n" C.max_steps;
    let denotation = X.denote (C.values) C.max_steps ast in
    let red fmt = Format.fprintf fmt "\027[38;5;209m%s\027[39;49m" in
    let model_denotations = (X.apply_axioms denotation) in
    List.fold_right (fun (model, denotation) models_json ->
        if C.pp_tex then (Format.fprintf texfmt "\\section{%s}" model);
        (* ????
        if not C.pp_tex && C.pp_denotion then Format.fprintf texfmt "%a\n" X.pp_denotation denotation;
        *)
        if C.pp_tex then X.pp_denotation_tex texfmt denotation;
        if C.pp_tex && C.enumerate then (
          List.iter (fun exn ->
              X.pp_exn_tex texfmt denotation exn
            ) (X.p_exns denotation)
        );
        (
          match outcome with
            Some outcome -> (
            if C.pp_tex && C.check then (
              Format.fprintf texfmt "\\subsection*{Check}\n";
              match outcome with
                (AST.Forbidden _) as o ->
                (
                  Format.fprintf texfmt "\\subsubsection*{Outcome: %a}\n" AST.pp_outcome o;
                  let contradicting_exns = X.check C.closed_program o denotation in
                  if List.length contradicting_exns > 0 then (
                    Format.fprintf texfmt "There are executions which are \\textbf{inconsistent} with the constraint!\n\n";
                    Format.fprintf fmt "%s = %a; " model red "contradiction";
                    List.iter (fun exn ->
                        Format.fprintf texfmt "\\textbf{Contradicting} execution: %a.\n\n"
                                       (fun fmt -> X.pp_exn_tex fmt denotation) exn
                      ) contradicting_exns
                  )
                  else (
                    Format.fprintf texfmt "All executions are \\textbf{consistent} with the constraint.\n\n";
                    Format.fprintf fmt "%s = %s;            " model "ok"
                  )
                )
              | (AST.Allowed _) as o ->
                 Format.fprintf texfmt "\\subsubsection*{Outcome: %a}\n" AST.pp_outcome o;
                 let acceptable_exns = X.check C.closed_program o denotation in
                 if List.length acceptable_exns > 0 then (
                   Format.fprintf texfmt "The constraint may be satisfied.\n\n";
                   Format.fprintf fmt "%s = %s;            " model "ok"
                 )
                 else (
                   Format.fprintf texfmt "There are \\textbf{no} executions that are consistent with the constraint!\n\n";
                   Format.fprintf fmt "%s = %a; " model red "contradiction"
                 ))
          
          else if C.check then 
              match outcome with
                (AST.Forbidden _) as o ->
                (
                  let contradicting_exns = X.check C.closed_program o denotation in
                  if List.length contradicting_exns > 0 then (
                    Format.fprintf fmt "%s = %a; " model red "contradiction";
                  )
                  else (
                    Format.fprintf fmt "%s = %s;            " model "ok"
                  )
                )
              | (AST.Allowed _) as o ->
                 let acceptable_exns = X.check C.closed_program o denotation in
                 if List.length acceptable_exns > 0 then (
                   Format.fprintf fmt "%s = %s;            " model "ok"
                 )
                 else (
                   Format.fprintf fmt "%s = %a; " model red "contradiction"
                 ))
          | _ -> ()
        );
        if C.pp_tex then (
          Format.fprintf texfmt "\\subsection*{Justification Relation}\n";
          Format.fprintf texfmt "%a" X.pp_jst denotation
        );
        let (model_json : Yojson.Safe.t) = `Assoc [
          "name", `String model;
          "denotation", X.denotation_json denotation;
          ]
        in model_json::models_json
      ) model_denotations []
      end

end
