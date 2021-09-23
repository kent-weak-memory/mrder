open RunConfig
open Model

let check = ref false
let closed_program = ref false
let enumerate = ref false
let verbose = ref false
let max_steps = ref 5
let values = ref [0;1;2]

let pp_ast = ref false
let pp_denotion = ref false
let pp_tex_ax = ref false
let pp_tex_ppo = ref false
let tex_filename : string option ref = ref None
let json_output = ref false
let json_filename : string option ref = ref None

let run_axm = ref true
let run_ppo = ref true
let run_ptr = ref true
                 
 (* stuff which should change between models *)
 (* tex_filename doesnt do anything now. it should! but it does not. *)
module type Configuration_extras = sig
  val pp_tex : bool
  val tex_filename : string option
  val go : bool
end 

let run filename =
  let fmt = Format.std_formatter in
  let fn = Util.option "/dev/null" (fun x -> x) !tex_filename in
  let perms = 0o644 in
  let tex_c = open_out_gen [Open_creat; Open_append] perms fn in
  let texfmt = Format.formatter_of_out_channel tex_c in
  let json_fn = Util.option "/dev/null" (fun x -> x) !json_filename in
  let json_c = open_out_gen [Open_creat; Open_wronly; Open_trunc] perms json_fn in
  let jsonfmt = Format.formatter_of_out_channel json_c in
  
  let config, ast, outcomes = Parse.parse filename in
  let config = match config with
      Some c -> c
    | None -> { name = filename; values = !values; comment = None }
  in


  let module C (M : Configuration_extras) : Configuration = struct
    type id = EventStructure.id
    type value = AST.value
    type register = AST.register

    let name = config.name
    let values = config.values
    let comment = config.comment
    let go = M.go

    let check = !check
    let enumerate = !enumerate
    let closed_program = !closed_program
    let verbose = !verbose
    let max_steps = !max_steps
    
    let pp_ast = !pp_ast
    let pp_denotion = !pp_denotion
    let pp_tex = M.pp_tex
    let json_output = !json_output

    let filename = filename
  end in

  let module C_ax = C (struct 
    let pp_tex = !pp_tex_ax
    let tex_filename = Option.bind !tex_filename (fun s -> Some (s ^ "_ax"))
    let go = !run_axm
  end) in
  let module C_ppo = C (struct
    let pp_tex = !pp_tex_ppo 
    let tex_filename = Option.bind !tex_filename (fun s -> Some (s ^ "_ppo"))
    let go = !run_ppo
  end) in

  let run_models o =
    Format.fprintf fmt "%60s: " C_ax.filename;
    
    let module Impl = (Axiomatic.Axiomatic : MM) in
    let module Mod = Model_implementation (Impl) (C_ax) in
    let axiomatic_models_json = Mod.go (texfmt, fmt) ast o in
    
    let module Impl = (Ppofixed.Ppofixed : MM) in
    let module Mod = Model_implementation (Impl) (C_ppo) in
    let ppofixed_models_json = Mod.go (texfmt, fmt) ast o in

    Format.fprintf fmt "(%.2fs)\n" (execution_time ());
    if C_ax.json_output then (
      let models_json = axiomatic_models_json @ ppofixed_models_json in
      let (json : Yojson.Safe.t) = `Assoc [("models", `List models_json)] in
      Format.fprintf jsonfmt "%s" (Yojson.Safe.pretty_to_string json);
    );
  in
  
  (
    match outcomes with
      Some os ->
      List.iter (fun outcome -> run_models (Some outcome)) os
    | _ -> run_models None
  );
           
  close_out tex_c

(* determine which model to use when printing tex file *)
(* this could be made more generic but right now i simply do not care enough *)
let parse_model str =
  if String.equal str "axiom" then pp_tex_ax := true 
  else if String.equal str "ppo" then pp_tex_ppo := true 
  else failwith ("illegal model name: " ^ str)

let args = Arg.align [
    "--values",
    Arg.String ((fun s -> let vs = String.split_on_char ',' s in values := (List.map int_of_string vs))),
    (Format.sprintf "  set the values which are used in the denotation. Default: [%s]"
       (String.concat ", " (List.map string_of_int !values)))
  ; "--axm", 
    Arg.Clear run_axm,
    "  don't run the Axiomatic model"
  ; "--ppo",
    Arg.Clear run_ppo,
    "  don't run the Ppo_fixed model"
  ; "--ptr",
    Arg.Clear run_ptr,
    "  don't run the AxiomaticBulk model"
  ; "--verbose",
    Arg.Set verbose,
    "  verbose printing"
  ; "--check",
    Arg.Set check,
    "  check the expected outcomes as specified in the litmus test file"
  ; "--enumerate",
    Arg.Set enumerate,
    "  enumerate all permitted executions"
  ; "--pp-tex",
    Arg.Tuple [
      Arg.String parse_model;
      Arg.String (fun s -> tex_filename := Some s);
      ],
    "  output a tex file to draw the denotation"
  ; "--max-steps",
    Arg.Set_int max_steps,
    (Format.sprintf "  set the maximum number of loop unrollings to do. Default: %d" !max_steps)
  ; "--pp-ast",
    Arg.Set pp_ast,
    (Format.sprintf "  pretty print the program as parsed. Default: %b" !pp_ast)
  ; "--pp-denotation",
    Arg.Set pp_denotion,
    "  do not print the program denotation"
  ; "--closed-programs",
    Arg.Set closed_program,
    "  only consider closed program executions"
  ; "--json-output",
    Arg.String (fun s -> json_output := true; json_filename := Some s),
    "  output denotation and all possible executions for each model to a JSON file"
  ]

let usage () =
  Format.sprintf "%s [OPTIONS] <FILENAME>" (Array.get Sys.argv 0)

let () = Arg.parse args run (usage ())
