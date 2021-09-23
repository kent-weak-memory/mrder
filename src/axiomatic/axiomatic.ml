open Model

module Axiomatic : MM = struct
  type denotation = A_MemoryES.t
  type event = EventStructure.event
  type label = Common.label
  type event_structure = EventStructure.les
  type execution = A_MemoryES.exn
  type justification = A_MemoryES.justification

  let denote = A_Interp.denote_program
  let p_les (les, _, _, _, _, _, _, _, _, _) = les
  let p_jst (_, _, jst, _, _, _, _, _, _, _) = jst
  let p_exns (_, exns, _, _, _, _, _, _, _, _) = exns
             
  let events = EventStructure.events
  let lookup = A_MemoryES.lookup
  let apply_axioms d =
    let q = A_MemoryES.quantified_rf_lck d in
    let us = A_MemoryES.apply_axioms q in
    [
      "us", us
    ; "rc11", Rc11.apply_axioms q
    ; "rc11-aug", Rc11aug.apply_axioms q
    (* ; "c20-aug", C20aug.apply_axioms q *)
    ]
    
  let es_configurations = EventStructure.es_configurations
  let check = A_MemoryES.check

  let pp_denotation = A_MemoryESTex.pp_tex
  let pp_con_tex = A_MemoryESTex.pp_con_tex
  let pp_exn_tex = A_MemoryESTex.pp_exn_tex
  let pp_denotation_tex = A_MemoryESTex.pp_tex
  let pp_jst = A_MemoryESTex.pp_jst
  let denotation_json = A_MemoryESJSON.denotation_json
end
