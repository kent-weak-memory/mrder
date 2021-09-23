open Model

module Ppofixed : MM = struct
  type denotation = P_MemoryES.t
  type event = EventStructure.event
  type label = Common.label
  type event_structure = EventStructure.les
  type execution = P_MemoryES.exn
  type justification = P_MemoryES.justification

  let denote = P_Interp.denote_program
  let p_les (les, _, _, _, _, _, _, _, _) = les
  let p_jst (_, _, jst, _, _, _, _, _, _) = jst
  let p_exns (_, exns, _, _, _, _, _, _, _) = exns

  let events = EventStructure.events
  let lookup = P_MemoryES.lookup
  let apply_axioms d =
    let q = P_MemoryES.quantified_rf_lck d in
    let add_empty_ppo (les, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist)  =
      (les, exns, jst, [], rmw, data, addr, ctrl, casdep, jst_hist)
    in
    let forget_empty_ppo (les, exns, jst, _, rmw, data, addr, ctrl, casdep, jst_hist) =
      (les, exns, jst, rmw, data, addr, ctrl, casdep, jst_hist)
    in
    let q = add_empty_ppo q in
    [
      "imm", forget_empty_ppo @@ Imm.apply_axioms q 
    ; "imm-aug", forget_empty_ppo @@  Immaug.apply_axioms q
    ]
    
  let es_configurations = EventStructure.es_configurations
  let check = P_MemoryES.check

  let pp_denotation = P_MemoryESTex.pp_tex
  let pp_con_tex = P_MemoryESTex.pp_con_tex
  let pp_exn_tex = P_MemoryESTex.pp_exn_tex
  let pp_denotation_tex = P_MemoryESTex.pp_tex
  let pp_jst = P_MemoryESTex.pp_jst
  let denotation_json = P_MemoryESJSON.denotation_json
end
