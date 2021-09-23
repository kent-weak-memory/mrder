open Relation
open JSONUtils

let denotation_json (les, exns, jst, _, _, _, _, _, _, jst_hist) =
    let (denotation : Yojson.Safe.t) = `Assoc [
        "les", (les_record_to_yojson (les_to_les_record les));
        "executions", (set_to_yojson exn_record_to_yojson (List.map (fun exn -> exn_to_exn_record exn les) exns));
        "justifications", A_MemoryES.justification_to_yojson (jst@jst_hist)]
    in
    denotation
