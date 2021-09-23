open EventStructure
open Relation

val pp_jst : Format.formatter -> A_MemoryES.t -> unit
val pp_tex : Format.formatter -> A_MemoryES.t -> unit
val pp_con_tex : Format.formatter -> A_MemoryES.t -> id set-> unit
val pp_exn_tex : Format.formatter -> A_MemoryES.t -> A_MemoryES.exn -> unit
val pp_begin_tex : Format.formatter -> unit
val pp_end_tex : Format.formatter -> unit
