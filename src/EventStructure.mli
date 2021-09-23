open AST
open Relation
open Common

type id = int
[@@deriving to_yojson]

type event = id * label
[@@deriving to_yojson]

val project_id : event -> id
val project_label : event -> label

type les = event set * (id, id) relation * (id, id) relation

val fresh_id : unit -> id

val empty_les : les

val events : les -> event set
val order : les -> (id, id) relation
val cnf : les -> (id, id) relation

val location : label -> global
val value : label -> value
val strength : label -> ordering

val same_location : event -> event -> bool
val same_value : event -> event -> bool
val is_write : event -> bool
val is_read : event -> bool
val is_fence : event -> bool
val is_lock : event -> bool
val is_unlock : event -> bool
val is_nonatomic : event -> bool
val writes : event list -> event list
val reads : event list -> event list
  
val con : les -> event set -> bool
val label : les -> id -> label
val id : event -> id
    
val prefix_event : les -> event -> les
val es_product : les -> les -> les
val es_coproduct : les -> les -> les
val es_sequence : les -> les -> ((id -> id) list) * les
val es_configurations : les -> id set set

val es_relabel : les -> (id -> id) * les

val equal_id : id -> id -> bool
val equal_event : event -> event -> bool

val partition_by_rel : (id, id) relation -> id set -> id set set

val pp_id : Format.formatter -> id -> unit
val pp_label : Format.formatter -> label -> unit
val pp_event : Format.formatter -> event -> unit
val pp_les : Format.formatter -> les -> unit

val test : unit -> unit

val final_register_values : les -> (id * register * value) list
