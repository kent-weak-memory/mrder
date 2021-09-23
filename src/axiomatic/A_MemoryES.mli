open AST
open Relation
open EventStructure

type justification = (event set, event) relation [@@deriving to_yojson]

type rf = (id, id) relation [@@deriving to_yojson]
type dep = (id, id) relation [@@deriving to_yojson]
type lck = (id, id) relation [@@deriving to_yojson]
type co = (id, id) relation [@@deriving to_yojson]
type calculated_relations = (string * (id, id) relation) list [@@deriving to_yojson]
type exn = (id set * rf * dep * lck * co * calculated_relations)
         
type ppo = (id, id) relation
type rmw = (id, id) relation
type data = (id, id) relation
type addr = (id, id) relation
type ctrl = (id, id) relation
type casdep = (id, id) relation
type jst_hist = justification
         
type t = les * exn set * justification * ppo * rmw * data * addr * ctrl * casdep * jst_hist

type continuation = (register, value) env -> (register, id) env -> id set -> t

val empty : t
val empty_continuation : continuation
val empty_environment : ('a, value) env

val lookup : 'a -> ('a, 'b) relation -> 'a * 'b

val pre_compose : register set -> (register, id) env -> id set -> id set -> t -> event -> t
val product : t -> t -> t
val products : t list -> t
val coproduct : value list -> register -> global -> ordering ->
                (register, value) env ->
                register set ->
                (register, id) env ->
                id set ->
                id set ->
                continuation -> t

val fadd : (global * expr * ordering * rmw_strength) ->
           value list -> register -> global -> ordering ->
           (register, value) env ->
           register set ->
           (register, id) env ->
           id set -> id set ->
           continuation -> t
  
val cas : (global * expr * expr * ordering * rmw_strength) ->
          value list -> register -> global -> ordering ->
          (register -> id) ->
          register list ->
          (register, id) env ->
          id set -> id set ->
          continuation -> t
  
val join : t -> t -> t
val freeze : t -> t

val quantified_rf_lck : t -> t
val apply_axioms : t -> t

val check : bool -> outcome -> t -> exn set
