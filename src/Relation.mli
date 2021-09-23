type 'a set = 'a list
[@@deriving to_yojson]
type ('a, 'b) env = ('a -> 'b)
type ('a, 'b) relation = ('a * 'b) set
[@@deriving to_yojson]

val union : 'a set -> 'a set -> 'a set
val (<|>) : 'a set -> 'a set -> 'a set

val intersect : 'a set -> 'a set -> 'a set
val (<&>) : 'a set -> 'a set -> 'a set

val difference : 'a set -> 'a set -> 'a set
val (<->) : 'a set -> 'a set -> 'a set

val cross : 'a set -> 'b set -> ('a, 'b) relation
val powerset : 'a set -> 'a set set

val rel_of_set : 'a set -> ('a, 'a) relation
val opt : 'a set -> ('a, 'a) relation -> ('a, 'a) relation
val seq : ('a, 'b) relation -> ('b, 'c) relation -> ('a, 'c) relation
val inv : ('a, 'b) relation -> ('b, 'a) relation
  
val transitive_closure : ?reflexive:bool -> (int, int) relation -> (int, int) relation
val tc : (int, int) relation -> (int, int) relation
val rtc : int set -> (int, int) relation -> (int, int) relation 
val irreflexive : (int, int) relation -> bool
val acyclic : (int, int) relation -> bool
  
val transitive_reduction : (int, int) relation -> (int, int) relation 

  
(** Derived functionss *)
val equal_set :
  ('a -> 'a -> bool)
  -> 'a set -> 'a set -> bool

val subset : ('a -> 'a -> bool) -> 'a set -> 'a set -> bool

val equal_relation :
  ('a -> 'a -> bool) ->
  ('b -> 'b -> bool) ->
  ('a, 'b) relation -> ('a, 'b) relation -> bool

val pp_list : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a set -> unit
val pp_pair : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a * 'a -> unit
  
val pp_set : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a set -> unit
val pp_relation :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter -> ('a, 'b) relation -> unit

(** Unit testing *)
val test : unit -> unit
