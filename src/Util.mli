val fold_left_pairwise : ('a -> 'a -> 'a) -> 'a list -> 'a

val cmp_of_eq : ('a -> 'a -> bool) -> 'a -> 'a -> int

val n_cartesian_product : 'a list list -> 'a list list

val range : int -> int -> int list

val repeat : int -> 'a -> 'a list

val option : 'a -> ('b -> 'a) -> 'b option -> 'a
  
val pp_list : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

val permutations : 'a list -> 'a list list

val order_of_list : 'a list -> ('a*'a) list
             
