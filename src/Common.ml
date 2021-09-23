(* types and functions (that should be) common to all backends, written as
an interface to the Tex modules *)
open AST

type label =
    R of (global * value * register * ordering * exclusivity)
  | W of (global * value * ordering * rmw_strength)
  | F of ordering
  | O of value
  | L | U
[@@deriving show, eq, to_yojson]