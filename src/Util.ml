
let rec fold_left_pairwise f = function
  | [x] -> x
  | (x::xs) -> f x (fold_left_pairwise f xs)
  | [] -> raise (Invalid_argument "cannot fold pairwise with empty list")

let cmp_of_eq f a b = if f a b then 0 else 1

let n_cartesian_product = BatList.n_cartesian_product

(* returns [i,...,k] *)
let range i k =
  let rec loop xs k = if k < i then xs else loop (k :: xs) (k - 1) in
  loop [] k

let rec repeat n x =
  if n == 0 then [] else x :: repeat (n-1) x

let option d f = function
  | None -> d
  | Some x -> f x

let map_option f = function
  | None -> None
  | Some x -> Some (f x)

let id x = x

let flip f x y = f y x

(* TODO: either use same type as Haskell, or rename; maybe_unit? maybe_do? *)
let maybe a f =
  match a with
    Some a' -> f a'
  | None -> ()

let map_join c f ts =
  String.concat c (List.map f ts)

let on_channel (filename : string) (f : in_channel -> 'a) : 'a option =
  let ch = (try Some (open_in filename) with Sys_error _ -> None) in
  let result = (match ch with Some x -> Some (f x) | None -> None) in
  (match ch with Some x -> close_in_noerr x | _ -> ());
  result

let from_some = function
  | None -> failwith "INTERNAL: expected Some"
  | Some x -> x

let rec pp_list pp_x fmt = function
    [x] -> Format.fprintf fmt "%a" pp_x x
  | x::xs -> Format.fprintf fmt "%a, %a" pp_x x (pp_list pp_x) xs
  | [] -> ()

let rm x l = List.filter ((<>) x) l  

let rec permutations = function  
  | [] -> [[]]
  | x::[] -> [[x]]
  | l -> List.fold_left (fun acc x -> acc @ List.map (fun p -> x::p) (permutations (rm x l))) [] l

let rec order_of_list = function
    [] -> []
  | l :: ls -> List.map (fun l' -> (l, l')) ls @ (order_of_list ls)
            
