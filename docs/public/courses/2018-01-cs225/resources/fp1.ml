#require "ppx_deriving.show"

(* remember to put this in a .merlin file in the same directory
 *
 *     PKG ppx_deriving.show
 *
 * also, use `utop` to evaluate this file with:
 *
 *     utop class.ml
 *)

exception TODO

(*
let _ = print_endline ([%show : int list list] [[1];[2;3]])
*)

let rec length (xs : 'a list) : 'a = match xs with
  | [] -> 0
  | x::xs' -> 1 + length xs'

(*
let _ = print_endline ([%show : int] (length [1;2;3;4]))
let _ = print_endline (string_of_int (length [1;2;3;4]))
*)

(*
type color = Red | Green | Blue
[@@deriving show]

let _ = print_endline ([%show : color] Blue)
*)

(* want:   append [1;2;3] [4;5;6] == [1;2;3;4;5;6]
 * want:   append [1;2;3] [3;5;6] == [1;2;3;3;5;6]
 *)
(* imagine calling (append [1;2] [3;4]) *)
let rec append (xs : int list) (ys : int list) : int list = 
  match xs with
  (* append [] ys == ys *)
  | [] -> ys
  (* x = 1
   * xs' = [2]
   * ys = [3;4]
   * append xs' ys == [2;3;4]
   *)
  | x :: xs' -> x :: append xs' ys

let ten_things : int list = [1;2;3;4;5;6;7;8;9;10]

(*
let _ = print_endline ([%show : int list] (append ten_things [1]))
*)

(* append [1;2] [3;4]
 * = 1 :: append [2] [3;4]
 * = 1 :: 2 :: append [] [3;4]
 * = 1 :: 2 :: [3;4]
 * = 1 :: (2 :: (3 :: (4 :: [])))
 * = 1 :: 2 :: 3 :: 4 :: []
 * = [1;2;3;4]
 *)

(* append is built into OCaml as (append xs ys == xs @ ys) *)

(*
let _ = print_endline ([%show : int list] ([1;2;3] @ [4;5;6]))
*)

(* reverse [1;2;3] == [3;2;1] *)
let rec reverse (xs : int list) : int list = match xs with
  (* reverse [] == [] *)
  | [] -> []
  (* reverse (x :: xs')
   * in the example...
   * x   = 1
   * xs' = [2;3]
   * reverse xs' = [3;2]
   *)
  | x :: xs' -> reverse xs' @ [x]

(*
let _ = print_endline ([%show : int list ] (reverse [1;2;3;4]))
*)

(* reverse_better xs ys == reverse xs @ ys
 * reverse_better [1;2] [3;4] == reverse [1;2] @ [3;4] == [2;1;3;4]
 *)
let rec reverse_better (xs : int list) (ys : int list) = match xs with
  (* reverse_better [] ys == reverse [] @ ys *)
  | [] -> ys
  (* x   = 1
   * xs' = [2]
   * ys  = [3;4]
   * reverse_better [2] (1 :: [3;4])
   * == [2] @ (1 :: [3;4])
   * reverse_better xs' (x :: ys) == reverse xs' @ (x :: ys)
   * goal:
   * reverse_better (x :: xs') ys 
   * == reverse (x :: xs') @ ys
   * == reverse xs' @ [x] @ ys
   *)
  | x :: xs' -> reverse_better xs' (x :: ys)

(* reverse' xs == reverse_better xs [] == reverse xs @ [] == reverse xs *)
let rec reverse' (xs : int list) : int list = reverse_better xs []

(* reverse_better [1;2;3] [] 
 * == reverse_better [2;3] (1 :: [])
 * == reverse_better [3] (2 :: 1 :: [])
 * == reverse_better [] (3 :: 2 :: 1 :: [])
 * == 3 :: 2 :: 1 :: []
 * == [3;2;1]
 *)

(*
let _ = print_endline ([%show : int list] (reverse' [1;2;3]))
*)

(* add_5 [] == [] *)
let rec add_5 (xs : int list) : int list = match xs with
  | [] -> []
  | x :: xs' -> (x + 5) :: add_5 xs'

  (*
let _ = print_endline ([%show : int list] (add_5 [1;2;3;4]))
*)

let rec add_n (n : int) (xs : int list) : int list = match xs with
  | [] -> []
  | x :: xs' -> (x + n) :: add_n n xs'

  (*
let _ = print_endline ([%show : int list] (add_n 4 [1;2;3;4]))
*)

let rec do_stuff (f : int -> int) (xs : int list) : int list = match xs with
  | [] -> []
  | x :: xs' -> f x :: do_stuff f xs'

let _ = print_endline ([%show : int list] (do_stuff (fun x -> x * 5) [1;2;3;4]))

let rec list_map (f : 'a -> 'b) (xs : 'a list) : 'b list = match xs with
  | [] -> []
  | x :: xs' -> f x :: list_map f xs'

let _ = print_endline 
  ([%show : (int * int) list] (list_map (fun x -> (x + 5,x * 5)) [1;2;3;4]))

let rec concat (xs : string list) : string = match xs with
  | [] -> ""
  | x :: xs' -> x ^ concat xs'

let _ = print_endline (concat ["x";"y";"z"])

let rec fold_right (i : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
  | [] -> i
  | x :: xs' -> f x (fold_right i f xs')

let concat' = fold_right "hi" (fun s1 s2 -> s1 ^ s2)

let _ = print_endline (concat' ["x";"y";"z"])

let rec list_identity (xs : int list) : int list = match xs with
  | [] -> []
  | x :: xs' -> x :: list_identity xs'

let list_identity' = fold_right [] (fun x xs -> x :: xs)

let append' xs ys = fold_right ys (fun x xs -> x :: xs) xs

let _ = print_endline ([%show : int list] (append' [1;2;3] [4;5;6]))
