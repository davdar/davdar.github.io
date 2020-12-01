#require "ppx_deriving.std"

(* In order for merlin to work, you need to have a file named .merlin in the
 * same directory as this file with the following text:
 *
 *     PKG ppx_deriving.std
 *
 * Interpret this file with `utop` instead of `ocaml`
 *
 *     utop <this-file>
 *)

(* universal quantification *)

let id (x : 'a) : 'b = x
(* id : ∀ 'a. 'a -> 'a *)

let five = id 5

let anothertrue = id true

let rec map (f : 'a -> 'b) (xs : 'a list) : 'b list = match xs with
  | [] -> []
  | x :: xs' -> f x :: map f xs'

let _ = print_endline ([%show : int list] (map (fun x -> x + 1) [1;2;3;4;5]))

let iszero (x : int) : bool = id (id x = 0)

let isfivezero : bool = iszero 5

let _ = print_endline (string_of_bool isfivezero)

let iszero_id_arg (id : 'a -> 'a) (x : int) : bool = failwith "not implemented" (*id (id x = 0) *)

(* iszero_id_arg : ∀ 'a. ('a -> 'a) -> int -> bool *)
(* iszero_id_arg : (∀ 'a. 'a -> 'a) -> int -> bool *)

(* in OCaml: map : ('a -> 'b) -> 'a list -> 'b list
 * in Java:
 * public <A,B> List<B> map(Fun<A,B> f, List<A> xs)
 * <see java code>
 *)

(* existential quantification *)

(* fancy name for what's going on is Generalized Algebraic Data Types (GADTs) *)
type obj =
  Object : 'a * ('a -> string) -> obj

let fiveO : obj = Object(5,string_of_int)
let trueO : obj = Object(true,string_of_bool)
let hiO : obj = Object("hi",id)

let to_string (o : obj) : string = match o with
  | Object(x,show_x) -> show_x x

let _ =
  print_endline (to_string fiveO) ;
  print_endline (to_string trueO) ;
  print_endline (to_string hiO)

(* OCaml has universal quantification (∀), although only supported in
 * left-most-outer-most position.
 * OCaml has existential quantification (∃), although in a strange form which
 * requires GADTs (a new feature).
 *
 * Java has universal quantification (∀), which are called generics, and are
 * slightly harder to use than OCaml's lightweight syntax.
 * Java has existential quantification (∃), everywhere, through the use of
 * objects and class hierarchies.
 *
 * ∃ x. P x ≈ ∀ Y. (∀ x. P x -> Y) -> Y
 *
 *)
