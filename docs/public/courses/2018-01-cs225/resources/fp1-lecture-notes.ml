#require "ppx_deriving.std"

(* In order for merlin to work, you need to have a file named .merlin in the
 * same directory as this file with the following text:
 *
 *     PKG ppx_deriving.std
 *
 *)

(* Programming with lists and iteration in OCaml *)

let rec length (xs : 'a list) : int = match xs with
  | [] -> 0
  | x::xs' -> 1 + length xs'

(* time: O(N) in length of xs *)
(* same as built in operator `@` *)
let rec append (xs : 'a list) (ys : 'a list) : 'a list = match xs with
  | [] -> ys
  | x::xs' -> x::append xs' ys

(* time: O(N²) in length of xs *)
let rec reverse (xs : 'a list) : 'a list = match xs with
  | [] -> []
  | x :: xs' -> reverse xs' @ [x]

let _ = print_endline ([%show : int list] (reverse [1;2;3;4]))

(* reverse [1;2;3;4]
 * = reverse [2;3;4] @ [1]
 * = (reverse [3;4] @ [2]) [1]
 * = ((reverse [4] @ [3]) @ [2]) [1]
 * = (((reverse [] @ [4]) @ [3]) @ [2]) @ [1]
 * O(N)
 *   | = ((([] @ [4]) @ [3]) @ [2]) @ [1]
 *   | O(0)
 *   | = (([4] @ [3]) @ [2]) @ [1]
 *   | O(1)
 * N | = ([4;3] @ [2]) @ [1]
 *   | O(2)
 *   | = [4;3;2] @ [1]
 *   | O(3)
 *   | = [4;3;2;1]
 * total time complexity: O(N²)
 *)

(* reverse_i xs ys ≈ reverse xs @ ys
 * time: O(N) in length of xs *)
let rec reverse_i (xs : 'a list) (ys : 'a list) = match xs with
  | [] -> ys
  | x::xs' -> reverse_i xs' (x::ys)

let rec reverse' (xs : 'a list) : 'a list = reverse_i xs []

let _ = print_endline ([%show : int list] (reverse' [1;2;3;4]))
(* reverse' [1;2;3;4]
 * = reverse_i [1;2;3;4] []
 * = reverse_i [2;3;4] (1 :: [])
 * = reverse_i [3;4] (2 :: 1 :: [])
 * = reverse_i [4] (3 :: 2 :: 1 :: [])
 * = reverse_i [] (4 :: 3 :: 2 :: 1 :: [])
 * = 4 :: 3 :: 2 :: 1 :: []
 * = [4;3;2;1]
 *)

let rec add_5 (xs : int list) : int list = match xs with
  | [] -> []
  | x::xs' -> x + 5 :: add_5 xs'

let _ = print_endline ([%show : int list] (add_5 [1;2;3;4]))

let rec add_n (n : int) (xs : int list) : int list = match xs with
  | [] -> []
  | x::xs' -> x + n :: add_n n xs'

let add_5' = add_n 5

let _ = print_endline ([%show : int list] (add_5' [1;2;3;4]))

let rec change_int (f : int -> int) (xs : int list) : int list = match xs with
  | [] -> []
  | x :: xs' -> f x :: change_int f xs'

let add_5'' = change_int (fun x -> x + 5)

let _ = print_endline ([%show : int list] (add_5'' [1;2;3;4]))

let rec map (f : 'a -> 'b) (xs : 'a list) : 'b list = match xs with
  | [] -> []
  | x :: xs' -> f x :: map f xs'

let add_5''' = map (fun x -> x + 5)

let _ = print_endline ([%show : int list] (add_5''' [1;2;3;4]))

let rec upto_i (n_i : int) (n : int) : int list =
  if n_i = n
  then []
  else n_i :: upto_i (n_i + 1) n

let upto n = upto_i 0 n

let _ = print_endline ([%show : int list] (upto 10))
let _ = print_endline ([%show : int list list] (map upto (upto 10)))
let _ = print_endline ([%show : int list list list] (map (map upto) (map upto (upto 10))))

let rec concat (xs : string list) : string = match xs with
  | [] -> ""
  | x::xs' -> x ^ concat xs'

let _ = print_endline (concat ["x";"y";"z"])

let rec fold_right (y : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
  | [] -> y
  | x::xs' -> f x (fold_right y f xs')

let rec concat' = fold_right "" (fun x y -> x ^ y)

let _ = print_endline (concat' ["x";"y";"z"])

(* concat' ["x";"y";"z"]
 * = fold_right "" (fun x y -> x ^ y) ["x";"y";"z"]
 * = "x" ^ fold_right "" (fun x y -> x ^ y) ["y";"z"]
 * = "x" ^ "y" ^ fold_right "" (fun x y -> x ^ y) ["z"]
 * = "x" ^ "y" ^ "z" ^ fold_right "" (fun x y -> x ^ y)
 * = "x" ^ "y" ^ "z" ^ ""
 * = "xyz"
 *)

let rec list_identity = fold_right [] (fun x xs -> x :: xs)

let _ = print_endline ([%show : int list] (list_identity [1;2;3]))
(* list_identity [1;2;3]
 * = fold_right [] (fun x xs -> x :: xs) [1;2;3]
 * = 1 :: fold_right [] (fun x xs -> x :: xs) [2;3]
 * = 1 :: 2 :: fold_right [] (fun x xs -> x :: xs) [3]
 * = 1 :: 2 :: 3 :: fold_right [] (fun x xs -> x :: xs) []
 * = 1 :: 2 :: 3 :: []
 * = [1;2;3]
 *)

let rec fold_left (y : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
  | [] -> y
  | x::xs' -> fold_left (f x y) f xs'

let rec reverse'' = fold_left [] (fun x xs -> x :: xs)

let _ = print_endline ([%show : int list] (reverse'' [1;2;3]))
(* reverse'' [1;2;3]
 * = fold_left []                  (fun x xs -> x :: xs) [1;2;3]
 * = fold_left (1 :: [])           (fun x xs -> x :: xs) [2;3]
 * = fold_left (2 :: 1 :: [])      (fun x xs -> x :: xs) [3]
 * = fold_left (3 :: 2 :: 1 :: []) (fun x xs -> x :: xs) []
 * = (3 :: 2 :: 1 :: [])
 * = [3;2;1]
 *)

(* "point-free" versions *)

(* compose two functions *)
let rec (%) (g : 'b -> 'c) (f : 'a -> 'b) (x : 'a) : 'c = g (f x)

(* the identity function *)
let rec id (x : 'a) : 'a = x

let rec fold_right (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b -> 'b = match xs with
  | [] -> id
  | x::xs' -> f x % fold_right f xs'

let rec fold_left (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b -> 'b = match xs with
  | [] -> id
  | x::xs' -> fold_left f xs' % f x


