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

(* # Functional Programming w/recursion review *)

(* time: O(N) in length of xs *)
(* same as built in operator `@` *)
let rec append (xs : 'a list) (ys : 'a list) : 'a list = match xs with
  | [] -> ys
  | x::xs' -> x::append xs' ys

let _ = print_endline ([%show : int list] (append [1;2;3] [4;5;6]))

(* append [1;2] [3;4]
 * = 1 :: append [2] [3;4]
 * = 1 :: 2 :: append [] [3;4]
 * = 1 :: 2 :: [3;4]
 * = 1 :: (2 :: (3 :: (4 :: [])))
 * = 1 :: 2 :: 3 :: 4 :: []
 * = [1;2;3;4]
 *)

(* time: O(N²) in length of xs *)
let rec reverse (xs : 'a list) : 'a list = match xs with
  | [] -> []
  | x :: xs' -> reverse xs' @ [x]

let _ = print_endline ([%show : int list] (reverse [1;2;3;4]))

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

let rec map (f : 'a -> 'b) (xs : 'a list) : 'b list = match xs with
  | [] -> []
  | x :: xs' -> f x :: map f xs'

let add_5 = map (fun x -> x + 5)

let _ = print_endline ([%show : int list] (add_5 [1;2;3;4]))

(* upto_i 3 5 == [3;4;5] *)
(* upto_i 2 6 == [2;3;4;5;6] *)
let rec upto_i (n_i : int) (n : int) : int list =
  if n_i > n
  then []
  else n_i :: upto_i (n_i + 1) n

let upto n = upto_i 1 n

let _ = print_endline ([%show : int list] (upto 3))
let _ = print_endline ([%show : int list list] (map upto (upto 3)))
let _ = print_endline ([%show : int list list list] (map (map upto) (map upto (upto 3))))

let rec fold_right (y : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
  | [] -> y
  | x::xs' -> f x (fold_right y f xs')

let rec concat = fold_right "" (fun x y -> x ^ y)

let _ = print_endline (concat ["x";"y";"z"])

(* concat' ["x";"y";"z"]
 * = fold_right "" (fun x y -> x ^ y) ["x";"y";"z"]
 * = "x" ^ fold_right "" (fun x y -> x ^ y) ["y";"z"]
 * = "x" ^ "y" ^ fold_right "" (fun x y -> x ^ y) ["z"]
 * = "x" ^ "y" ^ "z" ^ fold_right "" (fun x y -> x ^ y)
 * = "x" ^ "y" ^ "z" ^ ""
 * = "xyz"
 *)

let rec fold_left (y : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
  | [] -> y
  | x::xs' -> fold_left (f x y) f xs'

let rec reverse' = fold_left [] (fun x xs -> x :: xs)

let _ = print_endline ([%show : int list] (reverse' [1;2;3]))

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

let add5 x = x + 5
let times3 x = x * 3

let add5_then_times3 = times3 % add5
let times3_then_add5 = add5 % times3

let _ = print_endline ([%show : int] (add5_then_times3 2))
let _ = print_endline ([%show : int] (times3_then_add5 2))

(* the identity function *)
let rec id (x : 'a) : 'a = x

(* old fold_right:
 *
 *     let rec fold_right (y : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
 *       | [] -> y
 *       | x::xs' -> f x (fold_right y f xs')
 *)
let rec fold_right (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b -> 'b = match xs with
  | [] -> id
  | x::xs' -> f x % fold_right f xs'

(* old fold_left:
 * 
 *     let rec fold_left (y : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
 *       | [] -> y
 *       | x::xs' -> fold_left (f x y) f xs'
 *)
let rec fold_left (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b -> 'b = match xs with
  | [] -> id
  | x::xs' -> fold_left f xs' % f x

(* # References *)

let _ =
  let r = ref 5 in
  print_endline ([%show : int] !r) ;
  r := 7 ;
  print_endline ([%show : int] !r) ;
  r := !r + 1;
  print_endline ([%show : int] !r) ;
  let s = r in
  print_endline ([%show : int] !s) ;
  s := 82 ;
  print_endline ([%show : int] !r)


let copy_r_s (r : int ref) (s : int ref) : unit =
  r := !s

let copy_r_s' (r : int ref) (s : int ref) : unit =
  r := 1 ;
  r := !s

(* are copy_r_s and copy_r_s' equal? *)

let _ =
  let r = ref 0 in
  let s = ref 9 in
  copy_r_s r s ;
  print_endline ([%show : int] !r) ;
  let r = ref 0 in
  let s = ref 9 in
  copy_r_s' r s ;
  print_endline ([%show : int] !r) ;
  let s = ref 9 in
  copy_r_s s s ;
  print_endline ([%show : int] !s) ;
  let s = ref 9 in
  copy_r_s' s s ;
  print_endline ([%show : int] !s)

(* # Array iteration using state *)

let _ = print_endline ([%show : int array] (Array.of_list [1;2;3;4]))

let arr_append (xs : int array) (ys : int array) : int array =
  let zs = Array.make (Array.length xs + Array.length ys) 0 in
  let i = ref 0 in
  while !i < Array.length xs do
    zs.(!i) <- xs.(!i) ;
    i := !i + 1
  done ;
  let i = ref 0 in
  while !i < Array.length ys do
    zs.(Array.length xs + !i) <- ys.(!i) ;
    i := !i + 1
  done ;
  zs

let _ = print_endline ([%show : int array] (arr_append (Array.of_list [1;2]) (Array.of_list [3;4])))

let arr_append' (xs : int array) (ys : int array) : int array =
  let zs = Array.make (Array.length xs + Array.length ys) 0 in
  for i = 0 to Array.length xs - 1 do
    zs.(i) <- xs.(i)
  done ;
  for i = 0 to Array.length ys - 1 do
    zs.(Array.length xs + i) <- ys.(i) ;
  done ;
  zs

let _ = print_endline ([%show : int array] (arr_append' (Array.of_list [1;2]) (Array.of_list [3;4])))

(* compare to... *)
let rec lst_append (xs : int list) (ys : int list) : int list = match xs with
  | [] -> ys
  | x :: xs -> x :: lst_append xs ys

let arr_reverse (xs : int array) : int array =
  let zs = Array.make (Array.length xs) 0 in
  for i = 0 to Array.length xs - 1 do
    zs.(Array.length xs - 1 - i) <- xs.(i)
  done ;
  zs

let _ = print_endline ([%show : int array] (arr_reverse (Array.of_list [1;2;3;4])))

(* compare to... *)
let rec lst_reverse (xs : 'a list) (ys : 'a list) = match xs with
  | [] -> ys
  | x::xs' -> reverse_i xs' (x::ys)

let rec reverse (xs : 'a list) : 'a list = reverse_i xs []

(* an array reverse with an alias problem *)

let arr_reverse_into (xs : int array) (ys : int array) : unit =
  if not (Array.length xs == Array.length ys) then failwith "bad arguments" ;
  for i = 0 to Array.length xs - 1 do
    ys.(Array.length xs - 1 - i) <- xs.(i)
  done

let _ =
  let xs = Array.of_list [1;2;3] in
  let ys = Array.of_list [0;0;0] in
  arr_reverse_into xs ys ;
  print_endline ([%show : int array] ys)

let _ =
  let xs = Array.of_list [1;2;3] in
  arr_reverse_into xs xs ;
  print_endline ([%show : int array] xs)
