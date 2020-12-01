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

let rec append (xs : int list) (ys : int list) : int list = match xs with
  (* append [] ys *)
  | [] ->  ys
  (* append (x::xs') ys *)
  | x :: xs' ->  x :: append xs' ys

let _ = print_endline ([%show : int list] (append [1;2;3] [4;5;6]))

(* append [1;2] [3;4] 
 * == 1 :: append [2] [3;4]
 * == 1 :: 2 :: append [] [3;4]
 * == 1 :: 2 :: [3;4]
 * == [1;2;3;4]
 *)

(* reverse_a xs ys == reverse xs @ ys
 * reverse_a [1;2] [3;4] == [2;1;3;4]
 *)
let rec reverse_a (xs : int list) (ys : int list) : int list = match xs with
  | [] -> ys
  | x :: xs' -> reverse_a xs' (x :: ys)

let reverse (xs : int list) : int list = reverse_a xs []

let _ = print_endline ([%show : int list] (reverse [1;2;3]))

(* reverse [1;2;3]
 * == reverse_a [1;2;3] []
 * == reverse_a [2;3] [1]
 * == reverse_a [3] [2;1]
 * == reverse_a [] [3;2;1]
 * == [3;2;1]
 *)

exception TODO

let rec fold_right (i : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
  | [] -> i
  | x::xs' -> f x (fold_right i f xs')

let append' (xs : 'a list) (ys : 'a list) : 'a list = 
  fold_right ys (fun z zs -> z :: zs) xs

let _ = print_endline ([%show : int list] (append' [1;2] [3;4]))

(* append' [1;2] [3;4]
 * == fold_right [3;4] (fun z zs -> z :: zs) [1;2]
 * == 1 :: fold_right [3;4] (fun z zs -> z :: zs) [2]
 * == 1 :: 2 :: fold_right [3;4] (fun z zs -> z :: zs) []
 * == 1 :: 2 :: [3;4]
 * == [1;2;3;4]
 *)

let rec fold_left (i : 'b) (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b = match xs with
  | [] -> i
  | x::xs' -> fold_left (f x i) f xs'

let reverse' (xs : int list) : int list =
  fold_left [] (fun z zs -> z :: zs) xs

let _ = print_endline ([%show : int list] (reverse' [1;2;3;4]))

(* reverse' [1;2;3]
 * == fold_left [] (fun z zs -> z :: zs) [1;2;3]
 * == fold_left (1 :: []) (fun z zs -> z :: zs) [2;3]
 * == fold_left [2;1] (fun z zs -> z :: zs) [3]
 * == fold_left [3;2;1] (fun z zs -> z :: zs) []
 * == [3;2;1]
 *)

(* (g % f) x == g (f x)
 * on paper in math you would write (g ∘ f)
 *)

let (%) (g : 'b -> 'c) (f : 'a -> 'b) : 'a -> 'c = fun x -> g (f x)

let identity (x : 'a) : 'a = x

let rec fold_right' (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b -> 'b = match xs with
  | [] -> identity
  | x :: xs' -> f x % fold_right' f xs'

let rec fold_left' (f : 'a -> 'b -> 'b) (xs : 'a list) : 'b -> 'b = match xs with
  | [] -> identity
  | x :: xs' -> fold_left' f xs' % f x

(* references in OCaml *)

let _ =
  let x : int = 5 in
  print_endline ([%show : int] x) ;
  let r : int ref = (ref 5) in
  print_endline ([%show : int] !r) ;
  r := 7 ;
  print_endline ([%show : int] !r) ;
  r := 9 ;
  print_endline ([%show : int] !r) ;
  let s : int ref = r in
  print_endline ([%show : int] !s) ;
  r := 1 ;
  print_endline ([%show : int] !s) ;
  s := 4 ;
  print_endline ([%show : int] !r)

let copy_r_s (r : int ref) (s : int ref) : unit =
  r := !s

let copy_r_s' (r : int ref) (s : int ref) : unit =
  r := 1 ;
  r := !s

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

(* iteration with arrays *)

let arr_append (xs : int array) (ys : int array) : int array =
  let zs : int array = Array.make (Array.length xs + Array.length ys) 0 in
  let i = ref 0 in
  while (!i < Array.length xs) do
    zs.(!i) <- xs.(!i) ;
    i := !i + 1
  done ;
  i := 0 ;
  while (!i < Array.length ys) do
    zs.(Array.length xs + !i) <- ys.(!i) ;
    i := !i + 1
  done ;
  zs

let _ = print_endline ([%show : int array] 
  (arr_append (Array.of_list [1;2]) (Array.of_list [3;4])))

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
