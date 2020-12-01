(* # Integers *)
print_endline "# Integers";;

let x : int = 5 * 9;;

print_int x;;
print_newline ();;

(* basic int operations: +, -, *, /, mod *)

(* # Floats (reals-ish) *)
print_endline "# Floats";;

let x : float = 5.0 +. 2.3;;

print_float x;;
print_newline ();;

(* basic float operations: +., -., *., /., sqrt, exp, log, sin, cos, ... *)

(* # Strings *)
print_endline "# Strings";;

let x : string = "hello" ^ " " ^ "CS 225";;

print_string x;;
print_newline ();;

print_endline x;;

(* basic string operations: ^ *)

(* # Bools *)
print_endline "# Bools";;

let x : bool = true || false && true;;

(* basic bool operations: ||, &&, not *)

print_endline (string_of_bool x);;

(* # Tuples *)
print_endline "# Tuples";;

let x : int * bool = (5,true);;
let old_x = x;;

print_endline ("(" ^ string_of_int (fst x) ^ "," ^ string_of_bool (snd x) ^ ")");;

let x : int * int * int * int = (1,2,3,4);;

let (a,b,c,d) = x in print_endline (string_of_int d);;
print_endline (string_of_int (fst old_x));;

(* # Equality and Ordering *)
print_endline "# Equality and Ordering";;

let x : int * bool = (5,true);;
let y : int * bool = (5,true);;

print_endline "> structural equality";;
print_endline (string_of_bool (x = y));;
print_endline (string_of_bool (x <> y));;

print_endline "> physical equality";;
print_endline (string_of_bool (x == y));;
print_endline (string_of_bool (x != y));;

let z : int * bool = (7,false);;

print_endline "> ordering";;
print_endline (string_of_bool (false < true));;
print_endline (string_of_bool (x < z));;

let x : int * bool = (5,true);;
let y : int * bool = (5,false);;

print_endline (string_of_bool (x = y));;
print_endline (string_of_bool (x <> y));;

print_endline (string_of_bool (x < y));;

(* # Scope and immutability *)
print_endline "# Scope"

let x : int = 5;;
let y : int = x;;
let x : int = 0;;

print_endline (string_of_int(x));;
print_endline (string_of_int(y));;

(* # Functions *)
print_endline "# Functions";;

let f (x : int) : int = x + 1;;

print_endline (string_of_int (f 1 * 3));;

let f : int -> int = fun (x : int) -> x + 1;;

print_endline (string_of_int (f 2 * 3));;

print_endline "---";;

let cat : int -> (int -> int) = fun x -> (fun y -> x + y);;

let d : int = cat 1 2;;
let a : int -> int = cat 2;;
let b : int = a 3;;
let c : int = a 4;;

print_endline (string_of_int d);;
print_endline (string_of_int b);;
print_endline (string_of_int c);;

let f (x : int) (y : int) : int = x + y;;

print_endline "---";;

let a : int -> int = f 2;;
let b : int = a 3;;
let c : int = a 4;;

print_endline (string_of_int b);;
print_endline (string_of_int c);;

(* # Option type *)
print_endline "# Option"

(* type 'a option = None | Some of 'a;; *)

let safe_divide (i : int) (j : int) : int option =
  if j = 0 
  then None
  else Some (i / j);;

let string_of_option (iO : int option) : string = match iO with
  | None -> "None"
  | Some i -> "(Some " ^ string_of_int i ^ ")";;

print_endline (string_of_option (safe_divide 10 3));;
print_endline (string_of_option (safe_divide 10 0));;

(* # Inductive Datatypes and pattern matching*)
print_endline "# Datatypes";;

type nat = Z | S of nat;;

let five : nat = S (S (S (S (S Z))));;

let rec string_of_nat (n : nat) : string = 
  match n with
  | Z -> "Z"
  | S n -> "(S " ^ string_of_nat n ^ ")";;

print_endline (string_of_nat five);;

let rec int_of_nat (n : nat) : int = match n with
  | Z -> 0
  | S n -> 1 + int_of_nat n;;

print_endline (string_of_int (int_of_nat five));;

let rec nat_of_int (i : int) : nat = match i with
  | 0 -> Z
  | j when (j > 0) -> S (nat_of_int (j - 1))
  | j when (j < 0) -> invalid_arg "only defined for non-negative integers"
  | _ -> failwith "impossible";;

print_endline (string_of_nat (nat_of_int 20));;
try 
  print_endline (string_of_nat (nat_of_int (-1)))
with
  Invalid_argument msg -> print_endline msg ; print_endline "<exception handled>";;

(* # Programming Language Syntax *)
print_endline "# Bool Lang Syntax";;

type term = True | False | If of term * term * term;;

let rec string_of_term (t : term) : string = match t with
  | True -> "True"
  | False -> "False"
  | If (t1,t2,t3) -> "(If " ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ " " ^ string_of_term t3 ^ ")"

let string_of_term_option (tO : term option) : string = match tO with
  | None -> "None"
  | Some t -> "Some " ^ string_of_term t

let rec step (t : term) : term option = match t with
  | True -> None
  | False -> None
  | If (t1,t2,t3) -> match t1 with
    | True -> Some t2
    | False -> Some t3
    | If _ -> match step t1 with
      | Some t1' -> Some (If (t1',t2,t3))
      | None -> failwith "impossible";;

let rec step_star (t : term) : term option = match step t with
  | Some t' -> step_star t'
  | None -> Some t;;

let t1 = If (If (True,False,True),If (False,True,False),If (False,False,True));;

print_endline (string_of_term t1);;

print_endline (string_of_term_option (step t1));;

print_endline (string_of_term_option (step_star t1));;
