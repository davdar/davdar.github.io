(* # Lists in OCaml *)

type mylist = Nil | Cons of int * mylist

let rec string_of_int_list (is : mylist) = match is with
  | Nil -> "Nil"
  | Cons(i,is') -> "Cons(" ^ string_of_int i ^ "," ^ string_of_int_list is' ^ ")"
  

let one_two_three : mylist = Cons(1,Cons(2,Cons(3,Nil)))

let _ = print_endline (string_of_int_list one_two_three)

(* # OCaml has special syntax for lists which makes working with them easier *)

let one_two_three' : int list = 1::2::3::[]

let rec string_of_list_elems (xs : int list) = match xs with
  | [] -> ""
  | x::[] -> string_of_int x
  | x::x'::xs' -> string_of_int x ^ ";" ^ string_of_list_elems (x'::xs')

let string_of_list (xs : int list) = 
  "[" ^ string_of_list_elems xs ^ "]"

let _ = print_endline (string_of_list one_two_three')

let one_two_three'' : int list = [1;2;3]

let _ = print_endline (string_of_list one_two_three'')

let rec length (xs : int list) : int = match xs with
  | [] -> 0
  | _::xs' -> 1 + length xs'

let _ = print_endline (string_of_int (length one_two_three''))

(* `ceiling`: A function that takes two lists and returns the maximum of each
 * list position. E.g., ceiling [1;2;3;4;5] [5;4;3;2;1] = [5;4;3;4;5] *)
let rec ceiling (xs : int list) (ys : int list) = match xs,ys with
  | [],[] -> []
  | x::xs',y::ys' -> max x y :: ceiling xs' ys'
  | [],y::ys' -> y::ys'
  | x::xs',[] -> x::xs'

let _ = print_endline (string_of_list (ceiling [1;2;3;4;5] 
                                               [4;3;2;1]))

(* # Sets in OCaml *)

(* Lists are ordered collections of elements, defined by a clean inductive
 * structure:
 * - To build a list, use `[]` and `::``.
 * - To compute something from a list, pattern match, handle `[]` and `::`
 *   case, and call recursively.
 * If you are programming with lists in OCaml and you are not using this
 * template, you are probably doing it wrong!
 *
 * Sets are *unordered* collections of elements, and do *not* have a clean
 * inductive structure. Your strategy for writing programs using sets should be
 * entirely different:
 * - To build a set, use `empty`, `singleton`, `of_list`, `add`, `remove,
 *   `union` and `intersection`
 * - To compute something from a set, either test for membership with `mem`, or
 *   convert to a list with `elements` and process the list using a recursive
 *   function.
 * Full documentation for set operations here:
 * https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html
 *
 * Some OCaml boilerplate is required to use sets, because it needs to know
 * which comparison operation to use. For most purposes, the following module
 * command will give you access to set operations for some datatype `mytype` of
 * elements:
 * 
 *     module MytypeSet = Set.Make(struct type t = mytype let compare = compare end)
 *
 * Set operations can then be accessed using `.` notation on MytypeSet. The
 * actual set datatype is accessed as `MytypeSet.t`. Sometimes it can be handy
 * to define a new name for `MytypeSet.t` which is a litle less
 * frightening:
 *
 *     type mytype_set = MytypeSet.t
 *
 * Lets see this in action for sets of integers.
 *)

module IntSet = Set.Make(struct type t = int let compare = compare end)
type int_set = IntSet.t

let int_set_empty : int_set = IntSet.empty
let int_set_repeats : int_set = IntSet.of_list [1;2;1;2;1;2;3;4]
let int_set_union : int_set = IntSet.union (IntSet.of_list [2;3;4;5]) int_set_repeats

(* We need a way for printing sets; let's use the same strategy as we did for
 * lists. *)

let string_of_int_set (xs : int_set) : string =
  "{" ^ string_of_list_elems (IntSet.elements xs) ^ "}"

let _ = print_endline (string_of_int_set int_set_empty)
let _ = print_endline (string_of_int_set int_set_repeats)
let _ = print_endline (string_of_int_set int_set_union)

(* If we wanted a datatype for sets of strings, we just need to instantiate
 * Set.Make again *)

module StringSet = Set.Make(struct type t = string let compare = compare end)
type string_set = StringSet.t

(* For built-in types like Int and String, the standard library already has
 * modules which define the `struct ... end` information. So you could instead
 * just write:
 *
 *     module IntSet = Set.Make(Int)
 *     module StringSet = Set.Make(String)
 *
 * However, for a custom datatype that you define on your own, you'll need to
 * either write the `struct ... end` bit yourself, or define your own named
 * module `MyType` that contains the same information. *)
