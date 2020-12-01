(* Name: <your name> *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* HW: HW2 *)

(* To run this file, execute the following command in a terminal from the same
 * directory as this file:
 *
 *     ocaml hw2.ml
 *
 * This command should execute this file, and print a number of lambda terms,
 * as well as some <todo> strings.
 *
 * Alternatively, you can load this file into an interactive prompt. E.g., to
 * inspect the value `t_id`:
 *
 *     ocaml
 *     # #use "hw2.ml";;
 *     # t_id;;
 *     - : term = Lam ("x", Var "x")
 *
 * I suggest if you want to use an interpreter to download and use utop.
 * (Installing utop is part of the install instructions posted to Piazza.) To
 * use utop, just execute it in place of the ocaml command:
 * 
 *     utop
 *     # #use "hw2.ml";;
 *     # t_id;;
 *     - : term = Lam ("x", Var "x")
 *
 * utop has more features than ocaml, e.g., if you press the up arrow on your
 * keyboard, it will load the last command you typed. *)

(* Some functions in this file are not fully implemented. (It will be your job
 * to fill them in.) To indicate this, but still allow OCaml to typecheck the
 * file, those functions are defined to throw a TODO exception. The line that
 * follows this comment defines the existence of that exception. *)
exception TODO

(* Here is a definition for the syntax of untyped lambda-calculus terms *)
type term =
  | Var of string
  | Lam of string * term
  | App of term * term

(* A helper function for printing terms *)
let rec string_of_term (t : term) : string = match t with
  | Var(x) -> x
  | Lam(x,t) -> "(lam " ^ x ^ ". " ^ string_of_term t ^ ")"
  | App(t1,t2) -> "(" ^ string_of_term t1 ^ " " ^ string_of_term t2 ^ ")"

(* It can be painful to write lambda terms in constructor form, e.g.,
 * App(Lam("x",Var("x")),Var("x")), so let's define some helpers. *)

(* A helper for constructing variable terms. `v` is just a short useful name
 * which wraps around `Var` *)
let v (x : string) : term = Var(x)

(* A helper function for constructing multi-argument lambdas. See examples
 * below for uses of `l`. *)
let rec l (xs : string list) (t : term) : term = match xs with
  | [] -> t
  | x::xs' -> Lam(x,l xs' t)

(* A helper function for constructing multi-argument applications. See
 * examples below for uses of `@`. 
 *
 * `@` is called an "in"fix operator, because to call it you place it
 * "in"between its arguments. E.g., `t1 @ [t1;t2]` is a call to `@` with `t1`
 * as the first argument and `[t1;t2]` as the second argument. (`[t1;t2]` is a
 * list containing two elements: `t1` and `t2`.) *)
let rec (@) (t : term) (ts : term list) : term = match ts with
  | [] -> t
  | t'::ts' -> App(t,t') @ ts'

(* Beware: if you are not familiar with OCaml, the syntax precedence can
 * sometimes be a little strange.
 * E.g., `l ["x"] (v "x") @ [v "x"]` is parsed as 
 * `(l ["x"] (v "x")) @ [v * "x"]`, NOT `l ["x"] ((v "x") @ [v "x"])`
 * *)

(* Some example terms, and how they look printed out *)

(* The identity function *)
let t_id : term = l ["x"] (v "x")
let _ = print_string "t_id:\t\t" ; print_endline (string_of_term t_id)

(* The U combinator *)
let t_U : term = l ["x"] (v "x" @ [v "x"])
let _ = print_string "t_U:\t\t" ; print_endline (string_of_term t_U)

(* The Omega term, which loops forever *)
let t_Omega : term = t_U @ [t_U]
let _ = print_string "t_Omega:\t" ; print_endline (string_of_term t_Omega)

(* An encoding for booleans *)
let t_true : term = l ["x";"y"] (v "x")
let _ = print_string "t_true:\t\t" ; print_endline (string_of_term t_true)

let t_false : term = l ["x";"y"] (v "y")
let _ = print_string "t_false:\t" ; print_endline (string_of_term t_false)

let t_cond : term = l ["b";"tb";"fb"] (v "b" @ [v "tb";v "fb"])
let _ = print_string "t_cond:\t\t" ; print_endline (string_of_term t_cond)

(* These lines import new types `string_set` and `string_map` for manipulating
 * sets of strings and maps of strings. *)

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
type string_set = StringSet.t
type 'a string_map = 'a StringMap.t

(* Sets of strings are created and manipulated through StringSet.* operations.
 * See https://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html for
 * documentation of all operations supported on sets. We also introduce
 * `string_map` for the map datatype with strings as keys. You won't need to
 * use `string_map`, but they are used in some helper functions provided for
 * you. *)

(* Helper functions for printing sets of strings and maps of strings *)

let string_of_string_set (ss : string_set) : string =
  let rec string_of_string_elems (ss : string list) : string = match ss with
    | [] -> ""
    | s::[] -> s
    | s1::s2::ss' -> s1 ^ "," ^ string_of_string_elems (s2::ss')
  in
  "{" ^ string_of_string_elems (StringSet.elements ss) ^ "}"

let string_of_string_map 
  (string_of_v : 'a -> string) 
  (kvs : 'a string_map) 
  : string = 
    let string_of_key_val (kv : string * 'a) : string = match kv with
      | (k,v) -> k ^ ":" ^ string_of_v v
    in
    let rec string_of_string_keyvals (kvs : (string * 'a) list) : string = match kvs with
    | [] -> ""
    | kv::[] -> string_of_key_val kv
    | kv1::kv2::kvs' -> string_of_key_val kv1 ^ "," ^ string_of_string_keyvals (kv2::kvs')
    in
    "{" ^ string_of_string_keyvals (StringMap.bindings kvs) ^ "}"

(* Here are some examples values of `string_set`. Notice how operations over
 * `string_set` are accessed using `StringSet` module, using dot notation,
 * e.g., `StringSet.empty` *)

(* The empty set of strings *)
let ss_emp = StringSet.empty
let _ = print_string "ss_emp:\t\t" ; print_endline (string_of_string_set ss_emp)

(* Sets do not contain repeated elements *)
let ss_rep = StringSet.of_list ["x";"y";"x";"y";"z"]
let _ = print_string "ss_rep:\t\t" ; print_endline (string_of_string_set ss_rep)

(* The union of two sets of strings *)
let ss_uni = StringSet.union (StringSet.of_list ["x";"y"]) (StringSet.of_list ["x";"z"])
let _ = print_string "ss_uni:\t\t" ; print_endline (string_of_string_set ss_uni)

(* Elements can be removed from sets *)
let ss_rem = StringSet.remove "x" (StringSet.of_list ["x";"x";"y";"z"])
let _ = print_string "ss_rem:\t\t" ; print_endline (string_of_string_set ss_rem)

(* ########## Problem 1 (15 Points) ##########
 *
 * Define a function `free_vars` which computes the free variables of a term.
 * *)

(* [!!] Implement this function. Erase "raise TODO" and put your function
 * definition in its place. *)
let rec free_vars (t : term) : string_set = match t with
  | Var(x) -> raise TODO
  | Lam(x,t') -> raise TODO
  | App(t1,t2) -> raise TODO

(* ########## End Problem 1 (15 Points) ########## *)

(* Some tests for `free_vars`. (Feel free to define some new ones of your own.)
 * (These are placed inside of a try block so that if one of them throws a TODO
 * exception, the rest of the file will still be executed.) *)

let t_fv1 = v "x"
let _ = 
  print_string "t_fv1:\t\t" ; 
  try print_endline (string_of_string_set (free_vars t_fv1))
  with TODO -> print_endline "<todo>"

let t_fv2 = l ["x"] (v "x")
let _ = 
  print_string "t_fv2:\t\t" ;
  try print_endline (string_of_string_set (free_vars t_fv2))
  with TODO -> print_endline "<todo>"

let t_fv3 = l ["x"] (v "x" @ [v "y"])
let _ = 
    print_string "t_fv3:\t\t" ; 
    try print_endline (string_of_string_set (free_vars t_fv3))
    with TODO -> print_endline "<todo>"

let t_fv4 = (l ["x"] (v "x" @ [v "y"])) @ [v "x"]
let _ =
    print_string "t_fv4:\t\t" ; 
    try print_endline (string_of_string_set (free_vars t_fv4))
    with TODO -> print_endline "<todo>"

(* Here is a function which converts all binders in a lambda term to be
 * globally unique. It will be used for the next problem.
 *
 * (You need not understand the implementation of `make_unique`, but you should
 * understand what it does, perhaps by running it on some example terms.) *)

let make_unique (t : term) : term =
  let debug_make_unique = false in
  let new_var (iO : int option) (x : string) : string = match iO with
      | None -> x
      | Some(i) -> x ^ string_of_int i
  in
  let next_var (iO : int option) : int option = match iO with
      | None -> Some(1)
      | Some(i) -> Some(i+1)
  in
  let rec rename_var_r
    (iO : int option)
    (x : string) 
    (g : string_set)
    : string * string_set = 
      let x' = new_var iO x in
      if StringSet.mem x' g 
      then rename_var_r (next_var iO) x g
      else (x',StringSet.add x' g)
  in
  let rename_var = rename_var_r None in
  let rec make_unique_r_i
    (t : term) 
    (env : string string_map) 
    (g : string_set) 
    : term * string string_map * string_set = 
      match t with
      | Var(x) -> begin match StringMap.find_opt x env with 
          | None -> 
              let (x',g') = rename_var x g in
              let env' = StringMap.add x x' env in
              (Var(x'),env',g')
          | Some(x') -> (Var(x'),env,g)
          end
      | Lam(x,t') -> 
          let (x',g') = rename_var x g in
          let env' = StringMap.add x x' env in
          let (t'',env'',g'') = make_unique_r t' env' g' in
          let env''' = match StringMap.find_opt x env with
            | None -> StringMap.remove x env''
            | Some(x'') -> StringMap.add x x'' env''
          in
          let t''' = Lam(x',t'')
          in (t''',env''',g'')
      | App(t1,t2) ->
          let (t1',env',g') = make_unique_r t1 env g in
          let (t2',env'',g'') = make_unique_r t2 env' g' in
          (App(t1',t2'),env'',g'')
  (* This is some debugging info, if you are curious how make_unique works at
   * each recursive step. Enable debugging info by setting `debug_make_unique`
   * to true at the top of this function. *)
  and make_unique_r t env g = 
    if debug_make_unique 
    then
      let (t',env',g') = make_unique_r_i t env g in
      print_endline "<" ;
      print_string "t-in: " ; print_endline (string_of_term t) ;
      print_string "env-in: " ; print_endline (string_of_string_map (fun x -> x) env) ;
      print_string "g-in: " ; print_endline (string_of_string_set g) ;
      print_string "t-out: " ; print_endline (string_of_term t') ;
      print_string "env-out: " ; print_endline (string_of_string_map (fun x -> x) env') ;
      print_string "g-out: " ; print_endline (string_of_string_set g') ;
      print_endline ">" ;
      flush_all () ;
      (t',env',g')
    else make_unique_r_i t env g
  in
  let (t',_,_) = make_unique_r t StringMap.empty StringSet.empty
  in t'

let t = (l ["x"] (v "x" @ [v "x"]) @ [v "x" @ [v "x";l ["x"] (v "x")]]) @ [v "x"]
let _ = print_string "make_unique:\t" ; print_endline (string_of_term (make_unique t))

(* ########## Problem 2 (25 Points) ##########
 *
 * Define a function `subst_r` which implements the substitution function on
 * terms. 
 *
 * The on-paper notation "[x |-> t2]t1" should translate into 
 * `subst_r x t2 t1`. That is, the first term argument `t2` is the term being
 * substituted, and the second term argument `t1` is the term for which
 * occurrences of `x` should be replaced with `t2`. The variable names are
 * written this way because substitution often arises from the beta reduction
 * rule: 
 *
 *     (lam x. t1)t2 --> [x |-> t2]t1
 *
 * Use the book's definition of substitution: Definition 5.3.5. As mentioned in
 * the book, this definition of substitution is only valid if it is assumed that
 * "the variable `y` is different from both `x` and the free variables of `s`".
 * This assumption will always be true of terms produced by `make_unique`.
 * Therefore, you need not worry about making sure this condition is true; that
 * part is already done for you.
 *
 * A wrapper for `subst_r` is provided for you---called `subst`---which calls
 * `make_unique` and then passes the renamed term to `subst_r`.  *)

(* [!!] Implement this function. Erase "raise TODO" and put your function
 * definition in its place. *)
let rec subst_r (x : string) (t2 : term) (t1 : term) : term = match t1 with
  | Var(y) -> raise TODO
  | Lam(y,t1') -> raise TODO
  | App(t11,t12) -> raise TODO

(* ########## End Problem 2 (25 Points) ########## *)

let subst (x : string) (t2 : term) (t1 : term) : term =
  match make_unique (App(Lam(x,t1),t2)) with
  | App(Lam(x',t1'),t2') -> subst_r x' t2' t1'
  | _ -> failwith "impossible"

let t_sub11 = v "x"
let t_sub12 = v "y"
let _ = 
  print_string "t_sub1:\t\t" ; 
  try print_endline (string_of_term (subst "x" t_sub12 t_sub11))
  with TODO -> print_endline "<todo>"

let t_sub21 = (l ["x"] (v "x")) @ [v "x"]
let t_sub22 = v "y"
let _ = 
  print_string "t_sub2:\t\t" ; 
  try print_endline (string_of_term (subst "x" t_sub22 t_sub21))
  with TODO -> print_endline "<todo>"

let t_sub31 = (l ["x"] (v "x")) @ [l ["x"] (v "x") ; v "x"]
let t_sub32 = v "z"
let _ = 
  print_string "t_sub3:\t\t" ; 
  try print_endline (string_of_term (subst "x" t_sub32 t_sub31))
  with TODO -> print_endline "<todo>"

let t_sub41 = (l ["y";"y";"y"] ((v "x") @ [v "y"])) @ [v "x"]
let t_sub42 = v "z"
let _ = 
  print_string "t_sub4:\t\t" ; 
  try print_endline (string_of_term (subst "x" t_sub42 t_sub41))
  with TODO -> print_endline "<todo>"

(* Name: <your name> *)
