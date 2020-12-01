let rec ctor_elems (ss : string list) : string = match ss with
  | [] -> ""
  | [s] -> s
  | s::ss' -> s ^ "," ^ ctor_elems ss'

let ctor (s : string) (ss : string list) : string =
  s ^ "(" ^ ctor_elems ss ^ ")"

type exp =
  | True
  | False
  | If of exp * exp * exp
  | Var of string
  | Lam of string * exp
  | App of exp * exp

let rec string_of_exp (e : exp) : string = match e with
  | True -> "True"
  | False -> "False"
  | If(e1,e2,e3) -> ctor "If" [string_of_exp e1;string_of_exp e2;string_of_exp e3]
  | Var(x) -> "\"" ^ x ^ "\""
  | Lam(x,e') -> ctor "Lam" ["\"" ^ x ^ "\"";string_of_exp e']
  | App(e1,e2) -> ctor "App" [string_of_exp e1;string_of_exp e2]

let e1 : exp = App(Lam("x",Var("x")),True)
let e2 : exp = App(Lam("x",Var("y")),True)

let _ = print_endline (string_of_exp e1)
let _ = print_endline (string_of_exp e2)

type ty =
    | Bool
    | Fun of ty * ty

let rec string_of_ty (t : ty) : string = match t with
  | Bool -> "Bool"
  | Fun(t1,t2) -> ctor "Fun" [string_of_ty t1;string_of_ty t2]

type value =
  | VTrue
  | VFalse
  | VLam of string * exp

let exp_of_value (v : value) : exp = match v with
  | VTrue -> True
  | VFalse -> False
  | VLam(x,e) -> Lam(x,e)

type result =
  | Val of value
  | Next of exp
  | Stuck

let subst (x : string) (v : value) (e : exp) : exp = failwith "undefined"

let rec step (e : exp) : result = match e with
  | True -> Val(VTrue)
  | False -> Val(VFalse)
  | If(e1,e2,e3) -> begin match step e1 with
    | Val(VTrue) -> Next(e2)
    | Val(VFalse) -> Next(e3)
    | Val(VLam(_,_)) -> Stuck
    | Next(e1') -> Next(If(e1',e2,e3))
    | Stuck -> Stuck
    end
  | Var(_) -> Stuck
  | Lam(x,e') -> Val(VLam(x,e'))
  | App(e1,e2) -> begin match step e1 with
    | Val(VTrue) -> Stuck
    | Val(VFalse) -> Stuck
    | Val(VLam(x,e')) -> begin match step e2  with
      | Val(v) -> Next(subst x v e')
      | Next(e2') -> Next(App(e1,e2'))
      | Stuck -> Stuck
      end
    | Next(e1') -> Next(App(e1',e2))
    | Stuck -> Stuck
    end

exception Stuck of exp

let rec step_star (e : exp) : exp = match step e with
  | Val(v) -> exp_of_value v
  | Next(e') -> step_star e'
  | Stuck -> e

let _ = print_endline (string_of_exp (step_star e1))
let _ = print_endline (string_of_exp (step_star e2))

exception NotInScopeError
exception TypeError

let rec check_tenv (tenv : (string * ty) list) (x : string) (t : ty) : bool = match tenv with
  | [] -> false
  | (x',t')::tenv' -> 
      if x = x' 
      then t = t' 
      else check_tenv tenv' x t

let rec lookup_tenv (tenv : (string * ty) list) (x : string) : ty = match tenv with
  | [] -> raise NotInScopeError
  | (x',t)::tenv' ->
      if x = x' then t
      else lookup_tenv tenv' x

let rec check (tenv : (string * ty) list) (e : exp) (t : ty) : bool = match e with
  | True -> t = Bool
  | False -> t = Bool
  | If(e1,e2,e3) -> 
      check tenv e1 Bool 
      && check tenv e2 t
      && check tenv e3 t
  | Var(x) -> check_tenv tenv x t
  | Lam(x,e') -> begin match t with
    | Bool -> false
    | Fun(t1,t2) -> check ((x,t1)::tenv) e' t2
    end
  | App(e1,e2) -> failwith "don't know what t1 should be"

let rec infer (tenv : (string * ty) list) (e : exp) : ty = match e with
  | True -> Bool
  | False -> Bool
  | If(e1,e2,e3) ->
      if not (infer tenv e1 = Bool)
      then raise TypeError
      else
      let t2 = infer tenv e2 in
      let t3 = infer tenv e3 in
      if not (t2 = t3)
      then raise TypeError
      else t2
  | Var(x) -> lookup_tenv tenv x
  (* One possible fix: include t1 in Lam, so Lam(x,t1,e) *)
  | Lam(x,e) -> failwith "don't know what t1 should be"
  | App(e1,e2) ->
      let t1 = infer tenv e1 in
      let t2 = infer tenv e2 in
      begin match t1 with
      | Bool -> raise TypeError
      | Fun(t11,t12) ->
          if not (t2 = t11) 
          then raise TypeError
          else t12
      end

let _ = 
  try print_endline (string_of_bool (check [] e1 Bool))
  with TypeError -> print_endline "<type-error>"

let _ = 
  try print_endline (string_of_bool (check [] e2 Bool))
  with TypeError -> print_endline "<type-error>"

let _ = 
  try print_endline (string_of_ty (infer [] e1))
  with TypeError -> print_endline "<type-error>"
let _ = 
  try print_endline (string_of_ty (infer [] e2))
  with TypeError -> print_endline "<type-error>"
