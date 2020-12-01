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
  | Zero
  | Succ of exp
  | Pred of exp
  | IsZero of exp

let rec string_of_exp (e : exp) : string = match e with
  | True -> "True"
  | False -> "False"
  | If(e1,e2,e3) -> ctor "If" [string_of_exp e1 ; string_of_exp e2 ; string_of_exp e3]
  | Zero -> "Zero"
  | Succ(e') -> ctor "Succ" [string_of_exp e']
  | Pred(e') -> ctor "Pred" [string_of_exp e']
  | IsZero(e') -> ctor "IsZero" [string_of_exp e']

let e1 : exp = If(False,Zero,Succ(Zero))
let e2 : exp = If(False,Zero,Succ(True))

let _ = print_endline (string_of_exp e1)
let _ = print_endline (string_of_exp e2)

type ty =
    | Bool
    | Nat

let string_of_ty (t : ty) : string = match t with
  | Bool -> "Bool"
  | Nat -> "Nat"

type num_value = 
  | VZero
  | VSucc of num_value

type value =
  | VTrue
  | VFalse
  | VNum of num_value

let rec exp_of_num_value (nv : num_value) : exp = match nv with
  | VZero -> Zero
  | VSucc(nv) -> Succ(exp_of_num_value nv)

let exp_of_value (v : value) : exp = match v with
  | VTrue -> True
  | VFalse -> False
  | VNum(nv) -> exp_of_num_value nv

type result =
  | Val of value
  | Next of exp
  | Stuck

let rec step (e : exp) : result = match e with
  | True -> Val(VTrue)
  | False -> Val(VFalse)
  | If(e1,e2,e3) -> begin match step e1 with
    | Val(VTrue) -> Next(e2)
    | Val(VFalse) -> Next(e3)
    | Val(VNum _) -> Stuck
    | Next(e1') -> Next(If(e1',e2,e3))
    | Stuck -> Stuck
    end
  | Zero -> Val(VNum VZero)
  | Succ(e')-> begin match step e' with
    | Val(VNum(nv)) -> Val(VNum(VSucc nv))
    | Val(VTrue) -> Stuck
    | Val(VFalse) -> Stuck
    | Next(e'') -> Next(Succ(e'))
    | Stuck -> Stuck
    end
  | Pred(e') -> begin match step e' with
    | Val(VNum VZero) -> Val(VNum(VZero))
    | Val(VNum (VSucc(nv))) -> Val(VNum nv)
    | Val(VTrue) -> Stuck
    | Val(VFalse) -> Stuck
    | Next(e'') -> Next(Pred(e''))
    | Stuck -> Stuck
    end
  | IsZero(e') -> begin match step e' with
    | Val(VNum VZero) -> Val(VTrue)
    | Val(VNum (VSucc(_))) -> Val(VFalse)
    | Val(VTrue) -> Val(VFalse)
    | Val(VFalse) -> Val(VFalse)
    | Next(e'') -> Next(Pred(e''))
    | Stuck -> Stuck
    end

exception Stuck of exp

let rec step_star (e : exp) : exp = match step e with
  | Val(v) -> exp_of_value v
  | Next(e') -> step_star e'
  | Stuck -> e

let _ = print_endline (string_of_exp (step_star e1))
let _ = print_endline (string_of_exp (step_star e2))

let rec check (e : exp) (t : ty) : bool = match e with
  | True -> t = Bool
  | False -> t = Bool
  | If(e1,e2,e3) -> 
      check e1 Bool 
      && check e2 t
      && check e3 t
  | Zero -> t = Nat
  | Succ(e') -> 
      t = Nat
      && check e' Nat
  | Pred(e') ->
      t = Nat
      && check e' Nat
  | IsZero(e') ->
      t = Bool
      && check e' Nat

let _ = print_endline (string_of_bool (check e1 Nat))
let _ = print_endline (string_of_bool (check e2 Nat))

exception TypeError

let rec infer (e : exp) : ty = match e with
  | True -> Bool
  | False -> Bool
  | If(e1,e2,e3) ->
      let t1 = infer e1 in
      let t2 = infer e2 in
      let t3 = infer e3 in
      if not (t1 = Bool && t2 = t3)
      then raise TypeError
      else t2
  | Zero -> Nat
  | Succ(e') ->
      let t' = infer e' in
      if not (t' = Nat)
      then raise TypeError
      else Nat
  | Pred(e') ->
      let t' = infer e' in
      if not (t' = Nat)
      then raise TypeError
      else Nat
  | IsZero(e') ->
      let t' = infer e' in
      if not (t' = Nat)
      then raise TypeError
      else Bool

let _ = 
  try print_endline (string_of_ty (infer e1))
  with TypeError -> print_endline "<type-error>"
let _ = 
  try print_endline (string_of_ty (infer e2))
  with TypeError -> print_endline "<type-error>"
