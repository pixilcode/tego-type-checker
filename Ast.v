From Coq Require Import String.

Inductive mtch_value : Type :=
| MV_Int : nat -> mtch_value (* 1 *)
| MV_Bool : bool -> mtch_value (* true *)
| MV_Char : nat -> mtch_value (* 'a' (nat represents the ASCII value) *)
.

Inductive mtch : Type :=
| M_Ident : string -> mtch (* x *)
| M_List : list mtch -> mtch (* x , y *)
| M_Boxed : mtch -> mtch (* [ x ] *)
| M_Val : mtch_value -> mtch (* 1 *)
| M_Unit : mtch (* () *)
| M_Ignore : mtch (* _ *)
.

(* Selected subset of operators from the full list of
   operators that are representative of the full list *)
Inductive binary_op : Type :=
| BO_Plus (* x + y *)
| BO_Mult (* x * y *)
| BO_And (* x and y *)
| BO_Or (* x or y *)
| BO_Equal (* x == y *)
| BO_LessThanEqual (* x <= y *)
| BO_Join (* x , y *)
.

Inductive unary_op : Type :=
| UO_Not (* not x *)
.

Inductive expr_value : Type :=
| EV_Int : nat -> expr_value (* 1 *)
| EV_Bool : bool -> expr_value (* true *)
| EV_Char : nat -> expr_value (* 'a' (nat represents the ASCII value) *)
| EV_Unit : expr_value (* () *)
.

Inductive expr : Type :=
| E_Literal (value : expr_value) (* 1 *)
| E_Var (ident : string) (* x *)
| E_Let (x : mtch) (e : expr) (body : expr) (* let x = e in body *)
| E_Fn (param : mtch) (body : expr) (* fn param -> body *)
| E_FnApp (fn : expr) (arg : expr) (* fn arg *)
| E_If (cond : expr) (t : expr) (f : expr) (* if cond then t else f *)
| E_Match (e : expr) (branches : list (mtch * expr)) (* match e to branches*)
| E_Binary (op : binary_op) (x y : expr) (* x op y *)
| E_Unary (op : unary_op) (x : expr) (* op x *)
.