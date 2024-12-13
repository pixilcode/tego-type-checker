From Tego Require Import Ast.
From Tego Require Import Types.
From Tego Require Import Env.

From Coq Require Import String.

Definition type_env := env type.

Definition type_of_evalue (value : expr_value) :=
	match value with
	| EV_Int _ => T_Int
	| EV_Bool _ => T_Bool
	| EV_Char _ => T_Char
	| EV_Unit => T_Unit
	end.

Definition type_of_mvalue (value : mtch_value) :=
	match value with
	| MV_Int _ => T_Int
	| MV_Bool _ => T_Bool
	| MV_Char _ => T_Char
	end.

Definition lookup_type (ident : string) (env : type_env) : option type := env ident.

Fixpoint typecheck_expr (expr : expr) (env : type_env) : option type :=
	match expr with
	| E_Literal value => Some (type_of_evalue value)
	| E_Var ident => lookup_type ident env
	| E_Let x e body =>
	  match (typecheck_and_get_assignments x e) with
	  | Some xs => typecheck_expr body (update_env env xs)
	  | None => None
	  end
	| E_Fn param body => None (* TODO: figure this one out *)
	| E_FnApp fn arg =>
		match (typecheck_expr fn) with
		| Some fn_t =>
		  match fn_t with
		  | T_Function param_t return_t =>
		  	(* TODO: compare param type and arg type to see if they
			         are equal. If they are, return the return type *)
			return_t
		  | None => None
		  end
		| None => None
		end
	| E_If cond t f =>
	  match (typecheck_expr cond) with
	  | T_Bool => T_Union (typecheck_expr t) (typecheck_expr f)
	| E_Match e branches =>
		let e_type := typecheck_expr e in
		typecheck_branches e_type 
		(* TODO: completion check *)
	| E_Binary op x y => _
	| E_Unary op x => _
	end.