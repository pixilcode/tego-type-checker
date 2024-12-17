Inductive type : Type :=
| T_Int : type (* 1 *)
| T_Char : type (* 'a' *)
| T_Bool : type (* true *)
| T_Unit : type (* () *)
| T_Function : type (* param *) -> type (* return *) -> type (* fn x -> y *)
| T_Union : type -> type -> type (* x | y *)
.

Definition atomic t :=
  match t with
  | T_Int
  | T_Char
  | T_Bool
  | T_Unit => True
  
  | T_Function _ _
  | T_Union _ _ => False
  end.

Definition composite t := ~(atomic t).

(* added later when I realized I needed this to make subtyping work *)
Reserved Notation " t '~=' t' " (at level 50).

Inductive tequiv : type -> type -> Prop :=
| TE_refl : forall t, t ~= t
| TE_symm : forall t1 t2,
  t1 ~= t2 ->
  t2 ~= t1
| TE_trans : forall t1 t2 t3,
  t1 ~= t2 ->
  t2 ~= t3 ->
  t1 ~= t3
| TE_union_assoc : forall t1 t2 t,
  T_Union t1 t2 ~= t ->
  T_Union t2 t1 ~= t
| TE_union_comm : forall t1 t2 t3 t,
  T_Union (T_Union t1 t2) t3 ~= t ->
  T_Union t1 (T_Union t2 t3) ~= t
| TE_union : forall t1 t1' t2 t2' t,
  t1 ~= t1' ->
  t2 ~= t2' ->
  T_Union t1 t2 ~= t ->
  T_Union t1' t2' ~= t
| TE_union_merge : forall t1 t2 t,
  t1 ~= t ->
  t2 ~= t ->
  T_Union t1 t2 ~= t
| TE_function : forall t1 t1' t2 t2' t,
  t1 ~= t1' ->
  t2 ~= t2' ->
  T_Function t1 t2 ~= t ->
  T_Function t1' t2' ~= t
where " t '~=' t' " := (tequiv t t').

Example tequiv1 : T_Int ~= T_Int.
Proof. apply TE_refl. Qed.

Example tequiv2 : T_Union T_Int T_Bool ~= T_Union T_Int T_Bool.
Proof. apply TE_refl. Qed.

Example tequiv3 : T_Union T_Int T_Bool ~= T_Union T_Bool T_Int.
Proof. apply TE_union_assoc. apply TE_refl. Qed.

Example tequiv4 :
    T_Union T_Int (T_Union T_Char T_Bool) ~=
    T_Union (T_Union T_Int T_Char) T_Bool.
Proof. apply TE_union_comm. apply TE_refl. Qed.

Example tequiv5 : T_Int ~= (T_Union T_Int T_Int).
Proof. apply TE_symm. apply TE_union_merge; apply TE_refl. Qed.

(* TODO: use tequiv in the subtype definition *)

(*
  When I chose to add T_Union, it introduced the idea of a subtype,
  so I had to define what that concept meant.
*)

Reserved Notation " t '<:' t' " (at level 50).

Inductive is_subtype : type -> type -> Prop :=
| TST_refl : forall t, t <: t
| TST_equiv : forall t1 t2 t3 t4,
  t1 ~= t2 ->
  t3 ~= t4 ->
  t1 <: t3 ->
  t2 <: t4
| TST_union_left : forall t t1 t2,
  t <: t1 ->
	t <: (T_Union t1 t2)
| TST_union_right : forall t t1 t2,
  t <: t2 ->
	t <: (T_Union t1 t2)
(* | TST_union_union : forall t1 t2 t,
  t1 <: t ->
  t2 <: t ->
  (T_Union t1 t2) <: t *)
| TST_union_factor : forall t1 t2 t,
  (T_Union t1 t2) <: t ->
  t1 <: t
| TST_function : forall t1 t2 t3 t4,
	t3 <: t1 -> (* input widening, contravariant *)
	t2 <: t4 -> (* output narrowing, covariant *)
	(T_Function t1 t2) <: (T_Function t3 t4)
where " t '<:' t' " := (is_subtype t t').

Theorem TST_atomic_subtype : forall t t',
  atomic t' ->
  t <: t' ->
  t ~= t'.
Proof.
  intros t t' Ht'.
  generalize dependent t.
  destruct t';
  destruct Ht' as [];
  intros t Ht.
  - inversion Ht; subst.
    + apply TE_refl.
    +  
Qed.

Theorem TST_equiv_left : forall t1 t2 t,
  t1 ~= t2 ->
  t1 <: t ->
  t2 <: t.
Proof.
  intros t1 t2 t H_equiv H_sub.
  eapply TST_equiv.
  - apply H_equiv.
  - apply TE_refl.
  - apply H_sub.
Qed.

Theorem TST_equiv_right : forall t t1 t2,
  t1 ~= t2 ->
  t <: t1 ->
  t <: t2.
Proof.
  intros t t1 t2 H_equiv H_sub.
  eapply TST_equiv.
  - apply TE_refl.
  - apply H_equiv.
  - apply H_sub.
Qed.

(* can TST_union_union be derived? *)
(* does assoc need to be given? *)

Theorem TST_union_assoc : forall t1 t2 t,
  (T_Union t1 t2) <: t ->
  (T_Union t2 t1) <: t.
Proof.
  intros t1 t2 t H.
  eapply TST_equiv_left.
  - apply TE_union_assoc.
    apply TE_refl.
  - assumption. 
Qed.

Theorem TST_union_union : forall t1 t2 t,
  t1 <: t ->
  t2 <: t ->
  (T_Union t1 t2) <: t.
Proof.
  intros t1 t2 t Ht1 Ht2.
  destruct t.
  - inversion Ht1; subst.
Qed.

Theorem TST_union_union' : forall t1 t2 t3 t4,
  t1 <: (T_Union t3 t4) ->
  t2 <: (T_Union t3 t4) ->
	(T_Union t1 t2) <: (T_Union t3 t4).
Proof.
  intros.
  apply TST_union_union; assumption.
Qed.

Theorem TST_union_factor' : forall t1 t2 t3 t4,
  (T_Union t1 t2) <: (T_Union t3 t4) ->
  t1 <: (T_Union t3 t4).
Proof.
  intros.
  eapply TST_union_factor.
  apply H.
Qed.

Theorem TST_function_return : forall t t1 t2,
	t1 <: t2 ->
	(T_Function t t1) <: (T_Function t t2).
Proof.
	intros.
	apply TST_function.
	- apply TST_refl.
	- apply H.
Qed.

Theorem TST_function_param : forall t1 t2 t,
	t2 <: t1 ->
  (T_Function t1 t) <: (T_Function t2 t).
Proof.
  intros.
  apply TST_function.
  - apply H.
  - apply TST_refl.
Qed.

Theorem TST_union_factor_both : forall t1 t2 t3 t4,
  (T_Union t1 t2) <: (T_Union t3 t4) ->
  t1 <: (T_Union t3 t4) /\ t2 <: (T_Union t3 t4).
Proof.
  intros.
  split.
  - apply TST_union_factor in H.
    assumption.
  - apply TST_union_assoc in H.
    apply TST_union_factor in H.
    assumption.
Qed.

Theorem TST_union_either : forall t t1 t2,
  t <: (T_Union t1 t2) ->
  t <: t1 \/ t <: t2.
Proof.
Admitted.

(* factoring (failed) *)
Theorem is_subtype_union__union_left : forall t1 t2 t3 t4,
  (T_Union t1 t2) <: (T_Union t3 t4) ->
  t1 <: (T_Union t3 t4).
Proof.
  intros.
  inversion H; subst.
  - admit.
Abort.

(* associative property (failed) *)
Theorem is_subtype_assoc : forall t1 t2 t,
  (T_Union t1 t2) <: t (* T_Union t3 t4 *) <->
  (T_Union t2 t1) <: t (* T_Union t3 t4 *).
Proof.
  (* split;
  intros.
  - inversion H; subst.
    * apply TST_union_both.
      + right. constructor.
      + left. constructor.
    * destruct H0. 
      + inversion H0; subst.
        -- apply TST_union_both;
           left;
           apply TST_union_right.
           ** right. apply TST_refl.
           ** left. apply TST_refl.
        -- apply  *)

Abort.

Theorem TST_merge : forall t1 t2 t,
  t1 <: t ->
  t2 <: t ->
  T_Union t1 t2 <: t.
Proof.
  intros.
  generalize dependent t2.
  induction H; intros.
  - apply TST_union_union.
    + constructor.
    + assumption.
  - apply TST_union_union.
    + apply TST_union_left.
      apply TST_union_factor with t.
      apply IHis_subtype.
      apply H.
    + assumption.
  - apply TST_union_union.
    + apply TST_union_right.
      apply TST_union_factor with t.
      apply IHis_subtype.
      apply H.
    + assumption.
  - apply TST_union_union.
    + apply TST_union_union; assumption.
    + assumption.
  - apply TST_union_union.
    + eapply TST_union_factor.
      apply H.
    + assumption.
  - apply TST_union_union.
    + apply TST_union_assoc.
      assumption.
    + assumption.
  - apply TST_union_union.
    + apply TST_function; assumption. 
    + assumption. 
Qed.


Theorem is_subtype_trans : forall t1 t2 t3,
  t1 <: t2 ->
  t2 <: t3 ->
  t1 <: t3.
Proof.
  intros t1 t2 t3 H12 H23.
  generalize dependent t1.
  induction H23; intros.
  - assumption.
  - apply TST_union_left.
    apply IHis_subtype.
    assumption.
  - apply TST_union_right.
    apply IHis_subtype.
    assumption.
  - apply TST_union_either in H12.
    destruct H12.
    + apply IHis_subtype1. assumption.
    + apply IHis_subtype2. assumption.
  - apply IHis_subtype.
    apply TST_union_left.
    assumption.
  - apply IHis_subtype.
    inversion H12; subst.
    + apply TST_union_union.
      * apply IHis_subtype1.
        constructor.
      * apply IHis_subtype2.
        constructor.
    + apply IHis_subtype1.
      assumption.
    + apply IHis_subtype2.
      assumption.
    + remember (TST_merge _ _ _ H23_ H23_0) as H12t.
    + inversion H; inversion H0; subst;
      apply TST_union_union;
      try apply TST_union_union;
      try (apply IHis_subtype1; assumption);
      try (apply IHis_subtype2; assumption);
      try assumption.
      * apply TST_union_union; apply TST_union_union; assumption.
      * 
    (* + assert (H'' : forall t', t' <: t1 \/ t' <: t2 -> t' <: t).
      { intros. destruct H1.
        - apply IHis_subtype1. assumption.
        - apply IHis_subtype2. assumption.
      }

      apply H''.
    + apply TST_union_union.
      * inversion H2; subst.
        -- apply TST_union_union; assumption.
        -- apply IHis_subtype1. assumption.
        -- apply IHis_subtype2. assumption.
        --  *)
  (* - apply TST_union_union
    with t1 t2 t3 t4 in H23_.
    + apply TST_union_union
      with t1 t2 t3 t4 in H23_0.
    + assumption. *)
  (* intros t1 t2 t3 H12 H23.
  generalize dependent t3.
  induction H12.
  - intros. assumption.
  - intros t3 H23.
    
  - intros.
    apply .  *)
  (* generalize dependent t1.
  induction t3. *)
  (* generalize dependent t3.
  induction H12; subst.
  - intros. assumption.
  - intros.
    inversion H23; subst.
    + apply TST_union_right.
      apply H.

    + constructor.
      assumption.
    + constructor.
      destruct H as [H | H].
      *  
      right.
      admit. *)
Qed.

Example is_subtype1 : T_Int <: T_Int.
Proof. apply TST_refl. Qed.

Example is_subtype2 : T_Int <: (T_Union T_Bool T_Int).
Proof. apply TST_union_right. right. apply TST_refl. Qed.

Example is_subtype3 :
		(T_Union T_Bool T_Int) <:
		(T_Union T_Char (T_Union T_Bool T_Int)).
Proof. apply TST_union_right. right. apply TST_refl. Qed.

Example is_subtype4 :
  (T_Union T_Bool T_Int) <:
		(T_Union T_Int T_Bool).
Proof.
	apply TST_union_both.
	- apply TST_union_right. right. apply TST_refl.
	- apply TST_union_right. left. apply TST_refl.
Qed.

Example is_subtype5 :
  (T_Function T_Int T_Int) <:
		(T_Function T_Int (T_Union T_Int T_Bool)).
Proof.
  apply TST_function_return.
  apply TST_union_right.
  left.
  apply TST_refl.
Qed.

Example is_subtype6 :
  (T_Function (T_Union T_Int T_Char) T_Int) <:
    (T_Function T_Int T_Int).
Proof.
  apply TST_function_param.
  apply TST_union_right.
  left.
  apply TST_refl.
Qed.

(*
  I also need to define equivalence, which I do using is_subtype, since
  that is equivalent to the "less than/equal to" operator
*)

(* Definition tequiv (t1 t2 : type) : Prop :=
  t1 <: t2 /\ t2 <: t1.

Theorem tequiv_refl : forall t, tequiv t t.
Proof.
  intros.
  unfold tequiv.
  split; apply TST_refl.
Qed.

Theorem tequiv_symm : forall t1 t2,
  tequiv t1 t2 -> tequiv t2 t1.
Proof.
  unfold tequiv.
  intros t1 t2 [H12 H21].
  split; assumption.
Qed.

Theorem tequiv_trans : forall t1 t2 t3,
  tequiv t1 t2 ->
  tequiv t2 t3 ->
  tequiv t1 t3.
Proof.
  unfold tequiv.
  intros t1 t2 t3 [H12 H21] [H23 H32].
  split.
Qed. *)

(* Definition type_union (t1 t2 : type) : type :=
	match t1, t2 with
	| T_Int, T_Int => T_Int
	| T_Char, T_Char => T_Char
	| T_Bool, T_Bool => T_Bool
	| T_Unit, T_Unit => T_Unit
	| T_Function param1_t return1_t,
	  T_Function param2_t return2_t => (* TODO: make this possibly better? *)
	    T_Union false false false false (t1 :: t2 :: nil)
	| T_Union has_int1 has_char1 has_bool1 has_unit1 functions1,
	  T_Union has_int2 has_char2 has_bool2 has_unit2 functions2 =>
	  T_Union
	  	(has_int1 or has_int2)
	  	(has_int1 or has_int2)
	  	(has_int1 or has_int2)
	  	(has_int1 or has_int2)
	| T_Union t1l t1r, t2 => T_Union t1 t2 (* TODO: make this possibly better? *)
	| t1, T_Union t2l t2r => T_Union t1 t2 (* TODO: make this possibly better? *)
	end.

Definition normalize_type_union (t1 t2 : type) : type. Admitted. *)
