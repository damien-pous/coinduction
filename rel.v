(** * Utilities for working with binary relations  *)

Require Import coinduction.
Set Implicit Arguments.
  

(** * Generic definitions and results about relations *)

(** pairs and sets of pairs *)

Definition pair A (x y: A) := fun x' y' => x=x' /\ y=y'.
Lemma leq_pair A (x y: A) (R: A -> A -> Prop): R x y <-> pair x y <= R.
Proof. firstorder congruence. Qed.
Global Opaque pair.

(** squaring function *)
Program Definition square {A}: mon (A -> A -> Prop) :=
  {| body R x y := exists2 z, R x z & R z y |}.
Next Obligation. cbv. firstorder. Qed. 

(** converse function (an involution) *)
Program Definition converse {A}: mon (A -> A -> Prop) :=
  {| body R x y := R y x |}.
Next Obligation. cbv. firstorder. Qed. 

Instance Involution_converse {A}: Involution (@converse A).
Proof. now intros ? ?. Qed.

(** provided that [const eq], [square], and [converse] are below [t], 
    we have that [gfp b], [t R], [bt R] and [T f R] are always equivalence relations. *)
(* TOTHINK: also [b (T f R)], useful? *)
Section s.
  Variables (A: Type) (b: mon (relation A)).
  Hypothesis eq_t: const eq <= t b.
  Hypothesis square_t: square <= t b.
  Lemma PreOrder_T f R: PreOrder (t (B b) f R).
  Proof.
    constructor.
    intro. now apply (ftT_T f eq_t).
    intros ? y ???. apply (ftT_T f square_t). exists y; assumption.
  Qed.
  Lemma PreOrder_t R: PreOrder (t b R).
  Proof.
    constructor.
    intro. now apply (ft_t eq_t).
    intros ? y ???. apply (ft_t square_t). exists y; assumption.
  Qed.
  Corollary PreOrder_gfp: PreOrder (gfp b).
  Proof PreOrder_t bot.
  Lemma PreOrder_bt R: PreOrder (bt b R).
  Proof.
    constructor.
    intro. now apply (fbt_bt eq_t).
    intros ? y ???. apply (fbt_bt square_t). exists y; assumption.
  Qed.

  Hypothesis converse_t: converse <= t b.
  Lemma Equivalence_T f R: Equivalence (t (B b) f R).
  Proof.
    constructor.
    intro. now apply (ftT_T f eq_t).
    intros x y. apply (ftT_T f converse_t).
    intros ? y ???. apply (ftT_T f square_t). exists y; assumption.
  Qed.
  Lemma Equivalence_t R: Equivalence (t b R).
  Proof.
    constructor.
    intro. now apply (ft_t eq_t).
    intros x y. apply (ft_t converse_t).
    intros ? y ???. apply (ft_t square_t). exists y; assumption.
  Qed.
  Corollary Equivalence_gfp: Equivalence (gfp b).
  Proof Equivalence_t bot.
  Lemma Equivalence_bt R: Equivalence (bt b R).
  Proof.
    constructor.
    intro. now apply (fbt_bt eq_t).
    intros x y. apply (fbt_bt converse_t).
    intros ? y ???. apply (fbt_bt square_t). exists y; assumption.
  Qed.
End s.


(** [gfp] is always a subrelation of [t R], [bt R] and [T f R] *)
Instance rel_gfp_T A b f (R: relation A): subrelation (gfp b) (t (B b) f R).
Proof. refine (gfp_T _ f R). Qed.

Instance rel_gfp_t A b (R: relation A): subrelation (gfp b) (t b R).
Proof. refine (gfp_t _ R). Qed.

Instance rel_gfp_bt A b (R: relation A): subrelation (gfp b) (bt b R).
Proof.
  intros x y H. apply (gfp_pfp b) in H.
  revert H. apply b. apply rel_gfp_t.
Qed.


(** * Contexts *)

(** unary context: [unary_ctx f](R) = {(f x, f y) | x R y }  *)
Program Definition unary_ctx S (f: S -> S): mon (S -> S -> Prop) :=
  {| body R := sup_all (fun x =>
               sup (R x) (fun x' => pair (f x) (f x'))) |}.
Next Obligation.
  Transparent pair. Opaque plus.
  cbv; firstorder subst; eauto.
  Transparent plus. Opaque pair.
Qed.

Lemma leq_unary_ctx S f R T:
  @unary_ctx S f R <= T <-> forall x x', R x x' -> T (f x) (f x').
Proof.
  unfold unary_ctx. setoid_rewrite sup_all_spec.
  setoid_rewrite sup_spec.
  setoid_rewrite <-leq_pair. firstorder. 
Qed.
Lemma in_unary_ctx S (f: S -> S) (R: S -> S -> Prop) x x':
  R x x' -> unary_ctx f R (f x) (f x').
Proof. intros. now apply ->leq_unary_ctx. Qed.
Global Opaque unary_ctx.

(** such a function is always symmetric *)
Lemma unary_sym S (f: S -> S): compat converse (unary_ctx f).
Proof. intro R. simpl. apply leq_unary_ctx. intros. now apply in_unary_ctx. Qed.

(** if it is below [t], then the function [f] always preserves [t R] and [bt R]*)
Lemma unary_proper S (f: S -> S) b:
  unary_ctx f <= t b -> forall R, Proper (t b R ==> t b R) f.
Proof. intros H R x x' Hx. apply (ft_t H). now apply (in_unary_ctx f). Qed.
Lemma unary_proper_bt S (f: S -> S) b:
  unary_ctx f <= t b -> forall R, Proper (bt b R ==> bt b R) f.
Proof. intros H R x x' Hx. apply (fbt_bt H). now apply (in_unary_ctx f). Qed.

                                 
(** binary context: [unary_ctx f](R) = {(f x x', f y y') | x R y, x' R y' }  *)
Program Definition binary_ctx S (f: S -> S -> S): mon (S -> S -> Prop) :=
  {| body R := sup_all (fun x =>
               sup_all (fun y => 
               sup (R x) (fun x' => 
               sup (R y) (fun y' => pair (f x y) (f x' y'))))) |}.
Next Obligation.
  Transparent pair. Opaque plus.
  cbv; firstorder subst; eauto 8.
  Transparent plus. Opaque pair.
Qed.

Lemma leq_binary_ctx S f R T:
  @binary_ctx S f R <= T <-> forall x x', R x x' -> forall y y', R y y' -> T (f x y) (f x' y').
Proof.
  unfold binary_ctx. do 2 setoid_rewrite sup_all_spec.
  do 2 setoid_rewrite sup_spec.
  setoid_rewrite <-leq_pair. firstorder. 
Qed.
Lemma in_binary_ctx S (f: S -> S -> S) (R: S -> S -> Prop) x x' y y':
  R x x' -> R y y' -> binary_ctx f R (f x y) (f x' y').
Proof. intros. now apply ->leq_binary_ctx. Qed.
Global Opaque binary_ctx.

(** such a function is always symmetric *)
Lemma binary_sym S (f: S -> S -> S): compat converse (binary_ctx f).
Proof. intro R. simpl. apply leq_binary_ctx. intros. now apply in_binary_ctx. Qed.

(** if it is below [t], then the function [f] always preserves [t R] *)
Lemma binary_proper S (f: S -> S -> S) b:
  binary_ctx f <= t b -> forall R, Proper (t b R ==> t b R ==> t b R) f.
Proof. intros H R x x' Hx y y' Hy. apply (ft_t H). now apply (in_binary_ctx f). Qed.
Lemma binary_proper_bt S (f: S -> S -> S) b:
  binary_ctx f <= t b -> forall R, Proper (bt b R ==> bt b R ==> bt b R) f.
Proof. intros H R x x' Hx y y' Hy. apply (fbt_bt H). now apply (in_binary_ctx f). Qed.

                                 
(** ternary context: [unary_ctx f](R) = {(f x x', f y y') | x R y, x' R y' }  *)
Program Definition ternary_ctx S (f: S -> S -> S -> S): mon (S -> S -> Prop) :=
  {| body R := sup_all (fun x =>
               sup_all (fun y => 
               sup_all (fun z => 
               sup (R x) (fun x' => 
               sup (R y) (fun y' => 
               sup (R z) (fun z' => pair (f x y z) (f x' y' z'))))))) |}.
Next Obligation.
  Transparent pair. Opaque plus.
  cbv; firstorder subst; eauto 8.
  Transparent plus. Opaque pair.
Qed.

Lemma leq_ternary_ctx S f R T:
  @ternary_ctx S f R <= T <->
  forall x x', R x x' -> forall y y', R y y' -> forall z z', R z z' -> T (f x y z) (f x' y' z').
Proof.
  unfold ternary_ctx. do 3 setoid_rewrite sup_all_spec.
  do 3 setoid_rewrite sup_spec.
  setoid_rewrite <-leq_pair. firstorder. 
Qed.
Lemma in_ternary_ctx S (f: S -> S -> S -> S) (R: S -> S -> Prop) x x' y y' z z':
  R x x' -> R y y' -> R z z' -> ternary_ctx f R (f x y z) (f x' y' z').
Proof. intros. now apply ->leq_ternary_ctx. Qed.
Global Opaque ternary_ctx.

(** such a function is always symmetric *)
Lemma ternary_sym S (f: S -> S -> S -> S): compat converse (ternary_ctx f).
Proof. intro R. simpl. apply leq_ternary_ctx. intros. now apply in_ternary_ctx. Qed.

(** if it is below [t], then the function [f] always preserves [t R] and [bt R] *)
Lemma ternary_proper S (f: S -> S -> S -> S) b:
  ternary_ctx f <= t b -> forall R, Proper (t b R ==> t b R ==> t b R ==> t b R) f.
Proof. intros H R x x' Hx y y' Hy z z' Hz. apply (ft_t H). now apply (in_ternary_ctx f). Qed.
Lemma ternary_proper_bt S (f: S -> S -> S -> S) b:
  ternary_ctx f <= t b -> forall R, Proper (bt b R ==> bt b R ==> bt b R ==> bt b R) f.
Proof. intros H R x x' Hx y y' Hy z z' Hz. apply (fbt_bt H). now apply (in_ternary_ctx f). Qed.


Transparent pair.
Lemma converse_pair A (p q: A): converse (pair p q) == pair q p.
Proof. unfold pair, converse; split; simpl; tauto. Qed.
Global Opaque pair.

Lemma converse_sup S I P (f: I -> relation S):
  converse (sup P f) == sup P (fun i => converse (f i)).
Proof. simpl. firstorder. Qed.

Lemma converse_cup S (R R': relation S):
  converse (cup R R') == cup (converse R) (converse R').
Proof. simpl. firstorder. Qed.
