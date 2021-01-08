(************************************************************************)
(*     This is part of CAWU, it is distributed under the terms          *)
(*       of the GNU Lesser General Public License version 3             *)
(*                (see file LICENSE for more details)                   *)
(*                                                                      *)
(*  Copyright 2016-2020: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(************************************************************************)

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
    we have that [gfp b], [t R], and [T f R] are always equivalence relations. *)
Section s.
  Variables (A: Type) (b: mon (relation A)).
  Hypothesis eq_t: const eq <= t b.
  Hypothesis converse_t: converse <= t b.
  Hypothesis square_t: square <= t b.
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
End s.


(** [R] is always a subrelation of [t R] and [T f R] *)
Instance rel_gfp_T A b f (R: relation A): subrelation (gfp b) (t (B b) f R).
Proof. refine (gfp_T _ f R). Qed.

Instance rel_gfp_t A b (R: relation A): subrelation (gfp b) (t b R).
Proof. refine (gfp_t _ R). Qed.


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

(** if it is below [t], then the function [f] always preserves [t R] *)
Lemma unary_proper S (f: S -> S) b:
  (unary_ctx f) <= t b -> forall R, Proper (t b R ==> t b R) f.
Proof. intros H R x x' Hx. apply (ft_t H). now apply (in_unary_ctx f). Qed.
 
                                 
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

(** if it is below [t], then the function [f] always preserves [t R] *)
Lemma ternary_proper S (f: S -> S -> S -> S) b:
  ternary_ctx f <= t b -> forall R, Proper (t b R ==> t b R ==> t b R ==> t b R) f.
Proof. intros H R x x' Hx y y' Hy z z' Hz. apply (ft_t H). now apply (in_ternary_ctx f). Qed.


Transparent pair.
Lemma converse_pair A (p q: A): converse (pair p q) == pair q p.
Proof. unfold pair, converse; split; simpl; tauto. Qed.
Global Opaque pair.

Lemma converse_sup S I P (f: I -> relation S):
  converse (sup P f) == sup P (fun i => converse (f i)).
Proof. simpl. firstorder. Qed.
                                                 


(** * reification tools to transform propositions in the language of
      gallina into relation containments, e.g.,

      [forall x y, R (x+y) (y+x+x)]
      becomes 
      [sup_all (fun x => sup_all (fun y => pair (x+y) (y+x+x))) <== R]

      [forall x y, R (x+y) y /\ R x y]
      becomes 
      [sup_all (fun x => sup_all (fun y => cup (pair (x+y) y) (pair x y)))) <== R]

*)
Module reification.

 (* depedently typed syntax for formulas of the shape
    forall x y, R t1 t2 /\ forall z, R s1 s2
  *)
 Inductive T :=
 | hol
 | abs(B: Type)(Q: B -> T)
 | cnj(H K: T).
 Arguments abs _ _: clear implicits. 

 Fixpoint fT (L: T) A :=
   match L with
   | hol => A
   | abs B Q => forall b: B, fT (Q b) A
   | cnj H K => (fT H A * fT K A)%type
   end.
 Fixpoint pT (L: T) A (R: A -> A -> Prop): fT L A -> fT L A -> Prop :=
   match L with
   | hol => R
   | abs B Q => fun x y => forall b, pT (Q b) R (x b) (y b)
   | cnj H K => fun x y => pT H R (fst x) (fst y) /\ pT K R (snd x) (snd y)
   end.
 Fixpoint rT (L: T) A: fT L A -> fT L A -> A -> A -> Prop :=
   match L with
   | hol => @pair A
   | abs B Q => fun x y => sup_all (fun b => rT (Q b) (x b) (y b))
   | cnj H K => fun x y => cup (rT H (fst x) (fst y)) (rT K (snd x) (snd y))
   end.
 Lemma eT (L: T) A R: forall x y: fT L A, pT L R x y <-> rT L x y <= R.
 Proof.
   induction L; intros x y; simpl pT.
   - apply leq_pair.
   - setoid_rewrite H. symmetry. apply sup_all_spec.
   - rewrite IHL1, IHL2. symmetry. apply cup_spec.  
 Qed.
 (* TODO: remove *)
 Lemma eT' (L: T) A (x y: fT L A) (b: mon (A -> A -> Prop)): pT L (t b (rT L x y)) x y.
 Proof. rewrite eT. apply id_t. Qed.

 (** the enhanced coinduction lemma expressed in this reified form *)
 Lemma coinduction L A x y (b: mon (A -> A -> Prop)):
     (forall R, pT L (t b R) x y -> pT L (b (t b R)) x y) ->
     pT L (gfp b) x y.
 Proof.
   intro H.
   rewrite eT. apply coinduction.
   rewrite <-eT. apply H.
   rewrite eT. apply id_t.
 Qed.

 (* idea: the above lemma can be used as follows: *)
 (*
 Section s.
  Variable b: mon (nat -> nat -> Prop).
  Goal forall n m (k: n=m), gfp b (n+n) (m+m) /\ forall k, gfp b (n+k) (k+m).
    apply (coinduction
            (abs nat (fun n =>
             abs nat (fun m => 
             abs (n=m) (fun _ => 
             cnj hol (abs nat (fun _ => hol))))))
             (fun n m _ => (n+n, fun k => n+k))
             (fun n m _ => (m+m, fun k => k+m))             
          ).
    simpl pT. intros R HR. 
  Abort.
 End s.
 *)

End reification.

(** resulting [coinduction] tactic *)
Declare ML Module "cawu_reification". 
Tactic Notation "coinduction" ident(R) simple_intropattern(H) :=
  cawu_reify; apply reification.coinduction; simpl reification.pT; intros R H.


(* TODO: remove? *)
Ltac step :=
  match goal with
  | |- gfp ?b ?x ?y => apply (proj2 (gfp_fp b x y))
  | |- body (t ?b) ?R ?x ?y => apply (bt_t b R x y)
  end;
  simpl body.

(** variant where the implicit bisimulation candidate is symmetric (for symmetric functions only) *)
(* TODO: improve *)
Ltac coinduction' R H :=
  cawu_reify; rewrite reification.eT; apply coinduction;
  match goal with |- _ <= body ?b _ =>
  apply by_symmetry; [solve [simpl; firstorder]|];
  rewrite <-reification.eT; set (R := reification.rT _ _ _);
  pose proof (reification.eT' _ _ _ b: reification.pT _ (t b R) _ _) as H;
  clearbody R; simpl reification.pT in *
  end.


(* old symmetry-solving tactic *)
(*
Ltac solve_sym := solve [
  repeat (rewrite converse_sup; apply sup_spec; intros);
  rewrite converse_pair;
  repeat (eapply eleq_xsup_all; intros);
  trivial ] || idtac "could not get symmetry automatically".
*)

