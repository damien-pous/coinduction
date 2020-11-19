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

(* TOBEREMOVED *)
Lemma in_pair0 A b (x y: A): t b (pair x y) x y.
Proof. now apply (id_t b), leq_pair. Qed.
Lemma in_pair1 I A b (x y: I -> A): forall i, t b (sup_all (fun i => pair (x i) (y i))) (x i) (y i).
Proof. intros. apply (id_t b). rewrite leq_pair. now repeat eapply eleq_xsup_all. Qed.
Lemma in_pair2 I J A b (x y: forall i: I, J i -> A): forall i j, t b (sup_all (fun i => sup_all (fun j => pair (x i (j i)) (y i (j i))))) (x i (j i)) (y i (j i)).
Proof. intros. apply (id_t b). rewrite leq_pair. now repeat eapply eleq_xsup_all. Qed.
Lemma in_pair3 I J K A b (x y: forall i: I, forall j: J i, K i j -> A): forall i j k, t b (sup_all (fun i => sup_all (fun j => sup_all (fun k => pair (x i (j i) (k i (j i))) (y i (j i) (k i (j i))))))) (x i (j i) (k i (j i))) (y i (j i) (k i (j i))).
Proof. intros. apply (id_t b). rewrite leq_pair. now repeat eapply eleq_xsup_all. Qed.

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


Transparent pair.
Lemma converse_pair A (p q: A): converse (pair p q) == pair q p.
Proof. unfold pair, converse; split; simpl; tauto. Qed.
Global Opaque pair.

Lemma converse_sup S I P (f: I -> relation S):
  converse (sup P f) == sup P (fun i => converse (f i)).
Proof. simpl. firstorder. Qed.
                                                 



(* TOBEREMOVED *)
Module nondep.
  
 Notation T := (list Set).
 
 Fixpoint fT (L: T) A :=
   match L with
   | nil => A
   | cons B Q => B -> fT Q A
   end.
 Fixpoint pT (L: T) A (R: A -> A -> Prop): fT L A -> fT L A -> Prop :=
   match L with
   | nil => R
   | cons B Q => fun x y => forall i, pT Q R (x i) (y i)
   end.
 Fixpoint rT (L: T) A: fT L A -> fT L A -> A -> A -> Prop :=
   match L with
   | nil => @pair A
   | cons B Q => fun x y => sup_all (fun i => rT Q (x i) (y i))
   end.
 Lemma eT (L: T) A R: forall x y: fT L A, pT L R x y <-> rT L x y <= R.
 Proof.
   induction L; intros x y; simpl pT.
   - apply leq_pair.
   - setoid_rewrite IHL. symmetry. apply sup_all_spec. 
 Qed.

 Lemma coinduction: forall L A x y (b: mon (A -> A -> Prop)),
     (forall R, pT L (t b R) x y -> pT L (b (t b R)) x y) ->
     pT L (gfp b) x y.
 Proof.
   intros.
   rewrite eT. apply coinduction.
   rewrite <-eT. apply H.
   rewrite eT. apply id_t. 
 Qed.
 
 Section s.
  Variable b: mon (nat -> nat -> Prop).
  Goal forall n m (* (k: n=m) *), gfp b (n+n) (m+m).
    apply (coinduction
            (cons nat (cons nat nil))
             (fun n m => n+n)
             (fun n m => m+m)             
          ).
    simpl pT. intros R HR. 
  Abort.
 End s.

End nondep.


Module reification.
  
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
 Lemma eT' (L: T) A (x y: fT L A) (b: mon (A -> A -> Prop)): pT L (t b (rT L x y)) x y.
 Proof. rewrite eT. apply id_t. Qed.

 Lemma coinduction L A x y (b: mon (A -> A -> Prop)):
     (forall R, pT L (t b R) x y -> pT L (b (t b R)) x y) ->
     pT L (gfp b) x y.
 Proof.
   intro H.
   rewrite eT. apply coinduction.
   rewrite <-eT. apply H.
   rewrite eT. apply id_t.
 Qed.
 
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

End reification.


(** * Friendly [coinduction] tactic, for relations
 (it just goes back and forth between the above encoding of sets of pairs, 
  and Coq's native symbols)
 *)

Declare ML Module "cawu_reification". 
Ltac coinduction R H :=
  cawu_reify; apply reification.coinduction; simpl reification.pT; intros R H.

(* tests *)
Section s.
  Variables b c: mon (nat -> nat -> Prop).
  Goal gfp b 5 6.
    coinduction R H.
  Abort.
  Goal gfp b 5 6 /\ gfp b 7 8.
    coinduction R H.
  Abort.
  Goal forall n m (k: n=m), gfp b (n+n) (m+m) /\ forall k, gfp b (n+k) (k+m).
    coinduction R H.
  Abort.
  Goal gfp b 5 6 /\ gfp c 7 8.
    Fail cawu_reify.
  Abort.
End s.



Ltac coinduction_old R H :=
  let rec init := 
    lazymatch goal with
    | |- forall x, _ => let x:=fresh x in intro x; init; revert x; rewrite <-sup_all_spec
    | |- gfp _ _ _ =>  rewrite leq_pair
  end in
  init; apply coinduction; 
  match goal with |- ?Rb <= body ?b _ => 
    set (R:=Rb) at -1;
    repeat setoid_rewrite sup_all_spec;
    setoid_rewrite <-leq_pair;
    first
      [ pose proof (in_pair0 b _ _: t b R _ _) as H
      | pose proof (in_pair1 b _ _: forall i, t b R _ _) as H
      | pose proof (in_pair2 b _ _: forall i j, t b R _ _) as H
      | pose proof (in_pair3 b _ _: forall i j k, t b R _ _) as H
      ];
    clearbody R 
  end.

Ltac step :=
  match goal with
  | |- gfp ?b ?x ?y => apply (proj2 (gfp_fp b x y))
  | |- body (t ?b) ?R ?x ?y => apply (bt_t b R x y)
  end;
  simpl body.

Ltac coinduction' R H :=
  cawu_reify; rewrite reification.eT; apply coinduction;
  match goal with |- _ <= body ?b _ =>
  apply by_symmetry; [solve [simpl; firstorder]|];
  rewrite <-reification.eT; set (R := reification.rT _ _ _);
  pose proof (reification.eT' _ _ _ b: reification.pT _ (t b R) _ _) as H;
  clearbody R; simpl reification.pT in *
  end.

Section a.
Variable s: mon (nat -> nat -> Prop). 
Goal forall n m, gfp (cap s (converse o s o converse)) n m.
Proof.
  coinduction' R H. 
Abort.
End a.
  
Ltac solve_sym := solve [
  repeat (rewrite converse_sup; apply sup_spec; intros);
  rewrite converse_pair;
  repeat (eapply eleq_xsup_all; intros);
  trivial ] || idtac "could not get symmetry automatically".

Ltac coinduction_old' R H :=
  let rec init := 
    lazymatch goal with
    | |- forall x, _ => let x:=fresh x in intro x; init; revert x; rewrite <-sup_all_spec
    | |- gfp _ _ _ =>  rewrite leq_pair
  end in
  init; apply coinduction;
  match goal with |- ?Rb <= body ?b _ => 
    set (R:=Rb) at -1; apply by_symmetry; [ solve_sym |
    repeat setoid_rewrite sup_all_spec;
    setoid_rewrite <-leq_pair;
    first
      [ pose proof (in_pair0 b _ _: t b R _ _) as H
      | pose proof (in_pair1 b _ _: forall i, t b R _ _) as H
      | pose proof (in_pair2 b _ _: forall i j, t b R _ _) as H
      | pose proof (in_pair3 b _ _: forall i j k, t b R _ _) as H
      ];
    clearbody R ]
  end.
