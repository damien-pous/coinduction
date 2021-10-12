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

Section s.
  Variables (A: Type) (b: mon (relation A)).
  Notation t := (t b).
  Notation T := (T b).
  Notation bt := (bt b).
  Notation bT := (bT b).

  (** [gfp] is always a subrelation of [t R], [bt R], [T f R], and [bT f R] 
      TOTHINK: declare other links in the lattice?
      (bt<=bT<=T and bt<=t<=T)
   *)
  Global Instance subrelation_gfp_T f (R: relation A): subrelation (gfp b) (T f R).
  Proof. refine (gfp_T _ _ R). Qed.
  
  Global Instance subrelation_gfp_t (R: relation A): subrelation (gfp b) (t R).
  Proof. refine (gfp_t _ R). Qed.

  (** the next two are not declared as instances by default, 
      in order to circumvent setoid_rewriting inefficiencies *)
  Lemma subrelation_gfp_bt (R: relation A): subrelation (gfp b) (bt R).
  Proof. refine (gfp_bt _ R). Qed.
  
  Lemma subrelation_gfp_bT f (R: relation A): subrelation (gfp b) (bT f R).
  Proof. refine (gfp_bT _ _ R). Qed.

  (** helpers to prove that relations are reflexive/symmetric/transitive from algebraic properties *)
  Lemma build_reflexive (R: relation A): const eq R <= R -> Reflexive R.
  Proof. intros H x. now apply H. Qed.
  Lemma build_symmetric (R: relation A): converse R <= R -> Symmetric R.
  Proof. intros H x y xy. now apply H. Qed.
  Lemma build_transitive (R: relation A): square R <= R -> Transitive R.
  Proof. intros H x y z xy yz. now apply H; exists y. Qed.
  Lemma build_preorder (R: relation A): const eq R <= R -> square R <= R -> PreOrder R.
  Proof.
    split.
    now apply build_reflexive.
    now apply build_transitive.
  Qed.
  Lemma build_equivalence (R: relation A): const eq R <= R -> converse R <= R -> square R <= R -> Equivalence R.
  Proof.
    split.
    now apply build_reflexive.
    now apply build_symmetric.
    now apply build_transitive.
  Qed.
  
  (** provided that [const eq], [square], and [converse] are below [t], 
    we have that [gfp b], [t R], [bt R], [T f R], and [bT f R] are always equivalence relations. *)
  (* TOTHINK: use the transfer lemmas [Pt_PT, Pt_Pbt, Pt_PbT]? *)
  (* TOTHINK: setup typclasses to avoid repetitions? *)
  Hypothesis eq_t: const eq <= t.
  Hypothesis square_t: square <= t.
  Lemma PreOrder_t R: PreOrder (t R).
  Proof. apply build_preorder; now apply ft_t. Qed.
  Corollary PreOrder_gfp: PreOrder (gfp b).
  Proof. apply PreOrder_t. Qed.
  Lemma PreOrder_T f R: PreOrder (T f R).
  Proof. apply build_preorder; now apply fT_T. Qed.  
  Lemma PreOrder_bt R: PreOrder (bt R).
  Proof. apply build_preorder; now apply fbt_bt. Qed.
  Lemma PreOrder_bT f R: PreOrder (bT f R).
  Proof. apply build_preorder; now apply fbT_bT. Qed.

  Hypothesis converse_t: converse <= t.
  Lemma Equivalence_t R: Equivalence (t R).
  Proof. apply build_equivalence; now apply ft_t. Qed.
  Corollary Equivalence_gfp: Equivalence (gfp b).
  Proof. apply Equivalence_t. Qed.
  Lemma Equivalence_T f R: Equivalence (T f R).
  Proof. apply build_equivalence; now apply fT_T. Qed.
  Lemma Equivalence_bt R: Equivalence (bt R).
  Proof. apply build_equivalence; now apply fbt_bt. Qed.
  Lemma Equivalence_bT f R: Equivalence (bT f R).
  Proof. apply build_equivalence; now apply fbT_bT. Qed.
End s.


(** * Contexts closure functions *)

Section context.
Variable S: Type.
Section unary. 
Variable f: S -> S. 

(** unary context: [unary_ctx f](R) = {(f x, f y) | x R y }  *)
Program Definition unary_ctx: mon (S -> S -> Prop) :=
  {| body R := sup_all (fun x =>
               sup (R x) (fun x' => pair (f x) (f x'))) |}.
Next Obligation.
  Transparent pair. Opaque plus.
  cbv; firstorder subst; eauto.
  Transparent plus. Opaque pair.
Qed.

Lemma leq_unary_ctx R T:
  unary_ctx R <= T <-> forall x x', R x x' -> T (f x) (f x').
Proof.
  unfold unary_ctx. setoid_rewrite sup_all_spec.
  setoid_rewrite sup_spec.
  setoid_rewrite <-leq_pair. firstorder. 
Qed.
Lemma in_unary_ctx (R: S -> S -> Prop) x x':
  R x x' -> unary_ctx R (f x) (f x').
Proof. intros. now apply ->leq_unary_ctx. Qed.
Global Opaque unary_ctx.

(** context functions are always symmetric *)
Lemma unary_sym: compat converse unary_ctx.
Proof. intro R. simpl. apply leq_unary_ctx. intros. now apply in_unary_ctx. Qed.

(** helper lemmas to prove that a unary context function is below the companion *)
Lemma unary_ctx_b b c:
  unary_ctx ° b <= c <-> forall R, Proper (b R ==> c R) f.
Proof.
  split; intro H.
  - intros R p q pq. apply H. now apply in_unary_ctx.
  - intro R. apply leq_unary_ctx. apply H.
Qed.
Corollary unary_ctx_t (b: mon (S -> S -> Prop)):
  (forall R, Proper (b R ==> bT b unary_ctx R) f) ->
  unary_ctx <= t b.
Proof. intro H. apply Coinduction. now apply unary_ctx_b. Qed.
Corollary unary_ctx_t_sym_ (b s: mon (S -> S -> Prop)) {H: Sym_from converse b s}:
  (forall R, Proper (b R ==> s (T b unary_ctx R)) f) ->
  unary_ctx <= t b.
Proof. intro. apply Coinduction, by_Symmetry. apply unary_sym. now apply unary_ctx_b. Qed.


(** if it is below [t], then the function [f] always preserves [t R], [bt R], [T f R], [bT f R] *)
Lemma unary_proper_t b:
  unary_ctx <= t b -> forall R, Proper (t b R ==> t b R) f.
Proof. intros H R x x' Hx. apply (ft_t H). now apply in_unary_ctx. Qed.
Lemma unary_proper_bt b:
  unary_ctx <= t b -> forall R, Proper (bt b R ==> bt b R) f.
Proof. intros H R x x' Hx. apply (fbt_bt H). now apply in_unary_ctx. Qed.
Lemma unary_proper_T b g:
  unary_ctx <= t b -> forall R, Proper (T b g R ==> T b g R) f.
Proof. intros H R x x' Hx. apply (fT_T H). now apply in_unary_ctx. Qed.
Lemma unary_proper_bT b g:
  unary_ctx <= t b -> forall R, Proper (bT b g R ==> bT b g R) f.
Proof. intros H R x x' Hx. apply (fbT_bT H). now apply in_unary_ctx. Qed.

Global Instance unary_proper_Tctx b R:
  Proper (T b unary_ctx R ==> T b unary_ctx R) f.
Proof. intros x x' Hx. apply (fTf_Tf b). now apply in_unary_ctx. Qed.

End unary.
Section binary. 
Variable f: S -> S -> S. 
                                 
(** binary context: [unary_ctx f](R) = {(f x x', f y y') | x R y, x' R y' }  *)
Program Definition binary_ctx: mon (S -> S -> Prop) :=
  {| body R := sup_all (fun x =>
               sup_all (fun y => 
               sup (R x) (fun x' => 
               sup (R y) (fun y' => pair (f x y) (f x' y'))))) |}.
Next Obligation.
  Transparent pair. Opaque plus.
  cbv; firstorder subst; eauto 8.
  Transparent plus. Opaque pair.
Qed.

Lemma leq_binary_ctx R T:
  binary_ctx R <= T <-> forall x x', R x x' -> forall y y', R y y' -> T (f x y) (f x' y').
Proof.
  unfold binary_ctx. do 2 setoid_rewrite sup_all_spec.
  do 2 setoid_rewrite sup_spec.
  setoid_rewrite <-leq_pair. firstorder. 
Qed.
Lemma in_binary_ctx (R: S -> S -> Prop) x x' y y':
  R x x' -> R y y' -> binary_ctx R (f x y) (f x' y').
Proof. intros. now apply ->leq_binary_ctx. Qed.
Global Opaque binary_ctx.

(** such a function is always symmetric *)
Lemma binary_sym: compat converse binary_ctx.
Proof. intro R. simpl. apply leq_binary_ctx. intros. now apply in_binary_ctx. Qed.

(** helper lemmas to prove that a binary context function is below the companion *)
Lemma binary_ctx_b b c:
  binary_ctx ° b <= c  <-> forall R, Proper (b R ==> b R ==> c R) f.
Proof.
  split; intro H.
  - intros R p q pq u v uv. apply H. now apply in_binary_ctx.
  - intro R. apply leq_binary_ctx. apply H.
Qed.
Corollary binary_ctx_t (b: mon (S -> S -> Prop)):
  (forall R, Proper (b R ==> b R ==> bT b binary_ctx R) f) ->
  binary_ctx <= t b.
Proof. intro H. apply Coinduction. now apply binary_ctx_b. Qed.
Corollary binary_ctx_t_sym_ (b s: mon (S -> S -> Prop)) {H: Sym_from converse b s}:
  (forall R, Proper (b R ==> b R ==> s (T b binary_ctx R)) f) ->
  binary_ctx <= t b.
Proof. intro. apply Coinduction, by_Symmetry. apply binary_sym. now apply binary_ctx_b. Qed.

(** if it is below [t], then the function [f] always preserves [t R], [bt R], [T f R], [bT f R] *)
Lemma binary_proper_t b:
  binary_ctx <= t b -> forall R, Proper (t b R ==> t b R ==> t b R) f.
Proof. intros H R x x' Hx y y' Hy. apply (ft_t H). now apply in_binary_ctx. Qed.
Lemma binary_proper_bt b:
  binary_ctx <= t b -> forall R, Proper (bt b R ==> bt b R ==> bt b R) f.
Proof. intros H R x x' Hx y y' Hy. apply (fbt_bt H). now apply in_binary_ctx. Qed.
Lemma binary_proper_T b g:
  binary_ctx <= t b -> forall R, Proper (T b g R ==> T b g R ==> T b g R) f.
Proof. intros H R x x' Hx y y' Hy. apply (fT_T H). now apply in_binary_ctx. Qed.
Lemma binary_proper_bT b g:
  binary_ctx <= t b -> forall R, Proper (bT b g R ==> bT b g R ==> bT b g R) f.
Proof. intros H R x x' Hx y y' Hy. apply (fbT_bT H). now apply in_binary_ctx. Qed.

Global Instance binary_proper_Tctx b R:
  Proper (T b binary_ctx R ==> T b binary_ctx R ==> T b binary_ctx R) f.
Proof. intros x x' Hx y y' Hy. apply (fTf_Tf b). now apply in_binary_ctx. Qed.

End binary.
Section ternary. 
Variable f: S -> S -> S -> S. 

                                 
(** ternary context: [ternary_ctx f](R) = {(f x x' x'', f y y' y'') | x R y, x' R y', x'' R y'' }  *)
Program Definition ternary_ctx: mon (S -> S -> Prop) :=
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

Lemma leq_ternary_ctx R T:
  ternary_ctx R <= T <->
  forall x x', R x x' -> forall y y', R y y' -> forall z z', R z z' -> T (f x y z) (f x' y' z').
Proof.
  unfold ternary_ctx. do 3 setoid_rewrite sup_all_spec.
  do 3 setoid_rewrite sup_spec.
  setoid_rewrite <-leq_pair. firstorder. 
Qed.
Lemma in_ternary_ctx (R: S -> S -> Prop) x x' y y' z z':
  R x x' -> R y y' -> R z z' -> ternary_ctx R (f x y z) (f x' y' z').
Proof. intros. now apply ->leq_ternary_ctx. Qed.
Global Opaque ternary_ctx.

(** such a function is always symmetric *)
Lemma ternary_sym: compat converse ternary_ctx.
Proof. intro R. simpl. apply leq_ternary_ctx. intros. now apply in_ternary_ctx. Qed.

(** helper lemmas to prove that a ternary context function is below the companion *)
Lemma ternary_ctx_b b c:
  ternary_ctx ° b <= c <-> forall R, Proper (b R ==> b R ==> b R ==> c R) f.
Proof.
  split; intro H.
  - intros R p q pq u v uv s t st. apply H. now apply in_ternary_ctx.
  - intro R. apply leq_ternary_ctx. apply H.
Qed.
Corollary ternary_ctx_t (b: mon (S -> S -> Prop)):
  (forall R, Proper (b R ==> b R ==> b R ==> bT b ternary_ctx R) f) ->
  ternary_ctx <= t b.
Proof. intro H. apply Coinduction. now apply ternary_ctx_b. Qed.
Corollary ternary_ctx_t_sym_ (b s: mon (S -> S -> Prop)) {H: Sym_from converse b s}:
  (forall R, Proper (b R ==> b R ==> b R ==> s (T b ternary_ctx R)) f) ->
  ternary_ctx <= t b.
Proof. intro. apply Coinduction, by_Symmetry. apply ternary_sym. now apply ternary_ctx_b. Qed.

(** if it is below [t], then the function [f] always preserves [t R], [bt R], [T f R], [bT f R] *)
Lemma ternary_proper_t b:
  ternary_ctx <= t b -> forall R, Proper (t b R ==> t b R ==> t b R ==> t b R) f.
Proof. intros H R x x' Hx y y' Hy z z' Hz. apply (ft_t H). now apply in_ternary_ctx. Qed.
Lemma ternary_proper_bt b:
  ternary_ctx <= t b -> forall R, Proper (bt b R ==> bt b R ==> bt b R ==> bt b R) f.
Proof. intros H R x x' Hx y y' Hy z z' Hz. apply (fbt_bt H). now apply in_ternary_ctx. Qed.
Lemma ternary_proper_T b g:
  ternary_ctx <= t b -> forall R, Proper (T b g R ==> T b g R ==> T b g R ==> T b g R) f.
Proof. intros H R x x' Hx y y' Hy z z' Hz. apply (fT_T H). now apply in_ternary_ctx. Qed.
Lemma ternary_proper_bT b g:
  ternary_ctx <= t b -> forall R, Proper (bT b g R ==> bT b g R ==> bT b g R ==> bT b g R) f.
Proof. intros H R x x' Hx y y' Hy z z' Hz. apply (fbT_bT H). now apply in_ternary_ctx. Qed.

Global Instance ternary_proper_Tctx b R:
  Proper (T b ternary_ctx R ==> T b ternary_ctx R ==> T b ternary_ctx R ==> T b ternary_ctx R) f.
Proof. intros x x' Hx y y' Hy z z' Hz. apply (fTf_Tf b). now apply in_ternary_ctx. Qed.

End ternary.
End context.

(** reexporting those three lemmas with different argument order to help typeclasss resolution *)
Definition unary_ctx_t_sym {S b s H} f := @unary_ctx_t_sym_ S f b s H. 
Definition binary_ctx_t_sym {S b s H} f := @binary_ctx_t_sym_ S f b s H. 
Definition ternary_ctx_t_sym {S b s H} f := @ternary_ctx_t_sym_ S f b s H. 

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

Lemma converse_square S (R: relation S):
  converse (square R) == square (converse R).
Proof. simpl. firstorder. Qed.
