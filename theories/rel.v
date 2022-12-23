(** * Utilities for working with binary relations  *)

Require Import tower.
Set Implicit Arguments.

(* TODO: 
   - sharing with relation algebra
 *)
  

(** * Generic definitions and results about relations *)

(** converse function (an involution) *)
Program Definition converse {A}: mon (A -> A -> Prop) :=
  {| body R x y := R y x |}.
Next Obligation. cbv. firstorder. Qed. 

#[export] Instance Involution_converse {A}: Involution (@converse A).
Proof. now intros ? ?. Qed.

Lemma converse_sup {A I} (f: I -> A -> A -> Prop) P: converse (sup' P f) == sup' P (fun i => converse (f i)). 
Proof. apply invol_sup. Qed.

Lemma converse_cup S (R R': relation S):
  converse (cup R R') == cup (converse R) (converse R').
Proof. apply invol_cup. Qed.

Lemma converse_cap S (R R': relation S):
  converse (cap R R') == cap (converse R) (converse R').
Proof. apply invol_cap. Qed.

Notation "` R" := (elem R) (at level 2).

Section s.
  Context {A: Type}.
          
  (** helpers for proving reflexivity/symmetry/transitivity of chain elements *)
  Lemma inf_closed_reflexive: inf_closed (@Reflexive A).
  Proof. cbv. firstorder. Qed.
  Lemma inf_closed_symmetric: inf_closed (@Symmetric A).
  Proof. cbv. firstorder. Qed.
  Lemma inf_closed_transitive: inf_closed (@Transitive A).
  Proof. cbv; firstorder eauto. Qed.

  Context {b: mon (relation A)}.

  (** for chain elements [R], [gfp b] and [b R] are always subrelations of [R] *)
  #[export] Instance sub_bChain (R: Chain b): subrelation (b `R) `R.
  Proof. apply (b_chain (b:=b)). Qed.
  #[export] Instance sub_gfp_Chain (R: Chain b): subrelation (gfp b) `R.
  Proof. apply (gfp_chain (b:=b)). Qed.
  
  Proposition Reflexive_chain: (forall R: Chain b, Reflexive `R -> Reflexive (b `R)) -> forall R: Chain b, Reflexive `R.
  Proof. apply tower', inf_closed_reflexive. Qed.  
  Proposition Symmetric_chain: (forall R: Chain b, Symmetric `R -> Symmetric (b `R)) -> forall R: Chain b, Symmetric `R.
  Proof. apply tower', inf_closed_symmetric. Qed.  
  Proposition Transitive_chain: (forall R: Chain b, Transitive `R -> Transitive (b `R)) -> forall R: Chain b, Transitive `R.
  Proof. apply tower', inf_closed_transitive. Qed.  

  (** helpers for proving that n-ary functions preserve chain elements *)
  Fixpoint nfun n :=
    match n with
    | 0 => A
    | S n => A -> nfun n
    end.
  Fixpoint respectful_iter n R S: relation (nfun n) :=
    match n with
    | 0 => S
    | S n => respectful R (respectful_iter n R S)
    end.
  Lemma inf_closed_respectful n f g: inf_closed (fun R => respectful_iter n R R f g).
  Proof.
    induction n; intros P HP.
    - apply HP.
    - intros x y xy. apply IHn. 
      intros R HR. apply HP. apply HR. apply xy, HR.
  Qed.
  Corollary inf_closed_proper n f: inf_closed (fun R => Proper (respectful_iter n R R) f).
  Proof. apply inf_closed_respectful. Qed.

  Proposition Proper_chain n f:
    (forall R: Chain b, Proper (respectful_iter n `R `R) f -> Proper (respectful_iter n (b `R) (b `R)) f) ->
    forall R: Chain b, Proper (respectful_iter n `R `R) f.
  Proof. exact (tower' (inf_closed_proper n f)). Qed.

  (** symmetry arguments *)

  Section sym.
    
   Context {s} {I: Symmetrical converse b s}.

   Section s.
    Variable R: Chain b.
  
    Lemma Sym_converse: converse `R == `R.
    Proof. apply invol_chain. Qed.
  
    Lemma Sym_biff x y: b `R x y <-> s `R x y /\ s `R y x.
    Proof. exact (symmetrical_chain (x:=R) x y). Qed.
  
    Lemma Sym_Reflexive_chain: Reflexive (s `R) -> Reflexive (b `R).
    Proof. intros H x. now apply Sym_biff; split. Qed.
  
    Lemma Sym_Transitive_chain: Transitive (s `R) -> Transitive (b `R).
    Proof. intros H x y z. rewrite 3Sym_biff. intuition; etransitivity; eauto. Qed.
  
    Lemma Sym_respectful_chain n f g:
      respectful_iter n (b `R) (s `R) f g ->
      respectful_iter n (b `R) (s `R) g f ->
      respectful_iter n (b `R) (b `R) f g.
    Proof.
      induction n; cbn; intros H H'.
      - now apply Sym_biff. 
      - intros x y xy. apply IHn. apply H, xy.
        apply H'. revert xy. rewrite 2Sym_biff. tauto.
    Qed.
    
    Corollary Sym_Proper_chain n f: Proper (respectful_iter n (b `R) (s `R)) f -> Proper (respectful_iter n (b `R) (b `R)) f.
    Proof. intro. now apply Sym_respectful_chain. Qed.

   End s.
   
   Proposition Reflexive_symchain:
     (forall R: Chain b, Reflexive `R -> Reflexive (s `R)) ->
     forall R: Chain b, Reflexive `R.
   Proof. intro. apply Reflexive_chain. intros. apply Sym_Reflexive_chain; auto. Qed.  
    
   Proposition Symmetric_symchain:
     (** this one is granted *)
     forall R: Chain b, Symmetric `R.
   Proof. intros. change (`R <= converse `R). now rewrite Sym_converse. Qed.

   Proposition Transitive_symchain:
     (forall R: Chain b, Transitive `R -> Transitive (s `R)) ->
     forall R: Chain b, Transitive `R.
   Proof. intro. apply Transitive_chain. intros. apply Sym_Transitive_chain; auto. Qed.

   Proposition Proper_symchain n f:
     (forall R: Chain b, Proper (respectful_iter n `R `R) f -> Proper (respectful_iter n (b `R) (s `R)) f) ->
     forall R: Chain b, Proper (respectful_iter n `R `R) f.
   Proof. intro. apply Proper_chain. intros. apply Sym_Proper_chain; auto. Qed.
  End sym. 
End s.
