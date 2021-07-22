(** * Hur et al.' toy example about divergence 

See C. Hur, G. Neis, D. Dreyer, and V. Vafeiadis. 
The power of parameterization in coinductive proof. 
In Proc. POPL, pages 193–206. ACM, 2013.

  *)

Require Import coinduction.
Set Implicit Arguments.

(** utilities to represent finite predicates using lists *)
Require Import List.
Import ListNotations.
Section l.
 Variable A: Type.
 Fixpoint In l (x: A) := match l with [] => False | y::q => x=y \/ In q x end.
 Lemma In_nil: In [] == bot.
 Proof. firstorder. Qed.
 Lemma In_cons x q: In (x::q) == cup (eq x) (In q).
 Proof. apply from_above. intro z. rewrite cup_spec. firstorder. Qed.
 Lemma In_single x: In [x] == eq x.
 Proof. firstorder. Qed.
 Lemma In_leq x (P: A -> Prop): In [x] <= P <-> P x.
 Proof. firstorder congruence. Qed.
End l.
Opaque In.

(** the transition system is hardcoded *)
Inductive S := a | b | c | d | e | f.
  
Definition edge i j :=
  match i,j with
    | a,b | b,d | d,b | b,c | e,c | c,f => True
    | _,_ => False
  end.

(** the greatest fixpoint of the following function [step] characterises 
    the set of divergent states *)
Program Definition step: mon (S -> Prop) := {| body P i := exists2 j, edge i j & P j |}.
Next Obligation. firstorder. Qed.
Notation diverges x := (gfp step x).

(** direct proof, by plain coinduction: we guess an appropriate predicate  *)
Goal diverges a.
Proof.
  rewrite <-In_leq.
  transitivity (In [a;b;d]). firstorder. apply leq_gfp.
  intros z [->|[->|[->|[]]]].
   exists b; firstorder. 
   exists d; firstorder. 
   exists b; firstorder.
Qed.

(** some notations and helpers to do proofs by parametrised coinduction *)
Notation D l x := (t step (In l) x).
Notation D' l x := (step (body (t step) (In l)) x).

Lemma init x: D [] x -> diverges x.
Proof. revert x. apply (t step). now rewrite In_nil. Qed.

Lemma save x l: D' (x::l) x -> D l x.
Proof.
  rewrite <-2(In_leq x). rewrite In_single, In_cons.
  rewrite cupC. apply accumulate. 
Qed.

Lemma play x l: D' l x -> D l x.
Proof. apply (ft_t (b_t step)). Qed.

Lemma done x l: In l x -> D l x. 
Proof. apply (id_t step). Qed.
                  
Lemma jump x y l: edge x y -> D l y -> D' l x.
Proof. intros. now exists y. Qed.

Ltac init := apply init. 
Ltac save := apply save.
Ltac play := apply play.
Ltac jump y := apply jump with y; [trivial; fail "no such edge"|].
Ltac done := apply done; firstorder; fail "no such assumption".

(** now we can get proofs interactively *)
Goal diverges a.
  init.
  play. jump b.
  save. jump d.
  play. jump b.
  done. 
Qed.

Goal diverges a.
  init.
  play. jump b.
  play. jump d.
  save. jump b.
  play. jump d.
  done. 
Qed.

Goal diverges a.
  init. 
  save. jump b.
  save. jump d.
  save. jump b.
  done. 
Qed.

(** and even build an automation tactic *)
Ltac div :=
  let rec search := done || save;
        solve [
            jump a; search |
            jump b; search |
            jump c; search |
            jump d; search |
            jump e; search |
            jump f; search 
          ]
  in init; search || fail "not diverging".
    
Goal diverges a. Proof. div. Qed.
Goal diverges c. Proof. Fail div. Abort.
