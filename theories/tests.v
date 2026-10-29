
(** * tests for the exported tactics *)

Require Import all.
Import CoindNotations.
    
Section s.

  (** on binary relations on natural numbers *)
  Variables b c s: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).
  Notation "x ≡[ R ] y" := (` R x y) (at level 80).
  Notation "x ≡ y" := (` _ x y) (at level 80).
  Notation "x [≡] y" := (b ` _ x y) (at level 80).
  Goal 5 ~ 6.
  Proof.
    coinduction R H.
    Restart.
  Proof.
    coinduction R _.
  Abort.
  Goal (5 ~ 6) /\ (7 ~ 8).
  Proof.
    coinduction R H.
    Restart.
  Proof.
    coinduction R [H H'].
  Abort.
  Goal forall n, n+n ~ n+n.
  Proof.
    coinduction R H.
  Abort.
  Goal forall n m (k: n=m), n+n ~ m+m.
  Proof.
    coinduction R H.
  Abort.
  Goal forall n m (k: n=m), (n+n ~ m+m) /\ forall k, n+k ~ k+m.
  Proof.
    coinduction R H.
  Abort.
  Goal gfp b 5 6 /\ gfp c 7 8.
  Proof.
    Fail coinduction R H.       (* duly failing: several gfps *)
  Abort.

  
  Goal 5 ~ 6.
  Proof.
    coinduction R H.
    cut (4 ≡[R] 5). admit.
    accumulate H'.
    cut (3 ≡[R] 2). admit.
    accumulate H''. 
    cut ((forall x, x ≡[R] 1) /\ 0 ≡[R] 18). admit.
    accumulate [H''' H'''']. 
  Abort.

  
  Abbreviation b' := (cap s (converse ° s ° converse)).
  Goal forall n m, gfp b' n m.
  Proof.
    coinduction R H.
    symmetric.
  Abort.  
  Goal forall n m, gfp b' (n+m) (m+n).
  Proof.
    coinduction R H.
    symmetric. 
  Abort.  
  Goal forall n m, gfp b' (n+m) (m+m).
  Proof.
    Fail symmetric.
    coinduction R H.
    Fail symmetric.             (* TOFIX: message (problem is that "tac1;[tac2|]" 
                                   fails to report the error messages from tac2) *)
    symmetric using idtac.
    Fail default_sym_tac.
  Abort.  
  Goal forall n m, (forall a, gfp b' (n+a) (a+m)) /\ (forall b, gfp b' (b+m) (n+b)).
  Proof.
    coinduction R H.
    symmetric. 
  Abort.
  
End s.

(** support for heterogeneous relations of arbitrary arity *)
Section h.
  Variable b: mon (nat -> bool -> nat+bool -> unit -> Prop).

  Goal gfp b 4 true (inl 5) tt.
  Proof.
    coinduction R H.
    cut (forall c, `R 3 c (inr c) tt). admit.
    accumulate H'.
    cut (forall n, `R n false (inl n) tt). admit.
    accumulate H''.
  Abort.
End h.

(** even dependent arities *)
Section h.
  Variable T: nat -> Type.
  Variable f: forall n, T n.
  Variable b: mon (forall n, T n -> T (n+n) -> Prop).

  Goal gfp b _ (f 2) (f 4).
  Proof.
    coinduction R H.
    cut (forall n x, `R _ (f n) x). admit.
    accumulate H'. 
  Abort.
End h.

(** step/unstep  *)
Section u.

Variable X : Type.
Variable b : mon (X -> Prop).

Goal forall x, gfp b x -> gfp b x.
Proof.
  intros.
  step.
  unstep.
  step in H.
  unstep in H.
  easy.
Qed.

Goal forall (R : Chain b) x, elem R x -> elem R x.
Proof.
  intros.
  step.
  (* Note: we cannot unstep, we cannot step in the hypothesis *)
  Fail unstep.                  (* duly failing *)
Abort.

End u.


(** gfp in hypotheses  *)
Section u.

Variable X : Type.
Variable b c: mon (X -> Prop).

Goal forall x, gfp b x -> gfp b x.
Proof.
  intro.
  coinduction P H.              (* note how the gfp is kept in the hypothesis *)
Abort.

Goal forall x, gfp b x -> gfp c x.
Proof.
  intro.
  coinduction P H.  
Abort.

End u.

(** named gfps  *)
Section m.

Variable X : Type.
Variable b c: mon (X -> Prop).
Definition gfpb := gfp b.
  
Goal forall x, gfpb x.
Proof.
  intro.
  Fail coinduction P H.         (* duly failing: gfpb not recognised *)
  coinduction P H for gfpb.
Abort.

Goal forall x, gfp b x /\ gfpb x.
Proof.
  intro.
  Fail coinduction P H.         (* duly failing: gfpb not recognised *)
  coinduction P H for gfpb.
Abort.

Goal forall x, gfpb x /\ gfp c x.
Proof.
  intro.
  Fail coinduction P H.          (* duly failing: gfpb not recognised *)
  Fail coinduction P H for gfpb.     (* duly failing: two gfps) *)
Abort.

Goal forall x, gfpb x /\ True.
Proof.
  intro.
  Fail coinduction P H for gfpb.     (* duly failing: True is not a gfp *)
Abort.

End m.

(** parametric named gfps *)
Section s.  
  Variable W : Type -> Type.
  Variable b : forall {X}, mon (W X -> W X -> Prop).  
  Definition bisim {X} := gfp (@b X).

  Goal forall X t u, @bisim X t u.
  Proof.
    intro. coinduction r cih for (@bisim X).
  Abort.

  Goal forall X t u, @bisim X t u.
  Proof.
    intro.
    Fail coinduction r cih for bisim. (* not yet... *)
  Abort.
End s.

  
