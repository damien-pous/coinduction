
(** * tests for the exported tactics *)

Require Import tower rel tactics.
    
Section s.

  (** on binary relations on natural numbers *)
  Variables b c s: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).
  Notation "x ≡[ R ] y" := (` R x y) (at level 80).
  Notation "x ≡ y" := (` _ x y) (at level 80).
  Notation "x [≡] y" := (b ` _ x y) (at level 80).
  Goal 5 ~ 6.
    coinduction R H.
    Restart.
    coinduction R _.
  Abort.
  Goal 5 ~ 6 /\ 7 ~ 8.
    coinduction R H.
    Restart.
    coinduction R [H H'].
  Abort.
  Goal forall n, n+n ~ n+n.
    coinduction R H.
  Abort.
  Goal forall n m (k: n=m), n+n ~ m+m.
    coinduction R H.
  Abort.
  Goal forall n m (k: n=m), n+n ~ m+m /\ forall k, n+k ~ k+m.
    coinduction R H.
  Abort.
  Goal gfp b 5 6 /\ gfp c 7 8.
    Fail coinduction R H.
  Abort.

  
  Goal 5 ~ 6.
    coinduction R H.
    cut (4 ≡[R] 5). admit.
    accumulate H'.
    cut (3 ≡[R] 2). admit.
    accumulate H''. 
    cut ((forall x, x ≡[R] 1) /\ 0 ≡[R] 18). admit.
    accumulate [H''' H'''']. 
  Abort.

  
  Notation b' := (cap s (converse ° s ° converse)).
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
