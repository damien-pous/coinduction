
(** * tests for the exported tactics *)

Require Import coinduction rel tactics.

Section s.

  Variables b c s: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).
  Notation "x ≡[ R ] y" := (t b R x y) (at level 80). 
  Notation "x ≡ y" := (t b _ x y) (at level 80). 
  Notation "x [≡] y" := (bt b _ x y) (at level 80).
  Goal 5 ~ 6.
    coinduction R H.
    Restart.
    coinduction R _. 
    Restart.
    coinduction ? _. 
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
    Fail symmetric.             (* TOFIX: message *)
    symmetric using idtac.
  Abort.  
  Goal forall n m, (forall a, gfp b' (n+a) (a+m)) /\ (forall b, gfp b' (b+m) (n+b)).
    coinduction R H.
    symmetric. 
  Abort.

  Goal True.
    assert (R: nat -> nat -> Prop). admit.
    cut (forall x: nat, t b R x x). admit.
    find_candidate.
  Abort.
  
End s.

Section h.
  Variable b: mon (nat -> bool -> nat+bool -> Prop).

  Goal gfp b 4 true (inl 5).
  Proof.
    coinduction R H.
    cut (forall c, t b R 3 c (inr c)). admit.
    accumulate H'.
    cut (forall n, t b R n false (inl n)). admit.
    accumulate H''.
  Abort.
End h.
