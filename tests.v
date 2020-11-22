(*******************************************************************)
(*     This is part of CAWU, it is distributed under the terms     *)
(*       of the GNU Lesser General Public License version 3        *)
(*                (see file LICENSE for more details)              *)
(*                                                                 *)
(*  Copyright 2020: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * tests for the reification tools  *)

Require Import coinduction rel.

Section s.
  Variables b c s: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80). 
  Notation "x ~ [ R ] y" := (t b R x y) (at level 80). 
  Notation "x .~ [ R ] y" := (b (body (t b) R) x y) (at level 80).
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
  Goal forall n m (k: n=m), n+n ~ m+m /\ forall k, n+k ~ k+m.
    coinduction R H.
  Abort.
  Goal gfp b 5 6 /\ gfp c 7 8.
    Fail cawu_reify.
  Abort.
  Goal forall n m, gfp (cap s (converse o s o converse)) n m.
  Proof.
    coinduction' R H. 
  Abort.  

  Import reification.
  Goal 5 ~ 6.
    coinduction R H.
    cut (4 ~[R] 5). admit.
    change (pT hol (t b R) 4 5).
    rewrite eT.
    apply accumulate.
    rewrite <-eT.
    set (R' := cup _ _). simpl pT.
    assert (RR': R <= R') by now unfold R'; rewrite <-cup_l.
    apply (Hbody (t b)) in RR'. apply RR' in H. clear RR'. 
    pose proof (cup_r R _: _ <= R') as H'. rewrite <-eT in H'.
    clearbody R'. simpl pT in H'. apply (id_t b) in H'.
    clear R. rename R' into R. 
  Abort.

End s.

