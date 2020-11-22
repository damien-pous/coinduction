(*******************************************************************)
(*     This is part of CAWU, it is distributed under the terms     *)
(*       of the GNU Lesser General Public License version 3        *)
(*                (see file LICENSE for more details)              *)
(*                                                                 *)
(*  Copyright 2020: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * tests for the reification tools  *)

Require Import rel.

Section s.
  Variables b c s: mon (nat -> nat -> Prop).
  Goal gfp b 5 6.
    coinduction R H.
    Restart.
    coinduction R _. 
  Abort.
  Goal gfp b 5 6 /\ gfp b 7 8.
    coinduction R H.
    Restart.
    coinduction R [H H'].
  Abort.
  Goal forall n m (k: n=m), gfp b (n+n) (m+m) /\ forall k, gfp b (n+k) (k+m).
    coinduction R H.
  Abort.
  Goal gfp b 5 6 /\ gfp c 7 8.
    Fail cawu_reify.
  Abort.
  Goal forall n m, gfp (cap s (converse o s o converse)) n m.
  Proof.
    coinduction' R H. 
  Abort.  
End s.

