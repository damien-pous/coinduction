(** * Tactics for coinductive binary relations  *)


Require Import coinduction rel.
Set Implicit Arguments.


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

 (** depedently typed syntax for formulas of the shape
     forall x y, R t1 t2 /\ forall z, R s1 s2 *)
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

 (** the enhanced coinduction lemma expressed in this reified form *)
 Lemma coinduction_ L A x y (b: mon (A -> A -> Prop)):
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
    apply (coinduction_
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

 (** accumulation rule *)
 Inductive Ts A :=
 | tnil
 | tcons(L: T)(x y: fT L A)(Q: Ts A).
 Fixpoint pTs A (Ls: Ts A) (R: A -> A -> Prop) (P: Prop): Prop :=
   match Ls with
   | tnil _ => P
   | tcons L x y Ls => pT L R x y -> @pTs _ Ls R P
   end.
 Fixpoint merge A (Ls: Ts A): A -> A -> Prop :=
   match Ls with
   | tnil _ => bot
   | tcons L x y Ls => cup (rT L x y) (merge Ls)
   end.
 Lemma eTs A Ls R P: @pTs A Ls R P <-> (merge Ls <= R -> P).
 Proof.
   induction Ls.
   - split. trivial. intro H; apply H. apply leq_bx.
   - simpl pTs. simpl merge. rewrite cup_spec, IHLs, eT. tauto.
 Qed.
 Fixpoint tsnoc {A} Ls L x y :=
   match Ls with
   | tnil _ => tcons L x y (tnil A)
   | tcons L' x' y' Ls => tcons L' x' y' (tsnoc Ls L x y)
   end.
 Lemma merge_tsnoc A Ls L x y: merge (@tsnoc A Ls L x y) == merge (tcons L x y Ls).
 Proof.
   induction Ls.
   - reflexivity.
   - simpl tsnoc. simpl merge.
     rewrite IHLs. simpl merge. now rewrite cupA, (cupC (rT _ _ _)), <-cupA.
 Qed.
 Lemma accumulate_ A Ls L x y (b: mon (A -> A -> Prop)):
     (forall R, pTs (tsnoc Ls L x y) (t b R) (pT L (b (t b R)) x y)) ->
     (forall R, pTs Ls (t b R) (pT L (t b R) x y)).
 Proof.
   setoid_rewrite eTs.
   setoid_rewrite merge_tsnoc. 
   intros H R HR. rewrite eT. apply accumulate. 
   rewrite <-eT. apply H. simpl merge. rewrite cup_spec. split.
   rewrite <-cup_r. apply id_t.
   rewrite <-cup_l. assumption. 
 Qed.

 (** for reasoning by symmetry *)
 Lemma by_symmetry_ {L A} {b s: mon (A -> A -> Prop)} {S: Sym_from converse b s} R x y:
     (forall i j, rT L x y j i -> rT L x y i j) ->
     pT L (s (t b R)) x y ->
     pT L (b (t b R)) x y.
 Proof. rewrite 2!eT. intros C H. now apply by_symmetry. Qed.
 
End reification.

(** * Exported tactics *)

(** resulting [coinduction] tactic, to start a proof by coinduction *)
Declare ML Module "reification". 
Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  coinduction_reify; apply reification.coinduction_;
  simpl reification.pT; intros R H.

(** tactic for reasoning on symmetric candidates with symmetric functions *)
Tactic Notation "symmetric" "using" tactic(tac) :=
  symmetric_reify; apply reification.by_symmetry_;
  [simpl reification.rT; tac | simpl reification.pT].

Tactic Notation "symmetric" :=
  symmetric using (solve[clear;firstorder]||fail "could not get symmetry automatically").

(* old symmetry-solving tactic *)
(*
Ltac solve_sym := solve [
  repeat (rewrite converse_sup; apply sup_spec; intros);
  rewrite converse_pair;
  repeat (eapply eleq_xsup_all; intros);
  trivial ] || idtac "could not get symmetry automatically".
*)

(** accumulation tactic (once a proof by coinduction has been started) *)
Ltac xaccumulate R tbR :=
  lazymatch goal with
  | H: context[tbR _ _] |- _ => revert H; xaccumulate R tbR; intro H
  | _ => accumulate_reify; revert R; apply reification.accumulate_; intro R;
         simpl reification.pTs; simpl reification.pT
  end.

Tactic Notation "accumulate" simple_intropattern(H) :=
  symmetric_reify;
  match goal with
    |- reification.pT _ ?tbR _ _ =>
    match tbR with
    | body (t _) ?R => xaccumulate R tbR; intros H
    end
  end.


(** performing a single step (equivalent to [accumulate _]) *)
Ltac step :=
  match goal with
  | |- gfp ?b ?x ?y => apply (proj2 (gfp_fp b x y))
  | |- body (t ?b) ?R ?x ?y => apply (bt_t b R x y)
  end;
  simpl body.
