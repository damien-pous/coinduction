(** * Abstract theory of coinduction via the final chain and tower induction *)

Require Export lattice.
Set Implicit Arguments.

Section s.

 Context {X} {L: CompleteLattice X}.
  
 (** inf-closed predicates *)
 Definition inf_closed (P: X -> Prop) := forall T, T <= P -> P (inf T).

 Lemma inf_closed_cap P Q: inf_closed P -> inf_closed Q -> inf_closed (cap P Q).
 Proof.
   intros HP HQ T. rewrite cap_spec; intros [TP TQ].
   split. now apply HP. now apply HQ.
 Qed.
 Lemma inf_closed_impl (P Q: X -> Prop): Proper (leq ==> leq) P -> inf_closed Q -> inf_closed (fun x => P x -> Q x).
 Proof.
   intros HP HQ T HT H. apply HQ. 
   intros x Hx. apply HT. trivial.
   revert H. apply HP. now apply leq_infx.
 Qed.
 Lemma inf_closed_leq (f: mon X): inf_closed (fun x => f x <= x).
 Proof.
   intros T HT. apply inf_spec. intros x Tx.
   transitivity (f x). now apply f, leq_infx.
   now apply HT. 
 Qed.
   

 Variable b: mon X.

 (** * Final chain as an inductive predicate *)

 (** the set of all (transfinite) iterations of b 
     although this set is (classically) a chain, we never need to know it *)
 Inductive C: X -> Prop :=
 | Cb: forall x, C x -> C (b x)
 | Cinf: forall T, T <= C -> C (inf T).

 (** a type for the elements of the chain *)
 Structure Chain := chain { elem:> X; #[canonical=no] Celem: C elem}.

 (** the chain is closed under [b] *)
 Canonical Structure chain_b (x: Chain) := {| elem := b x; Celem := Cb (Celem x) |}.

 (** ** the greatest fixpoint is the least element of the final chain *)
 Definition gfp := inf C.

 (** the gfp belongs to the chain *)
 Canonical Structure chain_gfp := {| elem := gfp; Celem := Cinf (reflexivity C) |}. 
 Corollary gfp_prop (P: X -> Prop): (forall x: Chain, P x) -> P gfp.
 Proof. now intro. Qed.

 Lemma gfp_pfp: gfp <= b gfp.
 Proof. apply leq_infx, chain_b. Qed.
 
 (** tower induction principle (just a rephrasing of induction on the Chain predicate *)
 Proposition tower (P: X -> Prop):
   inf_closed P ->
   (forall x: Chain, P x -> P (b x)) ->
   (forall x: Chain, P x).
 Proof.
   intros Hinf Hb [x Cx]; cbn.
   induction Cx; auto.
   now apply (Hb (chain Cx)).
 Qed.

 (** elements of the chain are closed under [b] *)
 Lemma b_chain: forall x: Chain, b x <= x.
 Proof.
   apply (tower (inf_closed_leq _)).
   intros; now apply b.
 Qed.
 
 (** [gfp] is below all elements of the chain (by definition) *)
 Lemma gfp_chain (x: Chain): gfp <= x.
 Proof. apply leq_infx, x. Qed.
 
 (** [gfp] is indeed a fixpoint  *)
 Theorem gfp_fp: b gfp == gfp.
 Proof. apply antisym. apply b_chain. apply gfp_pfp. Qed.

 (** and indeed the largest (post)-fixpoint *)
 Theorem leq_gfp x: x <= b x -> x <= gfp.
 Proof.
   intro H. apply gfp_prop.
   apply (tower (inf_closed_leq (const x))); cbn.
   intros y xy. now rewrite H, xy. 
 Qed.
 
 (** relativised tower induction *)
 Proposition ptower (Q P: X -> Prop):
   Proper (leq ==> leq) Q ->
   inf_closed P ->
   (forall x: Chain, Q x -> P x -> P (b x)) ->
   (forall x: Chain, Q x -> P x).
 Proof.
   intros Qleq Pinf Pb. apply (tower (P:=fun x => Q x -> P x)). 
   - now apply inf_closed_impl.
   - intros x I H. cut (Q x); auto. now rewrite <-b_chain. 
 Qed.

 Definition compat f := f ° b <= b ° f.
 Lemma compat_chain (x: Chain): forall f, compat f -> f x <= x.
 Proof.
   intros f Hf. revert x. apply (tower (inf_closed_leq _)). 
   intros x fx. rewrite (Hf x). now apply b. 
 Qed.
 
End s.
Global Opaque gfp. 
  

(** * Symmetry arguments *)

Section symmetry.
  
 (** when the function [b] is derived from a function [s] and an involution, we get symmetry arguments *)
 Context {X} {L: CompleteLattice X} {i b s: mon X} {I: Involution i}.
  
 Class Symmetrical := symmetrical: b == cap s (i ° s ° i).
 Context {H: Symmetrical}.

 (** [i] is compatible  *)
 Lemma invol_compat: i ° b <= b ° i.
 Proof.
   rewrite symmetrical. 
   rewrite o_mcap, 2compA, invol.
   rewrite mcap_o, <-2compA, invol.
   now rewrite capC. 
 Qed.

 (** thus fixes all elements in the chain *)
 Lemma invol_chain (x: Chain b): i (elem x) == elem x.
 Proof. apply invol_fixed, compat_chain, invol_compat. Qed.

 (** whence a simpler definition of [b] on the chain *)
 Lemma symmetrical_chain {x: Chain b}: b (elem x) == cap (s (elem x)) (i (s (elem x))).
 Proof.
   rewrite (symmetrical (elem x)). apply cap_weq; trivial.
   cbn. now rewrite invol_chain.
 Qed.

 (** reasoning by symmetry on plain post-fixpoints *)
 Proposition symmetric_pfp x: i x <= x -> x <= s x -> x <= b x.
 Proof.
   intros ix sx. rewrite symmetrical. apply cap_spec. split. assumption.
   cbn. apply switch. rewrite ix at 1. apply switch in ix. now rewrite <-ix. 
 Qed. 

End symmetry.
Arguments Symmetrical {_ _}.

(** obvious instance of [Sym_from] (default) *)
#[export] Instance symmetrical_from_def {X} {L: CompleteLattice X} {i s: mon X}: Symmetrical i (cap s (i ° s ° i)) s.
Proof. now cbn. Qed.
