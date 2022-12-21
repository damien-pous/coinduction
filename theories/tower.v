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
   

 Context {b: mon X}.

 (** * Final chain as an inductive predicate *)

 (** the set of all (transfinite) iterations of b 
     although this set is (classically) a chain, we never need to know it *)
 Inductive C: X -> Prop :=
 | Cb: forall x, C x -> C (b x)
 | Cinf: forall T, T <= C -> C (inf T).

 (** declaring the chain as a typeclass so that membership can be inferred automatically *)
 Class Chain x := chain: C x.
 #[export] Instance chain_b {x} {Cx: Chain x}: Chain (b x) := Cb Cx.

 (** ** the greatest fixpoint is the least element of the final chain *)
 Definition gfp := inf C.

 #[export] Instance chain_gfp: Chain gfp.
 Proof. now apply Cinf. Qed.

 Lemma gfp_pfp: gfp <= b gfp.
 Proof. apply leq_infx, chain_b. Qed.
 
 (** tower induction principle (just a rephrasing of induction on the Chain predicate *)
 Proposition tower (P: X -> Prop):
   inf_closed P ->
   (forall x, Chain x -> P x -> P (b x)) ->
   (forall x, Chain x -> P x).
 Proof. intros Pinf Pb. induction 1; auto. Qed.

 (** elements of the chain are closed under [b] *)
 Lemma b_chain: forall {s} {Cs: Chain s}, b s <= s.
 Proof.
   apply tower. 
   - apply inf_closed_leq.
   - intros; now apply b.
 Qed.

 (** [gfp] is indeed a fixpoint  *)
 Theorem gfp_fp: b gfp == gfp.
 Proof. apply antisym. apply b_chain. apply gfp_pfp. Qed.

 (** and indeed the largest (post)-fixpoint *)
 Theorem gfp_gfp x: x <= b x -> x <= gfp.
 Proof.
   intro H. apply inf_spec. apply tower.
   - apply (inf_closed_leq (const x)).
   - intros y Cy xy. now rewrite H, xy. 
 Qed.
 
 (** relativised tower induction *)
 Proposition ptower (Q P: X -> Prop):
   Proper (leq ==> leq) Q ->
   inf_closed P ->
   (forall x, Chain x -> Q x -> P x -> P (b x)) ->
   (forall x, Chain x -> Q x -> P x).
 Proof.
   intros Qleq Pinf Pb. refine (tower _ _).
   - now apply inf_closed_impl.
   - intros x Cx I H. cut (Q x); auto. now rewrite <-b_chain. 
 Qed.

 Definition compat f := f ° b <= b ° f.
 Lemma compat_chain {s} {Cs: Chain s}: forall f, compat f -> f s <= s.
 Proof.
   intros f Hf. revert s Cs. apply tower.
   - apply inf_closed_leq. 
   - intros x Cx fx. rewrite (Hf x). now apply b. 
 Qed.
 
End s.
Arguments gfp {_ _} _. 
Arguments Chain {_ _} _.
  

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
 Lemma invol_chain {x} {Cx: Chain b x}: i x == x.
 Proof. apply invol_fixed, compat_chain, invol_compat. Qed.

 (** whence a simpler definition of [b] on the chain *)
 Lemma symmetrical_chain {x} {Cx: Chain b x}: b x == cap (s x) (i (s x)).
 Proof.
   rewrite symmetrical. apply cap_weq; trivial.
   cbn. now rewrite invol_chain.
 Qed.

End symmetry.
Arguments Symmetrical {_ _}.

(** obvious instance of [Sym_from] (default) *)
#[export] Instance symmetrical_from_def {X} {L: CompleteLattice X} {i s: mon X}: Symmetrical i (cap s (i ° s ° i)) s.
Proof. now cbn. Qed.
