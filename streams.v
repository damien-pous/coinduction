(** * Example: Rutten's stream calculus *)

Require Import Psatz.
Require Import coinduction rel tactics.
Set Implicit Arguments.

Module streams.
  
 (** we consider streams of natural numbers, for the sake of simplicity *)
 CoInductive S := cons(n: nat)(q: S).

 Definition hd (s: S) := let 'cons n _ := s in n. 
 Definition tl (s: S) := let 'cons _ q := s in q. 

 (** the following function characterises (extensional) equality of streams *)
 Program Definition b: mon (S -> S -> Prop) :=
   {| body R s t := hd s = hd t /\ R (tl s) (tl t) |}.
 Next Obligation. firstorder. Qed.

 (** associated relation *)
 Infix "~" := (gfp b) (at level 70).
 
 (** associated companions  *)
 Notation T := (t (B b)).
 Notation t := (t b).

 (** notations  for easing readability in proofs by enhanced coinduction *)
 Notation "x ≡[ R ] y" := (t R x y) (at level 80).
 Notation "x ≡ y" := (t _ x y) (at level 80). 
 Notation "x [≡] y" := (b (body t _) x y) (at level 80).
 
 (* setoid_rewriting is extremely slow in trying to use the fact that [~] is a subrelation of [t R] or [T f R]
    in order to improve compilation time, we specialize the corresponding instances
    TODO: this is still not really efficient, fix this in a more satisfactory way (see more below). *)
 Local Remove Hints rel_gfp_t rel_gfp_T: typeclass_instances.
 Instance rel_gfp_t_: forall R, subrelation (gfp b) (t R) := (@rel_gfp_t _ b).
 Instance rel_gfp_T_: forall f R, subrelation (gfp b) (T f R) := (@rel_gfp_T _ b).
   
 (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
 Lemma eq_t: const eq <= t.
 Proof.
   apply leq_t. intro. change (eq <= b eq). 
   intros p ? <-. split; eauto.
 Qed.

 (** converse is compatible *)
 Lemma converse_t: converse <= t.
 Proof.
   apply leq_t. intros S x y [xy xy']. split.
   congruence. assumption.
 Qed.

 (** so is squaring *)
 Lemma square_t: square <= t.
 Proof.
   apply leq_t. intros S x z [y [xy xy'] [yz yz']]. split.
   congruence. eexists; eauto.
 Qed.

 (** thus [t R] is always an equivalence relation *)
 Global Instance Equivalence_t R: Equivalence (t R).
 Proof.
   apply Equivalence_t.
   apply eq_t. apply converse_t. apply square_t.
 Qed.
 (** and [gfp b = ~] in particular *)
 Corollary Equivalence_bisim: Equivalence (gfp b).
 Proof Equivalence_t bot.
 
 Global Instance hd_bisim: Proper (gfp b ==> eq) hd.
 Proof. intros x y H. apply (gfp_pfp b), H. Qed.

 Global Instance tl_bisim: Proper (gfp b ==> gfp b) tl.
 Proof. intros x y H. apply (gfp_pfp b), H. Qed.

 (** * "constant" streams *)
 CoFixpoint c n := cons n (c 0).

 (** * pointwise sum and its properties *)
 CoFixpoint plus s t := cons (hd s + hd t) (plus (tl s) (tl t)).
 Infix "+" := plus.

 Lemma plusC: forall x y, x + y ~ y + x.
 Proof.
   coinduction R HR. intros x y. split; simpl.
    lia.
    apply HR.
 Qed.

 Lemma plus_0x x: c 0 + x ~ x.
 Proof.
   revert x. coinduction R HR. intro x. split; simpl.
    reflexivity.
    apply HR.
 Qed. 

 Lemma plusA: forall x y z, x + (y + z) ~ (x + y) + z.
 Proof.
   coinduction R HR. intros x y z. split; simpl.
    lia.
    apply HR.
 Qed.

 (** addition corresponds to a compatible function *)
 Lemma plus_t: binary_ctx plus <= t.
 Proof.
   apply leq_t. intro R. apply (leq_binary_ctx plus).
   intros x x' [Hx Hx'] y y' [Hy Hy'].
   split.
    simpl. congruence.
    simpl tl. now apply in_binary_ctx. 
 Qed.
 Global Instance plust_t: forall R, Proper (t R ==> t R ==> t R) plus := binary_proper plus_t.
 

 (** * shuffle product *)
 (** shuffle product cannot be defined as easily as one could expect in Coq, 
     because of the guard condition. Here we simply assume its existence for the sake of simplicity *)
 Parameter shuf: S -> S -> S.
 Infix "@" := shuf (at level 40, left associativity).
 Axiom hd_shuf: forall s t, hd (s @ t) = (hd s * hd t)%nat.
 Axiom tl_shuf: forall s t, tl (s @ t) = tl s @ t + s @ tl t.
 Ltac ssimpl := repeat (rewrite ?hd_shuf, ?tl_shuf; simpl hd; simpl tl).

 (* TOFIX:
    slowness of setoid_rewrite with subrelations...
    cf. second rewrite in lemma [shuf_0x] below

    it seems this is because [partial_application_tactic] is very long to fail.
    doing
    Local Hint Extern 3 (Proper _ _) => proper_subrelation : typeclass_instances.
    solves it (by trying [proper_subrelation] first)
    but this makes other rewrites much slower afterwards...

    trying to remove most instances from the library doesn't seem to be helpful
  *)
 (*
   Local Remove Hints
          CompleteLattice_Prop CompleteLattice_fun
          gfp_leq gfp_weq
          Equivalence_weq PartialOrder_weq_leq
          sup_leq sup_weq
          cup_leq cup_weq
          inf_leq inf_weq
          cap_leq cap_weq
          Hbody
          Hbody'
          CompleteLattice_mon
          comp_leq comp_weq
          app_leq app_weq
          rel_gfp_t rel_gfp_T
      : typeclass_instances.
   Print HintDb typeclass_instances.
   Set Typeclasses Debug Verbosity 2.
  *)
 (* declaring the following instances improves some simple steps:
    for some reason, it is extremely slow when rewriting with subrelations in the present context,
    and having immediate instances as below prevents it from exploring dead-ends
  *)
 (*
 Instance proper_impl_t R:
   Proper (gfp b ==> t R ==> Basics.impl) (t R).
 Proof. intros x y H u v H' E. eapply rel_gfp_t in H. now rewrite <-H, <-H'. Qed.
 Instance proper_impl'_t R:
   Proper (gfp b ==> t R ==> Basics.flip Basics.impl) (t R).
 Proof. intros x y H u v H' E. eapply rel_gfp_t in H. now rewrite H, H'. Qed.
 Remove Hints rel_gfp_t rel_gfp_T: typeclass_instances.
  *)
 (*
   even wih those instances, other rewrites remain pretty slow, 
   e.g., the [rewrite 2plusA] in lemma [shuf_x_plus] below
  *)
 
 Lemma shuf_0x: forall x, c 0 @ x ~ c 0.
 Proof.
   coinduction R HR. intros x. split; ssimpl.
    nia.
    rewrite HR. rewrite plus_0x. apply HR. 
 Qed.
 
 Lemma shuf_1x: forall x, c 1 @ x ~ x.
 Proof.
   coinduction R HR. intros x. split; ssimpl.
    lia.
    rewrite shuf_0x, plus_0x. apply HR.
 Qed.

 Lemma shufC: forall x y, x @ y ~ y @ x.
 Proof.
   coinduction R HR. intros x y. split; ssimpl.
    nia.
    now rewrite HR, plusC, HR. 
 Qed.
 
 Lemma shuf_x_plus: forall x y z, x @ (y + z) ~ x@y + x@z.
 Proof.
   coinduction R HR. intros x y z. split; ssimpl.
    nia. 
    rewrite 2HR. rewrite 2plusA. 
    apply plust_t. 2: reflexivity.
    rewrite <-2plusA. 
    apply plust_t. reflexivity. now rewrite plusC.
 Qed.

 Lemma shuf_plus_x: forall x y z, (y + z)@x ~ y@x + z@x.
 Proof.
   intros. rewrite shufC, shuf_x_plus.
   apply plust_t; apply shufC.
 Qed.

 Lemma shufA: forall x y z, x @ (y @ z) ~ (x @ y) @ z.
 Proof.
   coinduction R HR. intros x y z. split; ssimpl.
    nia.
    rewrite shuf_x_plus, shuf_plus_x. rewrite 3HR.
    now rewrite plusA. 
 Qed.

 (** shuffle product is only compatible up-to *)
 Lemma shuf_t: binary_ctx shuf <= t. 
 Proof.
   apply Coinduction. 
   intro R. apply (leq_binary_ctx shuf). 
   intros x x' Hx y y' Hy. split; ssimpl.
   f_equal. apply Hx. apply Hy.
   apply (ftT_T _ plus_t). simpl. apply in_binary_ctx.  
    apply (fTf_Tf b). simpl. apply in_binary_ctx. apply (id_T b). apply Hx.
    apply (b_T b), Hy. 
    apply (fTf_Tf b). simpl. apply in_binary_ctx. now apply (b_T b). 
    apply (id_T b), Hy.
 Qed.
 Global Instance shuft_t: forall R, Proper (t R ==> t R ==> t R) shuf := binary_proper shuf_t.
 
 
 
 (** * convolution product *)
 (* like shuffle product, convolution product cannot be defined as easily as one could expect in Coq.
    Here we simply assume its existence for the sake of simplicity *)
 Parameter mult: S -> S -> S.
 Infix "*" := mult.
 Axiom hd_mult: forall s t, hd (s * t) = (hd s * hd t)%nat.
 Axiom tl_mult: forall s t, tl (s * t) = tl s * t + c (hd s) * tl t.
 Ltac msimpl := repeat (rewrite ?hd_mult, ?tl_mult; simpl hd; simpl tl).

 Lemma mult_0x: forall x, c 0 * x ~ c 0.
 Proof.
   coinduction R HR. intros x. split; msimpl.
    nia.
    rewrite HR. rewrite plus_0x. apply HR. 
 Qed.
 
 Lemma mult_x0: forall x, x  * c 0 ~ c 0.
 Proof.
   coinduction R HR. intros x. split; msimpl.
    nia.
    rewrite HR. rewrite plus_0x. apply HR. 
 Qed.
 
 Lemma mult_1x: forall x, c 1 * x ~ x.
 Proof.
   coinduction R HR. intros x. split; msimpl.
    lia.
    rewrite mult_0x, plus_0x. apply HR.
 Qed.

 Lemma mult_x1: forall x, x * c 1 ~ x.
 Proof.
   coinduction R HR. intros x. split; msimpl.
    lia.
    rewrite mult_x0, plusC, plus_0x. apply HR.
 Qed.

 Lemma mult_x_plus: forall x y z, x * (y + z) ~ x*y + x*z.
 Proof.
   coinduction R HR. intros x y z. split; msimpl.
    nia. 
    rewrite 2HR. rewrite 2plusA. 
    apply plust_t. 2: reflexivity.
    rewrite <-2plusA. 
    apply plust_t. reflexivity. now rewrite plusC.
 Qed.

 Lemma c_plus n m: c (n+m) ~ c n + c m.
 Proof.
   coinduction R HR. clear HR. split; simpl.
    reflexivity.
    now rewrite plus_0x.
 Qed.

 Lemma c_mult n m: c (n*m) ~ c n * c m.
 Proof.
   coinduction R HR. clear HR. split; msimpl.
    reflexivity.
    now rewrite mult_0x, mult_x0, plus_0x.
 Qed.

 (** as for the shuffle product, convolution product is only compatible up to  *)
 Lemma mult_t: binary_ctx mult <= t. 
 Proof.
   apply Coinduction. 
   intro R. apply (leq_binary_ctx mult).
   intros x x' Hx y y' Hy. split; msimpl.
   f_equal. apply Hx. apply Hy.
   apply (ftT_T _ plus_t). simpl. apply in_binary_ctx.  
    apply (fTf_Tf b). simpl. apply in_binary_ctx. apply (id_T b). apply Hx.
    apply (b_T b), Hy. 
    apply (fTf_Tf b). simpl. apply in_binary_ctx.
    apply (t_T b). apply proj1 in Hx. now rewrite Hx.
    apply (id_T b), Hy.
 Qed.
 Global Instance multt_t: forall R, Proper (t R ==> t R ==> t R) mult := binary_proper mult_t.
 
 Lemma mult_plus_x: forall x y z, (y + z) * x ~ y*x + z*x.
 Proof.
   coinduction R HR. intros x y z. split; msimpl.
    nia. 
    rewrite c_plus, 2HR, 2plusA.
    apply plust_t. 2: reflexivity.
    rewrite <-2plusA. 
    apply plust_t. reflexivity. now rewrite plusC.
 Qed.
 
 Lemma multA: forall x y z, x * (y * z) ~ (x * y) * z.
 Proof.
   coinduction R HR. intros x y z. split; msimpl.
    nia.
    rewrite mult_x_plus. rewrite 3HR.
    rewrite plusA, <-mult_plus_x.
    now rewrite c_mult.
 Qed.

 (** below: commutativity of convolution product, following Rutten's
     proof *)
      
 Lemma multC_n n: forall x, c n * x ~ x * c n.
 Proof.
   coinduction R HR. intro x. split; msimpl.
    nia.
    now rewrite mult_0x, mult_x0, plusC, HR.
 Qed.

 Definition X := cons 0 (c 1).

 Theorem expand x: x ~ c (hd x) + X * tl x.
 Proof.
   coinduction R HR. clear HR. split; msimpl.
    nia.
    now rewrite mult_0x, mult_1x, plus_0x, plusC, plus_0x.
 Qed.

 Lemma multC_11 x: tl (X * x) ~ x.
 Proof.
   coinduction R HR. clear HR. split; msimpl.
    nia.
    now rewrite !mult_0x, mult_1x, 2plus_0x, plusC, plus_0x.
 Qed.
 
 Lemma multC_X: forall x, X * x ~ x * X. 
 Proof.
   coinduction R HR. intro x. split; msimpl.      
    nia. 
    rewrite mult_0x, mult_1x, mult_x1.
    rewrite plusC, plus_0x.
    rewrite plusC. now rewrite <-HR, <-expand.
 Qed.
 
 Lemma multC: forall x y, x * y ~ y * x.
 Proof.
   coinduction R HR. intros x y. split.
    msimpl; nia.
    rewrite (expand x) at 1. rewrite mult_plus_x. simpl tl.
    rewrite <-multA, multC_11.
    rewrite (HR (tl x)).
    rewrite multC_n. rewrite <-(multC_11 (y*tl x)).
    rewrite multA, multC_X.
    rewrite (expand x) at 3. rewrite mult_x_plus.
    now rewrite multA. 
 Qed.

End streams.
