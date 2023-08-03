(** * Abstract theory of coinduction 

  See
  Coinduction All the Way Up. Damien Pous. In Proc. LICS, 2016.
  http://dx.doi.org/10.1145/2933575.2934564
  https://hal.archives-ouvertes.fr/hal-01259622/document

*)

Require Export lattice.
Require Classical.              (* only for distributivity of the companion *)
Set Implicit Arguments.

(** * Knaster-Tarski and compatibility  *)

Section s1.
 Context {X} {L: CompleteLattice X}.
 
 Variable b: mon X.

 (** ** compatible functions *)
 Notation compat f := (f ° b <= b ° f) (only parsing).
 
 (** compositionality properties of compatibility *)
 Lemma compat_id: compat id.
 Proof. reflexivity. Qed.
 
 Lemma compat_comp f g: compat f -> compat g -> compat (f ° g).
 Proof.
   intros Hf Hg.
   rewrite <-compA, Hg.
   rewrite compA, Hf.
   now rewrite compA. 
 Qed.

 Lemma compat_b: compat b.
 Proof. reflexivity. Qed.

 Lemma compat_const y: y <= b y -> compat (const y).
 Proof. now intros ??. Qed. 
 
 Lemma compat_sup (P: mon X -> Prop):
   (forall f, P f -> compat f) -> compat (sup P).
 Proof.
   intros H x. simpl. apply sup_spec. intros f Pf. 
   rewrite (H _ Pf x). apply b. eapply eleq_xsup; eauto.
 Qed.

 (** ** companion *)

 (** the companion is the largest compatible function *)
 Definition t := sup (fun f => compat f).

 Lemma compat_t: compat t.
 Proof. now apply compat_sup. Qed.

 (** ** Knaster Tarski *)

 (** we will show that [t bot] is the greatest fixpoint of [b] (Theorem 3.3), 
     whence the following definition *)
 Definition gfp := t bot. 

 (** [gfp] is a post-fixpoint *)
 Proposition gfp_pfp: gfp <= b gfp.
 Proof.
   transitivity (t (b bot)).
   now apply t. 
   apply compat_t.
 Qed.
 (** and actually the greatest one *)
 Proposition leq_gfp y: y <= b y -> y <= gfp.
 Proof.
   intro H.
   assert (H': const y <= t) by now apply leq_xsup, compat_const.
   apply (H' bot).
 Qed.

 (** thus a fixpoint, as in Knaster-Tarski's proof *)
 Theorem gfp_fp: gfp == b gfp.
 Proof.
   apply antisym. apply gfp_pfp.
   apply leq_gfp. apply b, gfp_pfp.
 Qed.

 (** more properties about [t] (Lemma 3.2) *)
 Lemma leq_t f: compat f -> f <= t.
 Proof. intro; now apply leq_xsup. Qed.
 
 Lemma id_t: id <= t.
 Proof. apply leq_t, compat_id. Qed.

 Lemma b_t: b <= t.
 Proof. apply leq_t, compat_b. Qed.
 
 Lemma tt_t: t ° t <= t.
 Proof. apply leq_t, compat_comp; apply compat_t. Qed.
 
 Lemma ft_t f: f <= t -> f ° t <= t.
 Proof. intro H. rewrite H. apply tt_t. Qed.

 Lemma t_idem: t ° t == t.
 Proof. apply antisym. apply tt_t. now rewrite <-id_t at 2. Qed.

 (** 'guarded companion', convenient later for expressing the [coinduction] and [accumulate] rules *)
 Definition bt := b ° t.

 Lemma bt_t: bt <= t.
 Proof. apply ft_t, b_t. Qed.

 Lemma fbt_bt {f}: f <= t -> f°bt <= bt.
 Proof. intro H. unfold bt. rewrite H. now rewrite compA, compat_t, <-compA, tt_t. Qed.
   
 (** to sum up: [gfp = t bot = t gfp <= t x] *)
 (** Corollary 3.4 *)
 Corollary t_gfp: t gfp == gfp.
 Proof. apply t_idem. Qed.

 Corollary gfp_t x: gfp <= t x.
 Proof. now apply t. Qed.

 Corollary gfp_bt x: gfp <= bt x.
 Proof. now rewrite gfp_pfp, (gfp_t x) . Qed.

 Lemma leq_f_ft f: f <= f ° t.
 Proof. now rewrite <-id_t. Qed.
 Lemma leq_f_tf f: f <= t ° f.
 Proof. now rewrite <-id_t. Qed.
 
End s1.
Notation compat b f := (f ° b <= b ° f) (only parsing).
#[export] Typeclasses Opaque t.
Global Opaque t.

Section s2.
 Context {X} {L: CompleteLattice X}.

 (** [gfp] is monotone, as a function from [mon X] to [X] 
     (be careful: [t] is not monotone from [mon X] to [mon X]) *)
 Instance gfp_leq: Proper (leq ==> leq) (gfp (X := X)).
 Proof. intros b b' Hb. apply leq_gfp. rewrite gfp_fp at 1. apply Hb. Qed.
 Instance gfp_weq: Proper (weq ==> weq) (gfp (X := X)) := op_leq_weq_1.
 
 Variable b: mon X.

 (** [t] is intended to be used as an up-to technique, to play with 
     [b' = b ° t] rather than just [b].
    The following proposition (Equation 11) shows that we would not get
    anything new by iterating this idea. *)
 Notation bt := (bt b).
 Notation t' := (t bt).
 Notation t := (t b).
 Proposition stagnate_t: t == t'.
 Proof.
   unfold bt.
   apply antisym'. apply leq_t. now rewrite compA, compat_t.
   intro E. apply leq_t.
   rewrite (leq_f_ft b b) at 3.
   rewrite compat_t.
   rewrite <-compA. rewrite E at 1.
   now rewrite tt_t.
 Qed.

 (** as a corollary, [b'] is a valid enhancement of [b] (Theorem 3.6) *)
 Corollary enhanced_gfp: gfp b == gfp bt.
 Proof. apply stagnate_t. Qed.

 (** and we get a unique enhanced coinduction principle *)
 Corollary coinduction x: x <= bt x -> x <= gfp b.
 Proof. intro. rewrite enhanced_gfp. now apply leq_gfp. Qed.  

End s2.
 
(** * Compatibility up-to: second order reasoning *)

Section s3.
 Context {X} {L: CompleteLattice X}.
 Variable b: mon X.
 
 (** a function whose post-fixpoints are the compatible functions (Definition 6.1) *)
 Program Definition B: mon (mon X) :=
   {| body g := sup (fun f => f ° b <= b ° g) |}.
 Next Obligation.
   intros g g' Hg x. apply sup_leq; trivial. 
   intros f Hf z. now rewrite <-(Hg z).
 Qed.

 (** Lemma 6.2 *)
 Lemma B_spec f g: f <= B g <-> f ° b <= b ° g.
 Proof.
   split; intro H. rewrite H. intro. apply sup_spec. 
   intros h Hh. apply Hh.
   now apply leq_xsup.
 Qed.
 Lemma Bfb f: B f ° b <= b ° f.
 Proof. now apply B_spec. Qed.

 (** the companion of [b] is the greatest fixpoint of [B] *)
 Theorem companion_gfp: t b == gfp B.
 Proof.
  apply antisym.
   apply leq_gfp. rewrite B_spec. apply compat_t.
   apply leq_t. rewrite <-B_spec. apply gfp_pfp.
 Qed.

 (** [T] is the companion of [B] *)
 Definition T := t B.
 Definition bT f := comp b (T f).
 Notation t := (t b).
 Notation bt := (bt b).

 (** corresponding second-order coinduction principle *)
 Corollary Coinduction f: f ° b <= bT f -> f <= t.
 Proof. unfold bT. rewrite <-B_spec, companion_gfp. apply coinduction. Qed.     

 
 (** ** properties of the second order companion (Proposition 6.4) *)
 
 (** the squaring function is compatible for [B] (Lemma 6.3) *)
 Program Definition csquare: mon (mon X) := {| body f := f ° f |}.
 Next Obligation. intros ? ? ?. now apply comp_leq. Qed.
 Lemma compat_csquare: compat B csquare. 
 Proof.
   intro f. apply B_spec. change (B f ° B f ° b <= b ° f ° f).
   rewrite <-compA, Bfb. 
   now rewrite compA, Bfb.    
 Qed.

 (** so is the constant-to-identity function *)
 Lemma compat_constid: const id ° B <= B ° const id.
 Proof. intro f. now apply B_spec. Qed.
 
 (** thus [T f] is always an idempotent function  *)
 Proposition TT_T f: T f ° T f <= T f.
 Proof. apply (ft_t (leq_t compat_csquare)). Qed.
 Proposition id_T f: id <= T f.
 Proof. apply (ft_t (leq_t compat_constid)). Qed.
 Corollary T_idem f: T f ° T f == T f.
 Proof. apply antisym. apply TT_T. now rewrite <-id_T at 2. Qed.

 (** [T f] always contains [f], [t], [b], and [gfp b] *)
 Lemma f_Tf f: f <= T f.
 Proof. apply id_t. Qed.
 Lemma t_T f: t <= T f.
 Proof. rewrite companion_gfp. apply gfp_t. Qed.
 Lemma bt_bT f: bt <= bT f.
 Proof. unfold bt, bT. now rewrite t_T. Qed.
 Lemma b_T f: b <= T f.
 Proof. rewrite b_t. apply t_T. Qed.
 Lemma bT_T f: bT f <= T f.
 Proof. unfold bT. rewrite (b_T f). apply TT_T. Qed.
 Lemma bt_T f: bt <= T f.
 Proof. rewrite bt_t. apply t_T. Qed.
 
 Lemma gfp_bT f x: gfp b <= bT f x.
 Proof. rewrite <-bt_bT. apply gfp_bt. Qed.
 Lemma gfp_T f x: gfp b <= T f x.
 Proof. rewrite <-t_T. apply gfp_t. Qed.

 (** helpers, to extract components out of [T]  *)
 Lemma fT_T_ f g: f <= T g -> f ° T g <= T g.
 Proof. intro H. rewrite H. apply TT_T. Qed.
 Lemma fTf_Tf f: f ° T f <= T f.
 Proof. apply fT_T_, f_Tf. Qed.
 Lemma fT_T f: f <= t -> forall g, f ° T g <= T g.
 Proof. intros H g. apply fT_T_. rewrite H. apply t_T. Qed.
 Lemma Tf_T f g: f <= T g -> T g ° f <= T g.
 Proof. intro H. rewrite H. apply TT_T. Qed.
 Lemma Cancel f g x y: f <= T g -> x <= T g y -> f x <= T g y.
 Proof. intros Hf Hx. rewrite Hx. now apply fT_T_. Qed.

 Lemma fbT_bT {f}: f <= t -> forall g, f°bT g <= bT g.
 Proof. intros H g. unfold bT. rewrite H. now rewrite compA, compat_t, <-compA, fT_T. Qed.

 (** [T f R] is always of the shape [t _] *)
 Lemma T_tT f: T f == t ° T f.
 Proof.
   apply antisym.
   - intro. apply id_t.
   - rewrite t_T. apply TT_T. 
 Qed.
 (** [bt R] is always of the shape [t _] *)
 Lemma bt_tbt: bt == t ° bt.
 Proof.
   apply antisym.
   - intro. apply id_t.
   - now apply fbt_bt.
 Qed.

 (** we can thus transfer universal properties of [t] to [bt], [T], and [bT] 
     (not used yet)
  *)
 Lemma Pt_PTf (P: X -> Prop) (H: forall R, P (t R)) (H': Proper (weq ==> leq) P): forall f R, P (T f R).
 Proof. intros f R. rewrite T_tT. apply H. Qed.
 Lemma Pt_Pbt (P: X -> Prop) (H: forall R, P (t R)) (H': Proper (weq ==> leq) P): forall R, P (bt R).
 Proof. intros R. rewrite bt_tbt. apply H. Qed.
 Lemma Pt_PbTf (P: X -> Prop) (H: forall R, P (t R)) (H': Proper (weq ==> leq) P): forall f R, P (bT f R).
 Proof. intros f R. unfold bT. rewrite T_tT. apply (Pt_Pbt H H' _). Qed.
 (* TOTHINK: 
    in fact, universal properties of [t] are universal properties of elements of [chain.S] below
  *)

 (** * Parametric coinduction: the accumulation rule  *)
 
 Program Definition xaccumulate y x: mon X :=
   {| body z := sup' (fun _:unit => x <= z) (fun _:unit => y) |}.
 Next Obligation.
   intros z z' Hz. apply sup_leq; trivial.
   intros _ H. now rewrite H.
 Qed.

 (** Theorem 10.2 *)
 Theorem accumulate y x: y <= bt (cup x y) -> y <= t x.
 Proof.
   intro H. set (f:=xaccumulate y x).
   assert (E: y <= f x) by now eapply eleq_xsup; eauto.
   cut (f <= t). intro F. now rewrite E.
   apply Coinduction. intro z. apply sup_spec. intros _ Hxz.
   rewrite H. apply b. apply Cancel. apply t_T.
   apply cup_spec. split.
   rewrite Hxz. apply b_T. 
   rewrite E, Hxz. apply Cancel. apply f_Tf. apply b_T.
 Qed.
 
End s3. 
#[export] Typeclasses Opaque B T.
Global Opaque B.

(** * Symmetry arguments *)

Section symmetry.
 (** we use a class to record the involution: this makes it possible to
     find the appropriate involution automativally in concrete examples  *)
 Context {X} {L: CompleteLattice X} {i: mon X}.
 Class Involution := invol: i ° i == id.
 Context {I: Involution}.
 
 Lemma invol' x: i (i x) == x.
 Proof. apply invol. Qed.
 
 Lemma switch x y: i x <= y <-> x <= i y.
 Proof. split; (intro H; apply i in H; now rewrite invol' in H). Qed.

 Lemma Switch f g: i ° f <= g <-> f <= i ° g.
 Proof. split; (intros H x; apply switch, H). Qed.

 Lemma compat_if_fi f: compat i f -> compat f i.
 Proof. intro H; apply Switch. now rewrite compA, <-H, <-compA, invol. Qed.
  
 (** [b] is assumed to be of the shape [s /\ i s i]  
     we use a class to record such a fact, so that the end-user may use syntactically different definitions and yet be able to declare a function as being of this shape.
  *)

 Context {b s: mon X}.
 Class Sym_from := sym_from: b == (cap s (i ° s ° i)).
 Context {H: Sym_from}.
 Notation B := (B b).
 Notation T := (T b).
 Notation t := (t b).
 Notation bt := (bt b).
 Notation bT := (bT b).

 (** [i] is compatible  *)
 Lemma compat_invol: compat b i.
 Proof.
   rewrite sym_from. 
   rewrite o_mcap, 2compA, invol.
   rewrite mcap_o, <-2compA, invol.
   now rewrite capC. 
 Qed.

 (** thus below [t]  *)
 Lemma invol_t: i <= t.
 Proof. apply leq_t, compat_invol. Qed.

 (** reasoning by symmetry on plain post-fixpoints *)
 Proposition symmetric_pfp x: i x <= x -> x <= s x -> x <= b x.
 Proof.
   intros ix sx. rewrite sym_from. apply cap_spec. split. assumption.
   apply switch. rewrite ix at 1. apply switch in ix. now rewrite <-ix. 
 Qed. 

 (** reasoning by symmetry at the first level *)
 Proposition by_symmetry x y: i x <= x -> x <= s (t y) -> x <= bt y.
 Proof.
   assert(it: i ° t == t). apply antisym'. apply ft_t, invol_t. apply Switch.
   intros Hx Hxy. rewrite (sym_from (t y)). apply cap_spec. split. assumption.
   apply switch. rewrite Hx, Hxy. now rewrite (it y).
 Qed. 

 (** reasoning by symmetry at the second level *)
 Proposition by_Symmetry f g: compat i f -> f ° b <= s ° (T g) -> f ° b <= bT g.
 Proof.
   intros Hf Hfg. apply compat_if_fi in Hf.
   unfold bT. rewrite sym_from at 2.
   rewrite mcap_o. apply cap_spec. split. assumption.
   change (f ° b <= i ° (s ° i ° T g)). apply Switch.
   rewrite compA, Hf.
   rewrite <-compA, compat_invol. 
   rewrite compA, Hfg, <-2(compA s).
   apply comp_leq. reflexivity.
   assert (iT: i <= T g). rewrite invol_t at 1. apply t_T.
   rewrite iT at 1. setoid_rewrite TT_T.
   apply Switch. apply fT_T_, iT. 
 Qed.

End symmetry.
Arguments Involution {_ _} _.
Arguments Sym_from {_ _} _ _ _.

(** obvious instance of [Sym_from] (default) *)
#[export] Instance sym_from_def {X} {L: CompleteLattice X} {i s: mon X}: Sym_from i (cap s (i ° s ° i)) s.
Proof. now cbn. Qed.


(** * Proof system *)

Section proof_system.
 Context {X} {L: CompleteLattice X}.
 
 Variable b: mon X.
 Notation B := (B b).
 Notation T := (T b).
 Notation t := (t b).
 Notation bt := (bt b).

 Lemma rule_init y: y <= t bot -> y <= gfp b.
 Proof. now intro. Qed.

 Lemma rule_done y x: y <= x -> y <= t x.
 Proof. now rewrite <-id_t. Qed.
 
 Lemma rule_upto f y x: f <= t -> y <= f (t x) -> y <= t x.
 Proof. intros Hf Hy. now rewrite <- (ft_t Hf). Qed.
 
 Lemma rule_coind y x: y <= bt (cup x y) -> y <= t x.
 Proof. apply accumulate. Qed.

End proof_system.


(** * Coincidence of the greatest respectful and the greatest compatible *)

Module respectful.
Section s.
 Context {X} {L: CompleteLattice X}.

 Variable b: mon X. 
 Notation b' := (cap b id).
 Notation t' := (t b').
 Notation B' := (B b').
 Notation T' := (T b').
 Notation B := (B b).
 Notation T := (T b).
 Notation t := (t b).
 
 Lemma b_b't: b <= b' ° t.
 Proof. 
   rewrite mcap_o. apply cap_spec. split.
    now rewrite <-id_t. 
    apply b_t.  
 Qed.

 (** Proposition 9.1  *)
 Proposition t_t': t == t'.
 Proof.
   apply antisym'. 
    apply leq_t. rewrite cap_l at 1. 
    rewrite compat_t. rewrite b_b't at 1. now rewrite <-compA, tt_t.
   intro E. apply leq_t. rewrite b_b't at 2. 
   rewrite compA, compat_t.
   rewrite E. rewrite <-compA, tt_t. 
   now rewrite cap_l at 1. 
 Qed.
 
 Proposition bt_b't: b ° t == b' ° t.
 Proof.
   apply antisym.
    rewrite b_b't at 1. now rewrite <-compA, tt_t.
    now rewrite cap_l.
 Qed.

 Lemma B'S_BS: forall S, S=T \/ S=T' -> B' ° S == B ° S.
 Proof.
   intros S HS g.
   assert (tS: t ° S g <= S g). destruct HS as [->| ->].
    now apply fT_T.
    rewrite t_t'. now apply fT_T. 
   assert (St: S g ° t <= S g). destruct HS as [->| ->].
    apply Tf_T, t_T. 
    rewrite t_t'. apply Tf_T, t_T. 
   apply from_below. intro f.
   change (f <= B' (S g) <-> f <= B (S g)). rewrite 2B_spec.
   split; intro H.
   rewrite b_b't at 1. rewrite compA, H. rewrite <-compA, St.
   now rewrite cap_l. 
   rewrite cap_l at 1. rewrite H. rewrite b_b't at 1.
   now rewrite <-tS at 2. 
 Qed.
                                          
 (** Proposition 9.2  *)
 Proposition T'_T: T' == T.
 Proof.
   apply antisym; apply leq_t.
   transitivity (T' ° B ° T'). now setoid_rewrite <-id_t at 3.
   rewrite <-compA. rewrite <-B'S_BS by tauto.
   rewrite compA. setoid_rewrite compat_t. 
   now rewrite <-compA, tt_t. 
   transitivity (T ° B' ° T). now setoid_rewrite <-id_t at 3.
   rewrite <-compA. rewrite B'S_BS by tauto.
   rewrite compA. setoid_rewrite compat_t. 
   now rewrite <-compA, tt_t. 
 Qed.

 Proposition B'T'_BT: B' ° T' == B ° T.
 Proof. rewrite T'_T. apply B'S_BS. tauto. Qed.
 
 (* note that B≠B' in general *)

End s.
End respectful.

Global Opaque T.



(** * Characterisation of Hur et al.' function G using the companion *)

Module paco.
Section s.

 Context {X} {L: CompleteLattice X}. 

 Program Definition g (b: mon X) x: mon X := {| body y := b (cup x y) |}.
 Next Obligation. intros y z H. now rewrite H. Qed.

 Program Definition G b: mon X := {| body x := gfp (g b x) |}.
 Next Obligation.
   intros ? ? ?. apply gfp_leq.
   intro. simpl. now rewrite H.
 Qed.

 Variable b: mon X.
 Notation t := (t b).
 Notation bt := (bt b).
 Notation G' := (G bt).
 
 (** Theorem 10.1 *)
 Theorem G_bt: G' == bt.
 Proof.
   apply antisym.
    assert (E: G' <= t).
     intro x. apply rule_coind. simpl. now rewrite gfp_fp at 1. 
    intro x. simpl. rewrite gfp_fp. simpl. apply b.
    rewrite (E x). rewrite <-(tt_t b x) at 2. apply t. apply cup_spec. split.
    apply id_t. reflexivity. 
   intro. simpl. apply leq_gfp. simpl. apply b, t, cup_l.
 Qed. 

 Proposition G_upto: G' == t ° G'. (* i.e., bt = tbt *)
 Proof.
   rewrite G_bt. apply antisym. intro. apply id_t.
   unfold bt. now rewrite compA, compat_t, <-compA, tt_t.
 Qed.
 
 (* note: tb < bt = tbt < t *)
End s.
End paco.


(** * alternative definition of the companion, using Kleene iteration *)
Module chain.
Section s.
 Context {X} {L: CompleteLattice X}. 
 Variable b: mon X.
 Notation t := (t b).
 Inductive S: X -> Prop :=
 | Sb: forall x, S x -> S (b x)
 | Sinf: forall T, T <= S -> S (inf T).
 Lemma gfpS: gfp b == inf S.
 Proof.
   apply antisym. apply inf_spec. simpl. intros u U. induction U.
   rewrite gfp_pfp. now apply b. now apply inf_spec.
   apply leq_gfp. apply leq_infx. now apply Sb, Sinf.
 Qed.
 Lemma tS: forall s, S s -> t s == s.
 Proof.
   intros s H. apply antisym. 2: apply id_t.
   induction H as [s Hs IH|T HT IH].
   rewrite (compat_t b s). now apply b.
   apply inf_spec. intros s Hs. rewrite <-(IH _ Hs). apply t. now apply leq_infx.
 Qed.               
 Definition S_ x s := S s /\ x <= s.
 Definition t'_ x := inf (S_ x).
 Lemma t'_mon: Proper (leq ==> leq) t'_.
 Proof.
   intros x y H. apply inf_spec; intros s [Ss E]. apply leq_infx.
   split. assumption. now rewrite H. 
 Qed.
 Definition t' := Build_mon t'_mon. 
 Lemma id_t' x: x <= t' x.
 Proof. apply inf_spec. now intros s [_ ?]. Qed.
 Lemma St' x: S (t' x).
 Proof. apply Sinf. now intros ? [? ?]. Qed.
 Lemma compat_t': t' ° b <= b ° t'.
 Proof.
   intro x. simpl. apply leq_infx. split.
   apply Sb. apply St'. apply b. apply id_t'. 
 Qed.
 
 Theorem tt': t == t'.
 Proof.
   apply antisym.
   intro x. rewrite (id_t' x) at 1. now rewrite tS by apply St'.
   apply leq_t, compat_t'.
 Qed.
 
 Corollary leq_t' f: f <= t <-> forall s, S s -> f s <= s.
 Proof.
   split.
   intros E s H. now rewrite (E s), tS.
   intros H. apply Coinduction. intro x. simpl.
   rewrite (id_t' x) at 1. rewrite H by apply Sb, St'.
   apply b. rewrite <-tt'. apply t_T.
 Qed.
 
 Lemma St x: S (t x).
 Abort.
 Lemma St x: exists tx, S tx /\ tx == t x.
 Proof. exists (t' x). split. apply St'. now rewrite tt'. Qed.

 Lemma Sflat s: S s -> exists T, T<=S /\ s == inf' T b.
 Proof.
   induction 1 as [s Hs IH|T HT IH].
   exists (eq s). split. now intros ? <-.
   apply antisym. apply inf_spec. now intros ? <-.
   eapply eleq_infx; eauto.
   (* exists (fun t => exists a (A: T a), match IH a A return Prop with ex_intro _ U _ => U t end). *)
 Abort.
 
 Lemma Sflat s: S s -> s == inf' (fun t => S t /\ s <= b t) b.
 Proof.
   intro E. apply antisym. now apply inf_spec; intros t [_ T].
   induction E as [s Hs IH|T HT IH].
   eapply eleq_infx; eauto.
   apply inf_spec. intros s Hs.
   rewrite <- (IH s Hs). apply inf_leq; trivial. 
   intros t [St sbt]. split. assumption.
   rewrite <-sbt. now apply leq_infx.
 Qed.

 (** * additivity of the companion (assuming classical logic) *)
 
 Import Classical. 
 Lemma choose (P A B: X -> Prop): (forall x, P x -> A x \/ B x) -> (exists x, P x /\ B x) \/ (forall x, P x -> A x).
 Proof.
   intro H. classical_right. intros x Px.
   destruct (H _ Px). assumption. exfalso; eauto. 
 Qed.

 Lemma S_linear x y: S x -> S y -> x <= y \/ y <= x.
 Proof.
   intro Sx. revert y. induction Sx as [x Hx IH|T HT IH]; intros y Sy.
   - pose proof (Sflat Sy) as E.
     set (T t := S t /\ y <= b t) in E. 
     assert (IH': forall y, T y -> x <= y \/ y <= x). intros t Tt. apply IH, Tt. 
     destruct (choose _ _ _ IH') as [[s [Ss sx]]|F].
     right. rewrite E, <-sx. eapply eleq_infx; eauto.
     left. rewrite E. apply inf_spec; intros s Ts. now apply b, F.
   - assert (IH': forall a, T a -> y <= a \/ a <= y). intros a A. specialize (IH _ A _ Sy). tauto. 
     destruct (choose _ _ _ IH') as [[s [Ss sx]]|F].
     left. rewrite <-sx. now apply leq_infx.
     right. apply inf_spec; intros t Tt. now apply F. 
 Qed.

 Lemma tcup x y: t (cup x y) == cup (t x) (t y).
 Proof.
   apply antisym.
   transitivity (t (cup (t' x) (t' y))).
   apply t. apply cup_leq; apply id_t'. 
   destruct (S_linear (St' x) (St' y)) as [xy|yx].
   transitivity (t (t' y)). apply t. apply cup_spec. now split.
   rewrite <-tt', (tt_t b y). apply cup_r. 
   transitivity (t (t' x)). apply t. apply cup_spec. now split.
   rewrite <-tt', (tt_t b x). apply cup_l.
   apply cup_spec. split; apply t. apply cup_l. apply cup_r. 
 Qed.

End s.
End chain.
