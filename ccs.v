(** * Example: Milner's CCS 
    
    references point to the following paper 
    Coinduction All the Way Up. Damien Pous. In Proc. LICS, 2016.
*)

Require Import coinduction rel tactics.
From AAC_tactics Require Import AAC.
Set Implicit Arguments.

Module Type N.
 Parameter N: Set.           (* channels names *)
End N.

Module CCS(Export M: N).

 (** CCS labels (or prefixes, they are the same) *)
 CoInductive label := tau | out(a: N) | inp(a: N).
  
 (** CCS processes. Instead of using process constants, as in the paper, 
   we use a coinductive definition. In other words, we use Coq's corecursive 
   definitions to encode CCS recursion *)
 CoInductive S :=
 | nil
 | prf(l: label)(p: S)
 | pls(p q: S)
 | par(p q: S)
 | new(a: N)(p: S)
 | rep(p: S).

 Declare Scope ccs_scope.
 Bind Scope ccs_scope with S.
 Delimit Scope ccs_scope with ccs.
 Open Scope ccs_scope.
 
 Notation "0" := nil: ccs_scope.
 Infix "\|" := par (at level 40, left associativity): ccs_scope. 
 Infix "+" := pls (at level 50, left associativity): ccs_scope.
 Notation "! p" := (rep p) (at level 20): ccs_scope.

 (** when a name [a] does not appear in a label [l] *)
 Definition fresh a (l: label) :=
   match l with tau => True | out b | inp b => a<>b end.

 (** the (standard) LTS  *)
 Inductive trans: S -> label -> S -> Prop :=
 | t_prf: forall l p, trans (prf l p) l p
 | t_pls_l: forall p q l p', trans p l p' -> trans (p+q) l p'
 | t_pls_r: forall p q l q', trans q l q' -> trans (p+q) l q'
 | t_par_l: forall p l p' q, trans p l p' -> trans (p \| q) l (p' \| q)
 | t_par_r: forall p l p' q, trans p l p' -> trans (q \| p) l (q \| p')
 | t_par_lr: forall a p p' q q', trans p (out a) p' -> trans q (inp a) q' -> trans (p \| q) tau (p' \| q')
 | t_par_rl: forall a p p' q q', trans p (inp a) p' -> trans q (out a) q' -> trans (p \| q) tau (p' \| q')
 | t_new: forall a p l p', trans p l p' -> fresh a l -> trans (new a p) l (new a p')
 | t_rep: forall p l p', trans (!p \| p) l p' -> trans (!p) l p'
 .
 Global Hint Resolve t_prf t_par_l t_par_r t_par_lr t_par_rl t_new t_pls_l t_pls_r: ccs.

 Lemma t_rep': forall p l p', trans p l p' -> trans (!p) l (!p \| p').
 Proof. intros. apply t_rep; eauto with ccs. Qed.
 Global Hint Resolve t_rep': ccs.

 Lemma t_rep'': forall p a po pi, trans p (out a) po -> trans p (inp a) pi -> trans (!p) tau (!p \| po \| pi).
 Proof. intros. apply t_rep; eauto with ccs. Qed.
 Global Hint Resolve t_rep'': ccs.
 
 (** dumb utilities for corecursion *)
 Definition id_S(p: S): S :=
   match p with
   | nil => nil
   | prf l p => prf l p
   | new a' p => new a' p
   | par p q => par p q
   | pls p q => pls p q
   | rep p => rep p 
   end.
 Lemma Sd p: p = id_S p.
 Proof. now case p. Qed.

 Ltac inverse_trans :=
   match goal with
   | H: trans ?p _ _ |- _ =>
     tryif is_var p then fail else
       inversion H; subst; clear H; try congruence; inverse_trans
   | _ => idtac
   end.

 (** the function defining simulations and similarity *)
 Program Definition s: mon (S -> S -> Prop) :=
   {| body R p q :=
        forall l p', trans p l p' -> exists2 q', trans q l q' & R p' q' |}.
 Next Obligation. cbv. firstorder. Qed.
 
 (** the symmetrised version, defining bisimulations and bisimilarity *)
 Notation b := (cap s (converse ° s ° converse)).

 Notation "p ~ q" := (gfp b p%ccs q%ccs) (at level 70).
 Notation B := (B b).
 Notation T := (t B).
 Notation t := (t b).
 Notation "x ≡[ R ] y" := (t R x y) (at level 80). 
 Notation "x ≡ y" := (t _ x y) (at level 80). 
 Notation "x [≡] y" := (b (body t _) x y) (at level 80).
 
 (** Some valid laws  *)
 Lemma parC: forall p q, p \| q ~ q \| p.
 Proof.
   (** the tactic [coinduction R H] makes it possible to start a proof by enhanced coinduction.
       the goal is transformed into a bisimulation candidate [R], and we get to analyse the transitions, information about pairs in [R] is stored in [H]. *)
   coinduction R H.
   (** the tactic [symmetric] makes it possible to play the bisimulation only from left-to-right here, since the candidate is symmetric*)
   symmetric.
   (** we finally analyse the transitions *)
   intros p q l p' pp'. inverse_trans; eauto with ccs.
 Qed.

 Lemma parA: forall p q r, p \| (q \| r) ~ (p \| q) \| r.
 Proof.
   coinduction R H.
   intros p q r; split; intros l p' pp'; simpl; inverse_trans; eauto with ccs.
 Qed.
 
 Lemma par0p: forall p, 0 \| p ~ p.
 Proof.
   coinduction R H.
   intros p; split; intros l p' pp'; simpl; inverse_trans; eauto with ccs.
 Qed.

 (** we prove more laws below, but first we need to establish the validity of up-to congruence, i.e., with the companion, that for all R, [t R] is a congruence w.r.t. CCS operators.
  *)
 
 (** * Equivalence closure *)
 
 (** [eq] is a post-fixpoint, thus [const eq] is below [t] *)
 Lemma refl_t: const eq <= t.
 Proof.
   apply leq_t. intro. change (eq <= b eq).
   apply cap_spec. split. 
    intros p q <- ? p'; eauto with ccs.
    intros p q <- ? p'; eauto with ccs.
 Qed.

 (** converse is compatible *)
 Lemma converse_t: converse <= t.
 Proof. apply invol_t. Qed.

 (** so is squaring *)
 Lemma square_t: square <= t.
 Proof.
   apply Coinduction, by_Symmetry. 
   intros R x z [y xy yz]. now exists y.
   rewrite cap_l at 1. rewrite <-id_t. 
   intros R x z [y xy yz] l x' xx'.
   destruct (xy _ _ xx') as [y' yy' x'y']. 
   destruct (yz _ _ yy') as [z' zz' y'z'].
   exists z'. assumption. eexists; eassumption.
 Qed.

 (** thus bisimilarity, [t R], and [T f R] are always equivalence relations *)
 Global Instance Equivalence_T f R: Equivalence (T f R).
 Proof. apply Equivalence_T. apply refl_t. apply converse_t. apply square_t. Qed.
 Global Instance Equivalence_t R: Equivalence (t R).
 Proof. apply Equivalence_t. apply refl_t. apply converse_t. apply square_t. Qed.
 Corollary Equivalence_bisim: Equivalence (gfp b).
 Proof. apply Equivalence_t. Qed.

 (** * Context closure *)

 (** ** prefix *)
 Lemma prf_t a: unary_ctx (prf a) <= t.
 Proof.
   assert (H: unary_ctx (prf a) <= s).
    intro R. apply leq_unary_ctx. intros p q Hpq.
    intros l p' pp'. inverse_trans. eauto with ccs. 
   apply Coinduction, by_Symmetry. apply unary_sym.
    rewrite H at 1. now rewrite <-b_T.
 Qed.
 Global Instance prft_t a: forall R, Proper (t R ==> t R) (prf a) := unary_proper (@prf_t a).

 (** ** name restriction *)
 Lemma new_t a: unary_ctx (new a) <= t.
 Proof.
   apply Coinduction, by_Symmetry. apply unary_sym.
   intro R. apply (leq_unary_ctx (new a)). intros p q Hpq l p0 Hp0.
   inverse_trans. destruct (proj1 Hpq _ _ H1) as [???]. eexists. eauto with ccs.
   apply (id_t B). now apply in_unary_ctx.
 Qed.
 Global Instance newt_t a: forall R, Proper (t R ==> t R) (new a) := unary_proper (@new_t a).

 (** ** choice *)
 Lemma pls_t: binary_ctx pls <= t.
 Proof.
   apply Coinduction, by_Symmetry. apply binary_sym.
   intro R. apply (leq_binary_ctx pls).
   intros p q Hpq r s Hrs l p0 Hp0. inverse_trans.
   destruct (proj1 Hpq _ _ H3) as [? ? ?]. eexists. eauto with ccs. now apply (id_T b).
   destruct (proj1 Hrs _ _ H3) as [? ? ?]. eexists. eauto with ccs. now apply (id_T b).
 Qed.
 Global Instance plst_t: forall R, Proper (t R ==> t R ==> t R) pls := binary_proper pls_t.
 
 (** ** parallel composition *)
 (** Lemma 8.1 *)
 Lemma par_t: binary_ctx par <= t.
 Proof.
   apply Coinduction, by_Symmetry. apply binary_sym.
   intro R. apply (leq_binary_ctx par).
   intros p q Hpq r s Hrs l p0 Hp0. inversion_clear Hp0.
    destruct (proj1 Hpq _ _ H) as [? ? ?]. eexists. eauto with ccs.
    apply (fTf_Tf b). apply (in_binary_ctx par). now apply (id_T b). now apply (b_T b). 
    destruct (proj1 Hrs _ _ H) as [? ? ?]. eexists. eauto with ccs.
    apply (fTf_Tf b). apply (in_binary_ctx par). now apply (b_T b). now apply (id_T b). 
    destruct (proj1 Hpq _ _ H) as [? ? ?].
    destruct (proj1 Hrs _ _ H0) as [? ? ?]. eexists. eauto with ccs.
    apply (fTf_Tf b). apply (in_binary_ctx par); now apply (id_T b).     
    destruct (proj1 Hpq _ _ H) as [? ? ?].
    destruct (proj1 Hrs _ _ H0) as [? ? ?]. eexists. eauto with ccs.
    apply (fTf_Tf b). apply (in_binary_ctx par); now apply (id_T b).     
 Qed.
 Global Instance part_t: forall R, Proper (t R ==> t R ==> t R) par := binary_proper par_t.
 
 (** ** replication (the challenging operation) *)

 (** preliminary results *)
 Lemma unfold_rep p: !p ~ !p \| p.
 Proof.
   step. split; intros l p' pp'; simpl.
   inversion_clear pp'. eauto with ccs.
   eexists. constructor; eassumption. reflexivity.
 Qed.

 (** Proposition 8.2(i) *)
 Proposition rep_trans p l p0: trans (rep p) l p0 -> exists2 p1, trans (p \| p) l p1 & p0 ~ !p \| p1.
 Proof.
   remember (!p)%ccs as rp. intro H. revert rp l p0 H p Heqrp. fix rep_trans 4.
   intros rp l p0 H p E. destruct H; try discriminate.
   remember (!p0 \| p0)%ccs as rpp. destruct H; try discriminate. 
    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. eexists. eauto with ccs. 
    rewrite H1. now rewrite (parC (rep _)), <-parA, <-unfold_rep.
    
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. eexists. eauto with ccs.
    now rewrite parA, <-unfold_rep.
    
    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. 
    inversion H1; subst; clear H1; (eexists; [eauto with ccs|]).
    rewrite H2. now rewrite (parC p'0), parA, <-unfold_rep, (parC q'), parA. 
    rewrite H2. now rewrite parA, <-unfold_rep, (parC q'), parA.

    destruct (rep_trans _ _ _ H p0) as [???]; clear H. congruence. 
    injection E. injection Heqrpp. intros. subst. clear E Heqrpp. 
    inversion H1; subst; clear H1; (eexists; [eauto with ccs|]).
    rewrite H2. now rewrite (parC p'0), parA, <-unfold_rep, parA. 
    rewrite H2. now rewrite parA, <-unfold_rep, parA.
 Qed.

 (** Proposition 8.2(ii) *)
 Proposition rep_trans' p l p1: trans (p \| p) l p1 -> exists2 p0, trans (!p) l p0 & p0 ~ !p \| p1.
 Proof.
   assert (E: !p \| (p\|p) ~ !p).
    now rewrite parA, <-2unfold_rep.
   intros H.
   assert (H': trans (!p \| (p\|p)) l (!p\|p1)) by auto with ccs.
   destruct (proj1 (gfp_pfp b _ _ E) _ _ H'). eexists. eauto with ccs. symmetry. assumption.
 Qed.

 (** Lemma 8.4 
     (note that we do not need Lemma 8.3 as in the paper: we
     use instead the more general fact that we can reason up to
     equivalence [Equivalence_t] and that [~ <= t R]) *)
 Lemma rep_t: unary_ctx rep <= t.
 Proof.
   apply Coinduction, by_Symmetry. apply unary_sym.
   intro R. apply (leq_unary_ctx rep). intros p q Hpq l p0 Hp0.
   apply rep_trans in Hp0 as [p1 ppp1 p0p1]. 
   assert (H: b (t R) (par p p) (par q q)).
    apply (compat_t b). apply par_t. now apply in_binary_ctx. 
   destruct (proj1 H _ _ ppp1) as [q1 qqq1 p1q1].
   apply rep_trans' in qqq1 as [q0 Hq0 q0q1].
   eexists. eassumption.
   rewrite p0p1, q0q1.
   apply (ftT_T _ par_t). apply (in_binary_ctx par). 
    apply (fTf_Tf b). apply (in_unary_ctx rep). now apply (b_T b).
    now apply (t_T b). 
 Qed.
 Global Instance rept_t: forall R, Proper (t R ==> t R) rep := unary_proper rep_t.

 (** more laws  *)
 
 Lemma parp0 p: p \| 0 ~ p.
 Proof. now rewrite parC, par0p. Qed.

 Instance par_Associative R: Associative (t R) par.
 Proof. intros ???. refine (@gfp_t _ _ _ R _ _ _). apply parA. Qed.
 Instance par_Commutative R: Commutative (t R) par.
 Proof. intros ??. refine (@gfp_t _ _ _ R _ _ _). apply parC. Qed.
 Instance par_Unit R: Unit (t R) par 0%ccs.
 Proof. split; intro; refine (@gfp_t _ _ _ R _ _ _). apply par0p. apply parp0. Qed.

 Lemma plsC: forall p q, p+q ~ q+p.
 Proof.
   (* coinduction not necessary, just used here to exploit symmetry argument *)
   coinduction R _. symmetric.
   intros p q l p' pp'. inverse_trans; eauto with ccs.
 Qed.

 Lemma plsA p q r: p+(q+r) ~ (p+q)+r.
 Proof.
   step.
   split; intros l p' pp'; simpl; inverse_trans; eauto with ccs. 
 Qed.

 Lemma pls0p p: 0 + p ~ p.
 Proof.
   step.
   split; intros l p' pp'; simpl; inverse_trans; eauto with ccs. 
 Qed.
   
 Lemma plsp0 p: p + 0 ~ p.
 Proof. now rewrite plsC, pls0p. Qed.   

 Instance pls_Associative R: Associative (t R) pls.
 Proof. intros ???. refine (@gfp_t _ _ _ R _ _ _). apply plsA. Qed.
 Instance pls_Commutative R: Commutative (t R) pls.
 Proof. intros ??. refine (@gfp_t _ _ _ R _ _ _). apply plsC. Qed.
 Instance pls_Unit R: Unit (t R) pls 0%ccs.
 Proof. split; intro; refine (@gfp_t _ _ _ R _ _ _). apply pls0p. apply plsp0. Qed.
 
 Lemma plsI p: p+p ~ p.
 Proof.
   step.
   split; intros l p' pp'; simpl; inverse_trans; eauto with ccs. 
 Qed.

 Lemma new_new: forall a b p, new a (new b p) ~ new b (new a p).
 Proof.
   coinduction R H. symmetric.
   intros a b p l p' pp'. inverse_trans; eauto with ccs.
 Qed.

 (* special case of [new_gc] below *)
 Lemma new_zer: forall a, new a 0 ~ 0.
 Proof.
   intro. step. 
   split; intros l' p' pp'; simpl; inverse_trans; eauto with ccs. 
 Qed.

 Lemma new_prf: forall a l p, fresh a l -> new a (prf l p) ~ prf l (new a p).
 Proof.
   intros. step. 
   split; intros l' p' pp'; simpl; inverse_trans; eauto with ccs. 
 Qed.

 Lemma new_prf': forall a l p, ~ fresh a l -> new a (prf l p) ~ 0.
 Proof.
   intros. step. 
   split; intros l' p' pp'; simpl; inverse_trans; eauto with ccs.
 Qed.
 
 Lemma new_sum: forall a p q, new a (p + q) ~ new a p + new a q.
 Proof.
   intros. step.
   split; intros l' p' pp'; simpl; inverse_trans; eauto with ccs. 
 Qed.

 Lemma prf_tau_new c p q: prf tau (new c (p \| q)) ~ new c (prf (out c) p \| prf (inp c) q).
 Proof.
   step.
   split; intros l p' pp'; simpl; inverse_trans; eauto with ccs.
 Qed.

 Lemma prf_prf_tau_new_o l c p q:
   fresh c l ->
   prf l (prf tau (new c (p \| q))) ~ new c (prf l (prf (out c) p) \| prf (inp c) q).
 Proof.
   intro H. step.
   split; intros l' p' pp'; simpl; inverse_trans;
     eexists; eauto with ccs; apply prf_tau_new.
 Qed.

 Lemma prf_prf_tau_new_i l c p q:
   fresh c l ->
   prf l (prf tau (new c (p \| q))) ~ new c (prf (out c) p \| prf l (prf (inp c) q)).
 Proof.
   intro H. step.
   split; intros l' p' pp'; simpl; inverse_trans;
     eexists; eauto with ccs; apply prf_tau_new.
 Qed.

 (* is a name [a] fresh in a process *)
 CoInductive freshp (a: N): S -> Prop :=
 | f_nil: freshp a 0
 | f_prf: forall l p, fresh a l -> freshp a p -> freshp a (prf l p) 
 | f_pls: forall p q, freshp a p -> freshp a q -> freshp a (p+q)
 | f_par: forall p q, freshp a p -> freshp a q -> freshp a (p\|q)
 | f_new: forall b p, a=b \/ freshp a p -> freshp a (new b p)
 | f_rep: forall p, freshp a p -> freshp a (!p).

 Lemma freshp_trans a p: freshp a p -> forall l p', trans p l p' -> fresh a l /\ freshp a p'.
 Proof.
   intros F l p' T. revert F.
   induction T; intro F; inversion F; subst; clear F;
     try (split; [simpl; tauto|firstorder; constructor; trivial]).
   - intuition subst; trivial; constructor; tauto.
   - apply IHT. now repeat constructor.
 Qed.

 Lemma new_gc: forall a p, freshp a p -> new a p ~ p.
 Proof.
   intro a. coinduction R HR; intros p Hp.
   pose proof (freshp_trans Hp) as H.
   split; intros l p' pp'; simpl. 
   - inverse_trans. eexists. eauto with ccs. apply HR. eapply H; eauto with ccs. 
   - specialize (H _ _ pp') as [? ?]. eauto with ccs. 
 Qed.

 Lemma prf_tau_new_i c p: freshp c p -> prf tau p ~ new c (prf (out c) 0 \| prf (inp c) p).
 Proof.
   intro. rewrite <- prf_tau_new.
   rewrite new_gc. aac_reflexivity.
   now repeat constructor.
 Qed.
 
 Lemma prf_tau_new_o c p: freshp c p -> prf tau p ~ new c (prf (out c) p \| prf (inp c) 0).
 Proof.
   intro. rewrite <- prf_tau_new.
   rewrite new_gc. aac_reflexivity.
   now repeat constructor.
 Qed.

 Lemma new_par: forall a p q, freshp a q -> new a (p\|q) ~ (new a p) \| q.
 Proof.
   intro a. coinduction R HR. intros p q Hq.
   split; intros l p' pp'; simpl; inverse_trans;
     (match goal with
      | H: trans q _ _ |- _ => destruct (freshp_trans Hq H) as [??]
      | _ => idtac end);
     eauto 10 with ccs.
 Qed.
  
 Proposition rep_trans2 p l p0:
   trans (!p) l p0 ->
   (exists p', trans p l p' /\ p0 ~ !p \| p')
   \/ (l=tau /\ exists a po pi, trans p (out a) po /\ trans p (inp a) pi /\ p0 ~ rep p \| po \| pi).
 Proof.
   intro T. apply rep_trans in T as [p1 T E].
   inversion T; subst; clear T.
   - left. eexists. split. eauto with ccs. rewrite E. now aac_rewrite <-unfold_rep.
   - left. eexists. split. eauto with ccs. rewrite E. now aac_rewrite <-unfold_rep.
   - right. split; trivial. do 4 eexists. eauto with ccs. split. eauto with ccs. rewrite E. aac_reflexivity.
   - right. split; trivial. do 4 eexists. eauto with ccs. split. eauto with ccs. rewrite E. aac_reflexivity.
 Qed.

 Ltac inverse_trans' :=
   match goal with
   | H: trans ?p _ _ |- _ =>
     lazymatch p with
     | rep _ => apply rep_trans2 in H as [(?&?&?)|(?&?&?&?&?&?&?)];
                (try congruence); (try subst); inverse_trans'
     | _ => tryif is_var p then fail else inversion H; subst; clear H; inverse_trans'
     end
   | _ => idtac
   end.
 
 Lemma rep_pls p q: !(p+q) ~ !p \| !q.
 Proof.
   coinduction R H.
   split; intros a p' T; simpl; inverse_trans';
     (eexists; [eauto with ccs|rewrite ?H1, ?H3, H; aac_reflexivity]).
 Qed.

 Lemma rep_invol p: !(!p) ~ !p.
 Proof.
   coinduction R H.
   split; intros l p' T; simpl.
   - inverse_trans'.
     eexists. eauto with ccs. rewrite H1, H2. aac_rewrite<-unfold_rep. rewrite H. aac_reflexivity.
     eexists. eauto with ccs. rewrite H1, H4. aac_rewrite<-unfold_rep. rewrite H. aac_reflexivity. 
     eexists. eauto with ccs. rewrite H3, H2, H4. do 2 aac_rewrite<-unfold_rep. rewrite H. aac_reflexivity.     
   - destruct (rep_trans T) as [? _ E].
     eexists. eauto with ccs. rewrite E. aac_rewrite<-unfold_rep. rewrite H. aac_reflexivity. 
 Qed.

 Lemma rep_idem p: !p ~ !p \| !p.
 Proof. now rewrite <-rep_pls, plsI. Qed.

 Lemma rep_par p q: !(p \| q) ~ !p \| !q.
 Proof.
   coinduction R H.
   split; intros a p' T; simpl; inverse_trans';
     (eexists; [eauto with ccs|rewrite ?H1, ?H3, H; repeat aac_rewrite <-unfold_rep; aac_reflexivity]).
 Qed.

 Lemma rep_prf_trans a p b p': trans (!prf a p) b p' -> a=b /\ p' ~ p \| !prf a p.
 Proof.
   intro T. apply rep_trans in T as [p'' T E].
   inverse_trans; split; trivial;
     rewrite E; rewrite unfold_rep at 2.
   aac_reflexivity. aac_reflexivity. 
 Qed.
 
 Lemma rep_prf a p: !prf a p ~ prf a (p \| !prf a p).
 Proof.
   coinduction R H. split; intros b p' T.
   - apply rep_prf_trans in T as [<- E]. eexists. eauto with ccs. now rewrite E.
   - inverse_trans. eexists. eauto with ccs. simpl. aac_reflexivity. 
 Qed.

 Goal forall a p q, !prf a (p \| prf a q) \| !prf a (prf a p \| q) ~ !prf a p \| !prf a q.
 Proof.
   intros. coinduction R H.
   split; intros b p' T; simpl; inverse_trans'.
   - eexists. apply t_par_l; eauto with ccs.
     rewrite H1. aac_rewrite H. aac_rewrite <-unfold_rep. aac_reflexivity.
   - eexists. apply t_par_r; eauto with ccs.
     rewrite H1. aac_rewrite H. aac_rewrite <-unfold_rep. aac_reflexivity.
   - eexists. apply t_par_l; eauto with ccs.
     rewrite H1. aac_rewrite H. aac_rewrite <-unfold_rep. aac_reflexivity.
   - eexists. apply t_par_r; eauto with ccs.
     rewrite H1. aac_rewrite H. aac_rewrite <-unfold_rep. aac_reflexivity.
 Qed.

 Infix ">>" := (prf) (at level 30, right associativity): ccs_scope. 

 (* NOTE: while the freshness assumptions about b are merely bureaucratic,
    x<>y is crucial in the equality below:
    this equation fails otherwise, thus proving that bisimularity is not closed under substitutions, (even in the absence of sum).
 *)
 Goal forall x y b p,
     b<>x -> b<>y -> freshp b p ->
     x<>y -> 
     !(out y >> inp x >> tau >> p) \| !(inp x >> out y >> tau >> p)
     ~ 
     !new b (out y >> out b >> 0 \| inp x >> inp b >> p).
 Proof.
   intros x y b p BX BY BP XY.
   assert (BX': fresh b (inp x)) by congruence. 
   assert (BY': fresh b (out y)) by congruence.
   assert (BP': freshp b (0 \| p)) by now repeat constructor. 
   coinduction R H.
   split; intros l p' pp'; simpl; inverse_trans'; try congruence; 
     eexists; eauto with ccs; rewrite H1; clear H1; aac_rewrite H; apply part_t; trivial.
   - rewrite <-prf_prf_tau_new_i by assumption.
     rewrite new_gc by assumption.
     aac_reflexivity.
   - rewrite <-prf_prf_tau_new_o by assumption. 
     rewrite new_gc by assumption.
     aac_reflexivity.
   - rewrite <-prf_prf_tau_new_i by assumption.
     rewrite new_gc by assumption.
     aac_reflexivity.
   - rewrite <-prf_prf_tau_new_o by assumption. 
     rewrite new_gc by assumption.
     aac_reflexivity.
 Qed.   
 
End CCS.

(** * A proof by enhanced coinduction  *)

Module acd.
 CoInductive N': Type := a | c | d.
 Definition N := N'.
End acd.
Module Import CCSacd := CCS(acd).

(** The four processes from Section 4 *)
CoFixpoint A := inp a >> inp c >> D
      with B := inp a >> inp c >> C
      with C := out a >> (A \| C)
      with D := out a >> (B \| D).

Lemma dA: A = inp a >> inp c >> D.
Proof. apply Sd. Qed.
Lemma dB: B = inp a >> inp c >> C.
Proof. apply Sd. Qed.
Lemma dC: C = out a >> (A \| C).
Proof. apply Sd. Qed.
Lemma dD: D = out a >> (B \| D).
Proof. apply Sd. Qed.

(** Utilities to factor code thanks to the (relative) determinism of the considered processes *)
Lemma bAB (R: S -> S -> Prop): R (inp c >> D) (inp c >> C) -> b R A B.
Proof. intro. rewrite dA, dB. split; intros ? ? T; inversion_clear T; eauto with ccs. Qed.
Lemma bCD (R: S -> S -> Prop): R (A \| C) (B \| D) -> b R C D.
Proof. intro. rewrite dC, dD. split; intros ? ? T; inversion_clear T; eauto with ccs. Qed.

(** the proof by enhanced bisimulation *)
Goal A ~ B /\ C ~ D.
  coinduction R [AB CD]. split.
  apply bAB. now rewrite CD.     (* apply prft_t. now symmetry.  *)
  apply bCD. now rewrite AB, CD. (* now apply part_t.  *)
Qed.

(** refining the candidate on-the-fly, using the [accumulate] tactic *)
Goal A ~ B.
  coinduction R AB.
  apply bAB. apply prft_t.
  symmetry. accumulate CD. 
  apply bCD. now rewrite AB, CD. 
Qed.
