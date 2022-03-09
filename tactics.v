(** * Tactics for coinductive n-ary relations *)

(**
we provide three tactics:
- [coinduction R H] to start a proof by coinduction 
  [R] is a name for the bisimulation candidate,
  [H] is an introduction pattern for the properties of the candidate
- [accumulate H] to accumulate new pairs in the bisimulation candidate
  [H] is an introduction pattern, as above
- [symmetric] to reason by symmetry when the coinductive (binary) relation is defined by a symmetric function.
  this tactics makes it possible to play only half of the coinductive game, provided it manages to prove automatically that the candidate is symmetric.
  A tactic [tac] for solving the symmetry requirement may be passed as follows:
  [symmetric using tac]
  (by default, we use solve[clear;firstorder])
*)


Require Import lattice coinduction rel.
Set Implicit Arguments.

(** arity for relations (e.g., A -> B -> Prop) *)
Inductive Arity :=
| PRP
| ABS(B: Type)(Q: Arity).
Arguments ABS _ _: clear implicits.

Fixpoint REL' A PROP :=
  match A with
  | PRP => PROP
  | ABS B Q => B -> REL' Q PROP
  end.
Notation REL A := (REL' A Prop).

#[local] Instance CompleteLatticeREL A: CompleteLattice (REL A).
Proof. revert A. fix f 1; destruct A; simpl; eauto with typeclass_instances. Defined.

Fixpoint PRD A: Type :=
  match A with
  | PRP => unit
  | ABS B Q => prod B (PRD Q)
  end.

Fixpoint curry [A]: REL A -> PRD A -> Prop :=
  match A with
  | PRP => fun R _ => R
  | ABS B Q => fun R x => let (b,q) := x in curry (R b) q
  end.

(* helper for the OCaml plugin: [prd A] produces tuples for arity [A] *)
Fixpoint kprd [A K]: (PRD A -> K) -> REL' A K :=
  match A with
  | PRP => fun k => k tt
  | ABS B Q => fun k x => kprd (fun p => k (x,p))
  end.
Definition prd {A}: REL' A (PRD A) := @kprd A _ (fun x => x).
         
Fixpoint cons (P: Prop) {A}: REL A -> REL A :=
  match A with
  | PRP => fun Q => P /\ Q
  | ABS B Q => fun R b => cons P (R b)
  end.
Fixpoint EQ {A}: PRD A -> REL A :=
  match A with
  | PRP => fun _ => True
  | ABS B Q => fun x b => cons (b = fst x) (EQ (snd x))
  end.
Fixpoint OR {A}: REL A -> REL A -> REL A :=
  match A with
  | PRP => or 
  | ABS B Q => fun R S b => OR (R b) (S b)
  end.
Fixpoint EX {X A}: (X -> REL A) -> REL A :=
  match A return (X -> REL A) -> REL A with
  | PRP => fun P => exists x, P x 
  | ABS B Q => fun P b => EX (fun x => P x b)
  end.


(* TOTHINK: more direct proof of cons_spec? *)
Lemma cons_true A (S: REL A) (P: Prop): P -> S <= cons P S.
Proof.
  intro p. induction A as [|A Q IH]; simpl cons.
  - now cbv.
  - intro a. apply IH.
Qed.
Lemma cons_fwd A: forall B (R: B -> REL A) b b', cons (b'=b) (R b) <= R b'.
Proof.
  intro B. induction A as [|A Q IH]; simpl cons; intros R b b'.
  - now intros [<- ].
  - intro a. apply (IH (fun b => R b a)).
Qed.
#[local] Instance cons_mon A P: Proper (leq ==> leq) (@cons P A).
Proof.
  induction A as [|A Q IH]; simpl cons; intros R S RS.
  - cbv in *; tauto. 
  - intro a. apply IH, RS. 
Qed.
Lemma cons_spec A (S: REL A): forall B (R: B -> REL A) b, S <= R b <-> (fun b': B => cons (b'=b) S) <= R.
Proof.
  destruct A as [|C Q]; simpl cons; intros B R b.
  - cbv. firstorder congruence. 
  - split; intro H.
    intros b' c. specialize (H c). rewrite H. apply (cons_fwd _ (fun b => R b c)). 
    intro c. rewrite<-(H b c). now apply cons_true. 
Qed.

Lemma EQ_spec A (T: REL A) x: curry T x <-> EQ x <= T.
Proof.
  induction A as [|B Q IH]. cbv. tauto.
  destruct x as [b q]. cbn. rewrite IH.
  apply cons_spec.
Qed.

Lemma EX_spec A X R (T: REL A): (forall x: X, R x <= T) <-> EX R <= T.
Proof.
  induction A as [|B Q IH]. cbv; firstorder. 
  cbn. split; intros H x. apply IH. intro. apply H.
  intros b. apply <-(IH (fun x => R x b)). apply H. 
Qed.

Lemma OR_spec A (R S T: REL A): R <= T /\ S <= T <-> OR R S <= T.
Proof.
  induction A as [|B Q IH]. cbv; tauto.
  cbn. split. intros [H K] b. apply IH. now split.
  intro H; split; intro b; apply <-(IH (R b) (S b) (T b)); apply H. 
Qed.


(** * reification tools to transform propositions in the language of
      gallina into relation containments, e.g.,

      [forall x y, R (x+y) (y+x+x)]
      becomes 
      [sup_all (fun x => sup_all (fun y => pair (x+y) (y+x+x))) <== R]
      which in turn becomes
      [pT (abs (fun x => abs (fun y => hol))) R (fun x y => (x+y)) (fun x y => (y+x+x))]

      [forall x y, R (x+y) y /\ R x y]
      becomes 
      [sup_all (fun x => sup_all (fun y => cup (pair (x+y) y) (pair x y)))) <== R]
      which in turn becomes
      [pT (abs (fun x => abs (fun y => cnj hol hol))) R (fun x y => (x+y,x)) (fun x y => (y,y))]

*)
Module reification.

 (** dependently typed syntax for formulas of the shape
     forall x y, R t1 t2 /\ forall z, R s1 s2 *)
 Inductive T :=
 | hol
 | abs(B: Type)(Q: B -> T)
 | cnj(H K: T).
 Arguments abs _ _: clear implicits. 

 Fixpoint fT A c :=
   match c with
   | hol => PRD A
   | abs B Q => forall b: B, fT A (Q b)
   | cnj H K => (fT A H * fT A K)%type
   end.

 Fixpoint pT [A c] (R: REL A): fT A c -> Prop :=
   match c with
   | hol => curry R
   | abs _ _ => fun x => forall b, pT R (x b)
   | cnj _ _ => fun xy => let (x,y) := xy in pT R x /\ pT R y
   end.
 
 Fixpoint rT [A c]: fT A c -> REL A := 
   match c with
   | hol => EQ
   | abs _ _ => fun z => EX (fun b => rT (z b))
   | cnj _ _ => fun z => let (x,y) := z in OR (rT x) (rT y)
   end.
 
 (** key property of the above functions *)  
 Proposition eT A c R (x: fT A c): pT R x <-> rT x <= R.
 Proof.
   induction c; cbn.
   - apply EQ_spec.
   - setoid_rewrite H. apply EX_spec.
   - destruct x. rewrite IHc1, IHc2. apply OR_spec.
 Qed. 

 (* examples on how to use eT/pT *)
 (*
 Goal forall R: relation nat, forall x y, R (x+y) (y+x+x).
   intro R.
   change (@pT (ABS nat (ABS nat PRP))
               (abs _ (fun x => abs _ (fun y => hol))) R
               (fun x y => (x+y,(y+x+x,tt)))).
 Abort.

 Goal forall R: relation nat, forall x y, R (x+y) y /\ R x y.
   intro R.
   change (@pT (ABS nat (ABS nat PRP))
               (abs _ (fun x => abs _ (fun y => cnj hol hol))) R
               (fun x y => ((x+y,(y,tt)),(x,(y,tt))))).
 Abort.

 Goal forall R: relation nat, forall x y, R (x+y) y /\ R x y.
   intro R.
   change (@pT (ABS nat (ABS nat PRP))
              (abs _ (fun x => abs _ (fun y => cnj hol hol))) R
              (fun x y => ((x+y,(y,tt)),(x,(y,tt))))).
   apply (eT (ABS nat (ABS nat PRP))
             (abs _ (fun x => abs _ (fun y => cnj hol hol)))).
   Restart.
   intro R.
   apply (eT (ABS nat (ABS nat PRP))
             (abs _ (fun x => abs _ (fun y => cnj hol hol)))
             R
             (fun x y => ((x+y,(y,tt)),(x,(y,tt))))).
 Abort.
 *)
 
 (** ** tools for the [coinduction] tactic *)
 
 (** reformulation of the enhanced coinduction lemma using reified terms
     this is the lemma which is applied in tactic [coinduction]
  *)
 Proposition coinduction A c (b: mon (REL A)) (x: fT A c):
     (forall R, pT (t b R) x -> pT (bt b R) x) -> pT (gfp b) x.
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
    apply (coinduction
            (ABS nat (ABS nat PRP))
            (abs nat (fun n =>
             abs nat (fun m => 
             abs (n=m) (fun _ => 
                          cnj hol (abs nat (fun _ => hol))))))
            b
            ((fun n m _ => ((n+n,(m+m,tt)), fun k => (n+k,(k+m,tt)))))
          ).
    simpl pT. simpl curry. simpl REL.
    Transparent cap. simpl cap. Opaque cap.
    intros R HR. 
  Abort.
 End s.
  *)
 
 (** ** tools for the [accumulate] tactic *)

 (** in order to implement the accumulation rule, 
     we also need to record the existing assumptions about the current candidate 
     we do so using "lists of [T]s" ([Ts]), which we can later merge into a single relation
  *)
 Inductive Ts A :=
 | tnil
 | tcons [c] (x: fT A c) (Q: Ts A).
 (** semantics of [Ts], as hypotheses  *)
 Fixpoint pTs A (cs: Ts A) (R: REL A) (P: Prop): Prop :=
   match cs with
   | tnil _ => P
   | tcons x cs => pT R x -> pTs cs R P
   end.
 Fixpoint merge A (cs: Ts A): REL A :=
   match cs with
   | tnil _ => bot
   | tcons x cs => cup (rT x) (merge cs)
   end.
 (** key lemma about the above functions  *)
 Lemma eTs A (cs: Ts A) R P: pTs cs R P <-> (merge cs <= R -> P).
 Proof.
   induction cs.
   - split. trivial. intro H; apply H. apply leq_bx.
   - simpl pTs. simpl merge. rewrite cup_spec, IHcs, eT. tauto.
 Qed.
 (** in order to add the current goal as an hypothesis *at the end of the goal*, 
     we need an operation to insert it *at the end of a list* *)
 Fixpoint tsnoc [A] cs [c] (x: fT A c) :=
   match cs with
   | tnil _ => tcons x (tnil A)
   | tcons x' cs => tcons x' (tsnoc cs x)
   end.
 Lemma merge_tsnoc A cs c x: merge (@tsnoc A cs c x) == merge (tcons x cs).
 Proof.
   induction cs.
   - reflexivity.
   - simpl tsnoc. simpl merge.
     rewrite IHcs. simpl merge. now rewrite cupA, (cupC (rT _)), <-cupA.
 Qed.
 (** reformulation of the accumulation lemma using reified terms
     this is the lemma which is applied in tactic [accumulate]
  *)
 Proposition accumulate A (b: mon (REL A)) cs c (x: fT A c):
     (forall R, pTs (tsnoc cs x) (t b R) (pT (bt b R) x)) ->
     (forall R, pTs cs (t b R) (pT (t b R) x)).
 Proof.
   setoid_rewrite eTs.
   setoid_rewrite merge_tsnoc. 
   intros H R HR. rewrite eT. apply accumulate. 
   rewrite <-eT. apply H. simpl merge. rewrite cup_spec. split.
   rewrite <-cup_r. apply id_t.
   rewrite <-cup_l. assumption. 
 Qed.

 (** ** tools for the [symmetric] tactic *)

 Section sym.
   Variable A: Type.
   Let A2 := ABS A (ABS A PRP).

   (** converse operation on [fT] *)
   Fixpoint converse_fT [c]: fT A2 c -> fT A2 c :=
     match c with
     | hol => fun z => let '(x,(y,tt)) := z in (y,(x,tt))
     | abs _ _ => fun x b => (converse_fT (x b))
     | cnj _ _ => fun z => let (x,y) := z in (converse_fT x,converse_fT y)
     end.

   Lemma converse_rT c (x: fT A2 c): converse (rT x) == rT (converse_fT x).
   Proof.
     induction c; simpl rT; intros i j. 
     - destruct x as (x,(y,[])). cbn. tauto. 
     - split; intros [z Hz]; exists z; revert Hz; apply H.
     - destruct x as (x,y). specialize (IHc1 x i j). specialize (IHc2 y i j). cbn in *. tauto.
   Qed.
 
   (** reformulation of the symmetry lemma using reified terms
       this is the lemma which is applied in tactic [symmetric]
    *)
   Lemma by_symmetry c (x: fT A2 c) {b s: mon (A -> A -> Prop)} {S: Sym_from converse b s} R:
     (* alternative to the hypothesis below: *)
     (* (forall i j, rT x j i -> rT x i j) -> *)
     (forall R, @pT A2 c R x -> @pT A2 c R (converse_fT x)) ->
     @pT A2 c (s (t b R)) x ->
     @pT A2 c (bt b R) x.
   Proof.
     rewrite 2!eT. intros C H. apply by_symmetry. 2: assumption.
     rewrite (converse_rT _ x), <-eT. apply C. now rewrite eT. 
   Qed.
 End sym.
 
End reification.

(** * Exported tactics *)

(** registering constants required in the OCaml plugin  *)
Register body                    as coinduction.body.
Register t                       as coinduction.t.
Register bt                      as coinduction.bt.
Register gfp                     as coinduction.gfp.
Register Sym_from                as coinduction.Sym_from.
Register PRP                     as coinduction.PRP.
Register ABS                     as coinduction.ABS.
Register prd                     as coinduction.prd.
Register reification.hol         as coinduction.hol.
Register reification.abs         as coinduction.abs.
Register reification.cnj         as coinduction.cnj.
Register reification.fT          as coinduction.fT.
Register reification.pT          as coinduction.pT.
Register reification.tnil        as coinduction.tnil.
Register reification.tcons       as coinduction.tcons.
Register reification.coinduction as coinduction.coinduction.
Register reification.accumulate  as coinduction.accumulate.
Register reification.by_symmetry as coinduction.by_symmetry.

(** loading the OCaml plugin  *)
Declare ML Module "reification". 

(** ** starting a proof by (enhanced) coinduction *)
(** when the goal is of the shape

    [forall x y..., gfp b u v /\ forall z, P -> gfp b s t]

    where x,y... may appear in u, v, P, s, t and z may appear in P, s ,t
    (more complex alternations of quantifiers/conjunctions/implications being allowed)
    and [b] is the function for the considered coinductive relation

    [coinduction R H] moves to a goal

    R: A -> A -> Prop
    H: forall x y..., t b R u v /\ forall z, P -> t b R s t
    -------------------------------------------------------
    forall x y..., bt b R u v /\ forall z, P -> bt b R s t

    [R] is the bisimulation up-to candidate.
    [H] expresses the pairs [R] is assumed to contain.
    Those pairs are actually assumed to be only in [t b R], the closure of [R] under the companion, simply because this is more convenient in practice.
    Note the move to [bt] in the conclusion: now we should play at least one step of the coinductive game for all pairs inserted in the candidate.
    Also note that [H] maybe an introduction pattern.
 *)
(** we use the OCaml defined [apply_coinduction] tactic, whose role is:
    - to parse the goal to recognise a bisimulation candidate
    - to `apply' [reification.coinduction] with reified arguments corresponding to that candidate
    - to `change' the new goal to get rid of the reified operations and get back to a goal resembling the initial one
    (The last step could be implemented with [simpl reification.pT], but this would result in unwanted additional simplifications, and this resets names of bound variables in a very bad way. This is why we spend time in OCaml to reconstruct a type for the new goal by following syntactically the initial one.)
  *)
Tactic Notation "coinduction" simple_intropattern(R) simple_intropattern(H) :=
  apply_coinduction; intros R H.

(** ** accumulating knowledge in a proof by enhanced coinduction *)

(** when the goal is of the shape, typically obtained after starting a proof by coinduction and    performing one step of the coinductive game:

    R: A -> A -> Prop
    H: forall x y, t b R u v
    H': forall x y z, P -> t b R s t
    --------------------------------
    forall i j, t b R p q

    (more complex alternations of quantifiers/conjunctions/implications being allowed in both hypotheses and conclusion)

    [accumulate H''] moves to a goal

    R: A -> A -> Prop
    H: forall x y, t b R u v
    H': forall x y z, P -> t b R s t
    H'': forall i j, t b R p q
    --------------------------------
    forall i j, bt b R p q

    The conclusion has saved as an hypothesis [H''],
    and a [b] has been inserted in the conclusion, so that we have to play at least one step of the coinductive game on the added pairs

    Like for [coinduction], [H''] maybe an introduction pattern.
 *)

(** the implementation is a bit more involved:
    - we first find the current bisimulation candidate, using the OCaml tactic [find_candidate]
    - we successively revert all assumptions about this candidate into the conclusion
    - we use the OCaml tactic [apply_accumulate] in order to reify the goal, apply [reification.accumulate] with appropriate arguments, and get rid of the reified operations 
    - then we move the hypotheses back to the context,
    - and we introduce the new hypothesis
  *)
Ltac xaccumulate n R :=
  lazymatch goal with
  | H: context[R] |- _ => revert H; xaccumulate (S n) R; intro H
  | _ => apply_accumulate n R
  end.

Tactic Notation "accumulate" simple_intropattern(H) :=
  find_candidate;
  match goal with
    |- ?tR = _ -> _ =>
    match tR with
    | body (t _) ?R => intros _; xaccumulate O R; intros H
    end
  end.


(** reasoning on symmetric candidates with symmetric functions *)
(** this tactic makes it possible to play only half of the coinductive game in cases where both the game and the current goal are symmetric:
    - that the game is symmetric is inferred using the typeclasse [Sym_from]
    - that the goal is symmetric is proven using the given tactic (by default, [firstorder])
    the goal should be of the form
    [forall x y..., bt b R u v] 
    it moves to a goal of the form
    [forall x y..., s (t b R) u v] 
    ([t] is the companion, [b] the function for the coinductive game, [s] the function for the `half of [b]'; conjunctions are also allowed, like in the other tactics)
 *)
(** as above, we use the OCaml defined tactic [apply_by_symmetry] in order to apply the lemma [reification.by_symmetry] and set the resulting goal back into a user-friendly shape *)
Tactic Notation "symmetric" "using" tactic(tac) :=
  apply_by_symmetry; [simpl reification.pT; tac|].
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


(** performing a single step 
    (equivalent to [accumulate _], except that we do not deal with composite candidates and the coinductive proof need not be started) *)
Ltac step :=
  match goal with
  | |- gfp ?b ?x ?y => apply (proj2 (gfp_fp b x y))
  | |- body (t ?b) ?R ?x ?y => apply (bt_t b R x y)
  end;
  simpl body.
