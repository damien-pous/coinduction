(** * Tactics for coinductive n-ary relations *)

(* TODO: update comments! *)

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


Require Import lattice tower rel.
Set Implicit Arguments.

(** * Arities and relations *)
(** we call 'relations' elements whose type is of the shape
    - [X1 -> X2 -> ... -> Xn -> Prop]
    - or more generally, [forall x1: X1, forall x2: X2, ..., Xn -> Prop]
    those are reified via the definition [REL] below, using "arities" of the shape
    - [ABS X1 (fun _ => ABS X2 (fun _ => ... (ABS Xn (fun _ => PRP))))]
    - [ABS X1 (fun x1 => ABS X2 (fun x2 => ... (ABS Xn (fun _ => PRP))))]
 *)

(** (dependent) arities *)
Inductive Arity :=
| PRP
| ABS(B: Type)(Q: B -> Arity).
Arguments ABS _ _: clear implicits.
(** non-dependent case *)
Notation ABS' B Q := (ABS B (fun _ => Q)).

(** Coq corresponding relation types,
    the [K] argument of [REL'] is mostly instantiated with [Prop], as in [REL] below *)
Fixpoint REL' A K :=
  match A with
  | PRP => K
  | ABS B Q => forall b, REL' (Q b) K
  end.
Notation REL A := (REL' A Prop).

(** corresponding complete lattice structure *)
#[local] Instance CompleteLatticeREL A: CompleteLattice (REL A).
Proof.
  revert A. fix f 1; destruct A; simpl.
  apply CompleteLattice_Prop. 
  apply CompleteLattice_dfun; auto.
Defined.

(** (dependent) product type corresponding to the given arity, for curried operations *)
Fixpoint PRD A: Type :=
  match A with
  | PRP => unit
  | ABS B Q => sigT (fun b => PRD (Q b))
  end.

(** currying *)
Fixpoint curry [A K]: REL' A K -> PRD A -> K :=
  match A with
  | PRP => fun R _ => R
  | ABS B Q => fun R x => let (b,q) := x in curry (R b) q
  end.

(** uncurrying *)
Fixpoint uncurry [A K]: (PRD A -> K) -> REL' A K :=
  match A with
  | PRP => fun k => k tt
  | ABS B Q => fun k x => uncurry (fun p => k (existT _ x p))
  end.

(* note: the two lemmas below could be generalised to [REL'] *)
Lemma curryK [A] (R: REL A): uncurry (curry R) == R.
Proof.
  induction A; cbn.
  - reflexivity. 
  - intro b. apply H. 
Qed.

Lemma uncurry_leq [A] (h k: PRD A -> Prop): uncurry h <= uncurry k <-> h <= k.
Proof.
  induction A; cbn.
  - split. now intros ? []. now intro.
  - split.
    -- intros H' [b q]. 
       apply (H b (fun q => h (existT _ b q)) (fun q => k (existT _ b q))). apply H'.
    -- intros H' b. apply H. intro q. apply H'. 
Qed.

(** helper for the OCaml plugin: [prd A] produces tuples for arity [A] *)
Definition tuple A: REL' A (PRD A) := uncurry (fun x => x).

(** singleton relation *)
Definition EQ {A} (p: PRD A): REL A := uncurry (eq p). 

Lemma EQ_spec A (T: REL A) x: EQ x <= T <-> curry T x.
Proof.
  unfold EQ. 
  rewrite <-(curryK T) at 1.
  rewrite uncurry_leq. split.
  intros H. now apply H.
  now intros ? ? <-.
Qed.


(** * reification tools to transform propositions in the language of
      gallina into relation containments, e.g.,

      [forall x y, R (x+y) (y+x+x)]
      becomes 
      [sup_all (fun x => sup_all (fun y => pair (x+y) (y+x+x))) <= R]
      and the LHS gets further reified using [pT]

      [forall x y, R (x+y) y /\ R x y]
      becomes 
      [sup_all (fun x => sup_all (fun y => cup (pair (x+y) y) (pair x y))) <== R]
      and the LHS gets further reified using [pT]

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
   | abs _ _ => fun z => sup' top (fun b => rT (z b))
   | cnj _ _ => fun z => let (x,y) := z in cup (rT x) (rT y)
   end.
 
 (** key property of the above functions *)  
 Proposition eT A c R (x: fT A c): pT R x <-> rT x <= R.
 Proof.
   induction c; cbn; symmetry.
   - apply EQ_spec.
   - setoid_rewrite H. rewrite sup_spec. firstorder. 
   - destruct x. rewrite IHc1, IHc2. apply cup_spec.
 Qed. 

 (* examples on how to use eT/pT *)
 (*
 Goal forall R: relation nat, forall x y, R (x+y) (y+x+x).
   intro R.
   change (let A := (ABS' nat (ABS' nat PRP)) in @pT A
               (abs _ (fun x => abs _ (fun y => hol))) R
               (fun x y => tuple A (x+y) (y+x+x))).
 Abort.

 Goal forall R: relation nat, forall x y, R (x+y) y /\ R x y.
   intro R.
   change (let A := (ABS' nat (ABS' nat PRP)) in @pT A
               (abs _ (fun x => abs _ (fun y => cnj hol hol))) R
               (fun x y => (tuple A (x+y) y, tuple A x y))).
 Abort.

 Goal forall R: relation nat, forall x y, R (x+y) y /\ R x y.
   intro R.
   change (let A := (ABS' nat (ABS' nat PRP)) in @pT A
              (abs _ (fun x => abs _ (fun y => cnj hol hol))) R
              (fun x y => (tuple A (x+y) y, tuple A x y))).
   apply (eT (ABS' nat (ABS' nat PRP))
             (abs _ (fun x => abs _ (fun y => cnj hol hol)))).
   Restart.
   intro R.
   apply (let A := (ABS' nat (ABS' nat PRP)) in @eT A
             (abs _ (fun x => abs _ (fun y => cnj hol hol)))
             R
             (fun x y => (tuple A (x+y) y, tuple A x y))).
 Abort.
 *)
 
 (** ** tools for the [coinduction] tactic *)


 Lemma inf_closed_pT A c (x: fT A c): inf_closed (fun y => pT y x).
 Proof.
   intros T HT. 
   rewrite eT. apply inf_spec. intros R TR.
   rewrite <-eT. apply HT, TR.
 Qed.
   
 (** reformulation of the tower induction lemma using reified terms
     for the tactic [coinduction]
     not used in practice, it is subsumed by Proposition [ptower] below *)
 Proposition tower A c (b: mon (REL A)) (x: fT A c):
     (forall R: Chain b, pT `R x -> pT (b `R) x) -> 
     (pT (gfp b) x).
 Proof.
   intro H.
   cut (forall R: Chain b, pT `R x). intros E. apply E. 
   apply (tower' (inf_closed_pT _ _ x)). apply H.
 Qed.

 (* idea: the above lemma can be used as follows: *)
 (*
 Section s.
  Variable b: mon (nat -> nat -> Prop).
  Goal forall n m (k: n=m), gfp b (n+n) (m+m) /\ forall k, gfp b (n+k) (k+m).
    apply (let A := ABS' nat (ABS' nat PRP) in
           coinduction A
            (abs nat (fun n =>
             abs nat (fun m => 
             abs (n=m) (fun _ => 
                          cnj hol (abs nat (fun _ => hol))))))
            b
            ((fun n m _ => (tuple A (n+n) (m+m), fun k => tuple A (n+k) (k+m))))
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

 (** reformulation of the relativised tower induction lemma using reified terms
     this is the lemma which is applied in tactic [accumulate] *)
 Proposition ptower A (b: mon (REL A)) cs c (x: fT A c):
     (forall R: Chain b, pTs (tsnoc cs x) `R (pT (b `R) x)) ->
     (forall R: Chain b, pTs cs `R (pT `R x)).
 Proof.
   setoid_rewrite eTs.
   setoid_rewrite merge_tsnoc.
   intro H.
   refine (ptower _ (inf_closed_pT _ _ _) _). 
   intros R HR Hyps. apply H; trivial.
   cbn; apply cup_spec. now rewrite <-eT.
 Qed.

 (** ** tools for the [symmetric] tactic *)

 Section sym.
   Variable A: Type.
   Let A2 := ABS A (fun _ => ABS A (fun _ => PRP)).

   (** converse operation on [fT] *)
   Fixpoint converse_fT [c]: fT A2 c -> fT A2 c :=
     match c with
     | hol => fun z => let 'existT _ x (existT _ y _) := z in tuple A2 y x
     | abs _ _ => fun x b => (converse_fT (x b))
     | cnj _ _ => fun z => let (x,y) := z in (converse_fT x,converse_fT y)
     end.

   Lemma existT_nodep_eq (a b: A) T (x y: T):
     existT (fun _ => T) a x = existT (fun _ => T) b y <->  a = b /\ x = y.
   Proof. split. intro H. inversion H. tauto. intuition congruence. Qed.

   Lemma converse_rT c (x: fT A2 c): converse (rT x) == rT (converse_fT x).
   Proof.
     induction c; simpl rT; intros i j. 
     - destruct x as (x,(y,[])). cbn.
       rewrite 4existT_nodep_eq. tauto. 
     - etransitivity. apply converse_sup. refine (sup_weq _ _).
       reflexivity. intros b. apply H.
     - destruct x. etransitivity. apply converse_cup.
       apply (@cup_weq _ _ _ _ (IHc1 _) _ _ (IHc2 _)).
   Qed.
 
   (** reformulation of the symmetry lemma using reified terms
       this is the lemma which is applied in tactic [symmetric]
    *)
   Lemma by_symmetry c (x: fT A2 c) {b s: mon (A -> A -> Prop)} {S: Symmetrical converse b s} (R: Chain b):
     (* alternative to the hypothesis below: *)
     (* (forall i j, rT x j i -> rT x i j) -> *)
     (forall R, @pT A2 c R x -> @pT A2 c R (converse_fT x)) ->
     @pT A2 c (s `R) x ->
     @pT A2 c (b `R) x.
   Proof.
     rewrite 2!eT. intros C H. rewrite symmetrical_chain.
     apply cap_spec. split; trivial.
     apply switch. rewrite (converse_rT _ x), <-eT.
     apply C. now rewrite eT. 
   Qed.
 End sym.
 
End reification.

(** * Exported tactics *)

(** registering constants required in the OCaml plugin  *)
Register body                    as coinduction.body.
Register elem                    as coinduction.elem.
Register Chain                   as coinduction.Chain.
Register gfp                     as coinduction.gfp.
Register Symmetrical             as coinduction.Symmetrical.
Register PRP                     as coinduction.PRP.
Register ABS                     as coinduction.ABS.
Register tuple                   as coinduction.tuple.
Register reification.hol         as coinduction.hol.
Register reification.abs         as coinduction.abs.
Register reification.cnj         as coinduction.cnj.
Register reification.fT          as coinduction.fT.
Register reification.pT          as coinduction.pT.
Register reification.tnil        as coinduction.tnil.
Register reification.tcons       as coinduction.tcons.
Register reification.ptower      as coinduction.ptower.
Register reification.by_symmetry as coinduction.by_symmetry.

(** loading the OCaml plugin  *)
Declare ML Module "coq-coinduction.plugin". 

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
Tactic Notation "coinduction" ident(R) simple_intropattern(H) :=
  apply gfp_prop; intro R; apply_ptower R O; intros H.

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
Ltac xaccumulate R n :=
  lazymatch goal with
  | H: context[R] |- _ => revert H; xaccumulate R (S n); intro H
  | _ => apply_ptower R n
  end.

Tactic Notation "accumulate" hyp(R) simple_intropattern(H) :=
  xaccumulate R O; intros H; simpl REL in *.

Tactic Notation "accumulate" simple_intropattern(H) :=
  lazymatch goal with
  | R: Chain _ |- _ => accumulate R H
  | _ => fail "could not find the coinductive candidate"
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
Ltac default_sym_tac := solve[clear;firstorder]||fail "could not get symmetry automatically".
Tactic Notation "symmetric" hyp(R) "using" tactic(tac) :=
  apply_by_symmetry R; [simpl reification.pT; tac|].
Tactic Notation "symmetric" hyp(R) :=
  symmetric R using default_sym_tac.
Tactic Notation "symmetric" "using" tactic(tac) :=
  lazymatch goal with
  | R: Chain _ |- _ => symmetric R using tac
  | _ => fail "could not find the coinductive candidate"
  end.
Tactic Notation "symmetric" :=
  lazymatch goal with
  | R: Chain _ |- _ => symmetric R
  | _ => fail "could not find the coinductive candidate"
  end.

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
Ltac step := apply b_chain; simpl body.
