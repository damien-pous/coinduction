(** * Tactics for coinductive binary relations *)

(**
we provide three tactics:
- [coinduction R H] to start a proof by coinduction 
  [R] is a name for the bisimulation candidate,
  [H] is an introduction pattern for the properties of the candidate
- [accumulate H] to accumulate new pairs in the bisimulation candidate
  [H] is an introduction pattern, as above
- [symmetric] to reason by symmetry when the coinductive relation is defined by a symmetric function.
  this tactics makes it possible to play only half of the coinductive game, provided it manages to prove automatically that the candidate is symmetric.
  A tactic [tac] for solving the symmetry requirement may be passed as follows:
  [symmetric using tac]
  (by default, we use solve[clear;firstorder])
*)


Require Import lattice coinduction rel.
Set Implicit Arguments.


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
      [pT (abs (fun x => abs (fun y => cnj hol hol))) R (fun x y => (x+y,y)) (fun x y => (x,y))]

*)
Module reification.

 (** dependently typed syntax for formulas of the shape
     forall x y, R t1 t2 /\ forall z, R s1 s2 *)
 Inductive T :=
 | hol
 | abs(B: Type)(Q: B -> T)
 | cnj(H K: T).
 Arguments abs _ _: clear implicits. 

 Fixpoint fT A (c: T) :=
   match c with
   | hol => A
   | abs B Q => forall b: B, fT A (Q b)
   | cnj H K => (fT A H * fT A K)%type
   end.
 Fixpoint pT A (R: A -> A -> Prop) (c: T): fT A c -> fT A c -> Prop :=
   match c with
   | hol => R
   | abs B Q => fun x y => forall b, pT R (Q b) (x b) (y b)
   | cnj H K => fun x y => pT R H (fst x) (fst y) /\ pT R K (snd x) (snd y)
   end.
 Fixpoint rT A (c: T): fT A c -> fT A c -> A -> A -> Prop :=
   match c with
   | hol => @pair A
   | abs B Q => fun x y => sup_all (fun b => rT (Q b) (x b) (y b))
   | cnj H K => fun x y => cup (rT H (fst x) (fst y)) (rT K (snd x) (snd y))
   end.
 (** key lemma about the above functions *)
 Lemma eT A R (c: T): forall x y: fT A c, pT R c x y <-> rT c x y <= R.
 Proof.
   induction c; intros x y; simpl pT.
   - apply leq_pair.
   - setoid_rewrite H. symmetry. apply sup_all_spec.
   - rewrite IHc1, IHc2. symmetry. apply cup_spec.  
 Qed.

 (** ** tools for the [coinduction] tactic *)
 
 (** reformulation of the enhanced coinduction lemma using reified terms
     this is the lemma which is applied in tactic [coinduction]
  *)
 Proposition coinduction A (b: mon (A -> A -> Prop)) c x y:
     (forall R, pT (t b R) c x y -> pT (b (t b R)) c x y) ->
     pT (gfp b) c x y.
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

 (** ** tools for the [accumulate] tactic *)

 (** in order to implement the accumulation rule, 
     we also need to record the existing assumptions about the current candidate 
     we do so using "lists of [T]s" ([Ts]), which we can later merge into a single relation
  *)
 Inductive Ts A :=
 | tnil
 | tcons(c: T)(x y: fT A c)(Q: Ts A).
 (** semantics of [Ts], as hypotheses  *)
 Fixpoint pTs A (R: A -> A -> Prop) (cs: Ts A) (P: Prop): Prop :=
   match cs with
   | tnil _ => P
   | tcons c x y cs => pT R c x y -> @pTs _ R cs P
   end.
 Fixpoint merge A (cs: Ts A): A -> A -> Prop :=
   match cs with
   | tnil _ => bot
   | tcons c x y cs => cup (rT c x y) (merge cs)
   end.
 (** key lemma about the above functions  *)
 Lemma eTs A R cs P: @pTs A R cs P <-> (merge cs <= R -> P).
 Proof.
   induction cs.
   - split. trivial. intro H; apply H. apply leq_bx.
   - simpl pTs. simpl merge. rewrite cup_spec, IHcs, eT. tauto.
 Qed.
 (** in order to add the current goal as an hypothesis *at the end of the goal*, 
     we need an operation to insert it *at the end of a list* *)
 Fixpoint tsnoc {A} cs c x y :=
   match cs with
   | tnil _ => tcons c x y (tnil A)
   | tcons c' x' y' cs => tcons c' x' y' (tsnoc cs c x y)
   end.
 Lemma merge_tsnoc A cs c x y: merge (@tsnoc A cs c x y) == merge (tcons c x y cs).
 Proof.
   induction cs.
   - reflexivity.
   - simpl tsnoc. simpl merge.
     rewrite IHcs. simpl merge. now rewrite cupA, (cupC (rT _ _ _)), <-cupA.
 Qed.
 (** reformulation of the accumulation lemma using reified terms
     this is the lemma which is applied in tactic [accumulate]
  *)
 Proposition accumulate A (b: mon (A -> A -> Prop)) cs c x y:
     (forall R, pTs (t b R) (tsnoc cs c x y) (pT (b (t b R)) c x y)) ->
     (forall R, pTs (t b R) cs (pT (t b R) c x y)).
 Proof.
   setoid_rewrite eTs.
   setoid_rewrite merge_tsnoc. 
   intros H R HR. rewrite eT. apply accumulate. 
   rewrite <-eT. apply H. simpl merge. rewrite cup_spec. split.
   rewrite <-cup_r. apply id_t.
   rewrite <-cup_l. assumption. 
 Qed.

 (** ** tools for the [symmetric] tactic *)
 
 Lemma converse_rT A c x y: converse (@rT A c x y) == rT c y x.
 Proof.
   induction c; simpl rT; intros i j.
   - apply converse_pair.
   - etransitivity. apply converse_sup. refine (sup_weq _ _).
     reflexivity. intros b. apply H.
   - etransitivity. apply converse_cup. apply (@cup_weq _ _ _ _ (IHc1 _ _) _ _ (IHc2 _ _)).
 Qed.
     
 (** reformulation of the symmetry lemma using reified terms
     this is the lemma which is applied in tactic [symmetric]
  *)
 Lemma by_symmetry A c x y {b s: mon (A -> A -> Prop)} {S: Sym_from converse b s} R:
   (* alternative to the hypothesis below: *)
   (* (forall i j, rT c x y j i -> rT c x y i j) -> *)
   (forall R, pT R c x y -> pT R c y x) ->
   pT (s (t b R)) c x y ->
   pT (b (t b R)) c x y.
 Proof.
   rewrite 2!eT. intros C H. apply by_symmetry. 2: assumption.
   rewrite converse_rT, <-eT. apply C. now rewrite eT. 
 Qed.
 
End reification.

(** * Exported tactics *)

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
    forall x y..., b (t b R) u v /\ forall z, P -> b (t b R) s t

    [R] is the bisimulation up-to candidate.
    [H] expresses the pairs [R] is assumed to contain.
    Those pairs are actually assumed to be only in [t b R], the closure of [R] under the companion, simply because this is more convenient in practice.
    Note the additional occurrences of [b] in the conclusion: now we should play at least one step of the coinductive game for all pairs inserted in the candidate.
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
    forall i j, b (t b R) p q

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
Ltac xaccumulate n R tbR :=
  lazymatch goal with
  | H: context[tbR _ _] |- _ => revert H; xaccumulate (S n) R tbR; intro H
  | _ => apply_accumulate n R
  end.

Tactic Notation "accumulate" simple_intropattern(H) :=
  find_candidate;
  match goal with
    |- ?tbR = _ -> _ =>
    match tbR with
    | body (t _) ?R => intros _; xaccumulate O R tbR; intros H
    end
  end.


(** reasoning on symmetric candidates with symmetric functions *)
(** this tactic makes it possible to play only half of the coinductive game in cases where both the game and the current goal are symmetric:
    - that the game is symmetric is inferred using the typeclasse [Sym_from]
    - that the goal is symmetric is proven using the given tactic (by default, [firstorder])
    the goal should be of the form
    [forall x y..., b (t b R) u v] 
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
