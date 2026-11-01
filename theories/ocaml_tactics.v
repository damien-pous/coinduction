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


(** in this file the tactics are defined using a deprecated ocaml plugin,
    see [elpi_tactics.v] for the new version, relying on elpi instead *)


Require Import lattice tower rel reification.
Import CoindNotations.
Set Implicit Arguments.

(** * Exported tactics *)

(** registering constants required in the OCaml plugin  *)
Register mon                     as coinduction.mon.
Register body                    as coinduction.body.
Register elem                    as coinduction.elem.
Register Chain                   as coinduction.Chain.
Register gfp                     as coinduction.gfp.
Register gfp_prop                as coinduction.gfp_prop.
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
Declare ML Module "rocq-coinduction.plugin". 

(** ** starting a proof by (enhanced) coinduction *)
(** when the goal is of the shape

    [forall x y..., gfp b u v /\ forall z, P -> gfp b s t]

    where x,y... may appear in u, v, P, s, t and z may appear in P, s ,t
    (more complex alternations of quantifiers/conjunctions/implications being allowed)
    and [b] is the function for the considered coinductive relation

    [coinduction R H] moves to a goal

    R: Chain b
    H: forall x y..., `R u v /\ forall z, P -> `R s t
    -------------------------------------------------------
    forall x y..., b `R u v /\ forall z, P -> b `R s t

    [R] should be understood as the bisimulation up-to candidate.
    [H] expresses the pairs [R] is assumed to contain.
    Note the move to [b `R] in the conclusion: now we should play at least one step of the coinductive game for all pairs inserted in the candidate.
    Also note that [H] maybe an introduction pattern.
 *)
(** we use the OCaml defined [apply_ptower] tactic, whose role is:
    - to parse the goal to recognise a bisimulation candidate
    - to `apply' [reification.ptower] with reified arguments corresponding to that candidate
    - to `change' the new goal to get rid of the reified operations and get back to a goal resembling the initial one
    (The last step could be implemented with [simpl reification.pT], but this would result in unwanted additional simplifications, and this resets names of bound variables in a very bad way. This is why we spend time in OCaml to reconstruct a type for the new goal by following syntactically the initial one.)
  *)
Tactic Notation "coinduction" ident(R) simple_intropattern(H) :=
  abstract_gfp; intro R; apply_ptower R O; intros H.

(** in case [gfp b] is named (eg. Definition x := gfp b), it is not possible to recognise it automatically.
    In those cases we can use the annotation "for x" *)
(* the following tactic makes it possible to retrieve [b] out of a defined term [x] convertible to [gfp b] *)
Definition get_gfp X L b x (e: @gfp X L b = x) := b.
Arguments get_gfp [_ _ _] _ _.
Ltac get_gfp x :=
  (eval unfold get_gfp in (get_gfp x eq_refl))
(* || fail "did not recognise" x "as a gfp" *).

(* BELOW: example of how to use [get_gfp] *)
(* Section s. *)
(*   Context X (L: CompleteLattice X) (b: mon X). *)
(*   Let x := gfp b. *)
(*   Goal True. *)
(*     let c := get_gfp x in set (b' := c). *)
(*     Fail let c := get_gfp nat in set (b'' := c). *)
(*   Abort. *)
(* End s. *)
    
Tactic Notation "coinduction" ident(R) simple_intropattern(H) "for" uconstr(x) :=
  let b := get_gfp x in
  abstract_gfp x b; intro R; apply_ptower R O; intros H.

(** ** accumulating knowledge in a proof by enhanced coinduction *)

(** when the goal is of the shape, typically obtained after starting a proof by coinduction and    performing one step of the coinductive game:

    R: Chain b
    H: forall x y, `R u v
    H': forall x y z, P -> `R s t
    --------------------------------
    forall i j, `R p q

    (more complex alternations of quantifiers/conjunctions/implications being allowed in both hypotheses and conclusion)

    [accumulate H''] moves to a goal

    R: Chain b
    H: forall x y, `R u v
    H': forall x y z, P -> `R s t
    H'': forall i j, `R p q
    --------------------------------
    forall i j, b `R p q

    The conclusion has been saved as an hypothesis [H''],
    and a [b] has been inserted in the conclusion, so that we have to play at least one step of the coinductive game on the added pairs

    Like for [coinduction], [H''] maybe an introduction pattern.
 *)

(** the implementation is a bit more involved:
    - we successively revert all assumptions about this candidate into the conclusion
    - we use the OCaml tactic [apply_ptower] in order to reify the goal, apply [reification.ptower] with appropriate arguments, and get rid of the reified operations 
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
    - that the game is symmetric is inferred using the typeclasse [Symmetrical]
    - that the goal is symmetric is proven using the given tactic (by default, [firstorder])
    the goal should be of the form
    [forall x y..., b `R u v] 
    it moves to a goal of the form
    [forall x y..., s `R u v] 
    (where [R: Chain b] with [b] the function for the coinductive game, and [s] the function for the `half of [b]')
    conjunctions are also allowed, like in the other tactics)
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

(** performing a single step 
    (equivalent to [accumulate _], except that we do not deal with composite candidates and the coinductive proof need not be started) *)
Ltac step :=
match goal with
| |- context [gfp ?b] => apply (pfp_gfp b)
| |- context [elem ?R] => apply (b_chain R)
end.

Ltac step_in h :=
match type of h with
| context [gfp ?b] => apply (gfp_pfp b) in h
end.

Tactic Notation "step" "in" ident(h) := step_in h.

Ltac unstep :=
match goal with
| |- context [gfp ?b] => apply (gfp_pfp b)
end.

Ltac unstep_in h :=
match type of h with
| context [gfp ?b] => apply (pfp_gfp b) in h
end.

Tactic Notation "unstep" "in" ident(h) := unstep_in h.
