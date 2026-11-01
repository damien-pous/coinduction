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

(** in this file the tactics are defined using elpi,
    see [ocaml_tactics.v] for the former version, with a dedicated ocaml plugin *)

Require Import lattice tower rel reification.
From elpi Require Import elpi.
From Coinduction Extra Dependency "coinduction.elpi" as coinduction.
Import CoindNotations.
Set Implicit Arguments.

(* Elpi Debug "DEBUG_COINDUCTION". *)
Elpi Tactic coinduction.
Elpi Accumulate File coinduction.

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

Tactic Notation "coinduction" ident(R) simple_intropattern(H) :=
  elpi coinduction start; intros R H.

(* Section test.   *)
(*   Variables b c : mon (nat -> nat -> Prop).   *)
(*   Goal gfp b 2 3. *)
(*   Proof. *)
(*     coinduction R H. *)
(*   Abort. *)
(* End test. *)

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
Ltac xaccumulate R n :=
  lazymatch goal with
  | H: context[R] |- _ => revert H; xaccumulate R (S n); intro H
  | _ => elpi coinduction accumulate (R) (n); clear R; intro R
  end.

Tactic Notation "accumulate" hyp(R) simple_intropattern(H) :=
  xaccumulate R O; intros H.

Tactic Notation "accumulate" simple_intropattern(H) :=
  lazymatch goal with
  | R: Chain _ |- _ => accumulate R H
  | _ => fail "could not find the coinductive candidate"
  end.


(* Section test.   *)
(*   Variables b : mon (nat -> nat -> Prop).   *)
(*   Goal gfp b 2 3. *)
(*   Proof. *)
(*     coinduction R H. *)
(*     cut (`R 4 5). admit. *)
(*     accumulate H'.  *)
(*     cut (`R 5 6). admit. *)
(*     accumulate H''.  *)
(*   Abort. *)
(* End test. *)



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
Ltac default_sym_tac := solve[clear;firstorder] || fail "could not get symmetry automatically".
Tactic Notation "symmetric" hyp(R) "using" tactic(tac) :=
  (elpi coinduction symmetry (R)); [simpl reification.pT; tac|].
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

(* Section test. *)
(*   Variables s: mon (nat -> nat -> Prop). *)
(*   Abbreviation b := (cap s (converse ° s ° converse)). *)
(*   Goal forall n m, gfp b n m. *)
(*   Proof. *)
(*     coinduction R H. *)
(*     symmetric.  *)
(*   Abort.   *)
(* End test. *)
