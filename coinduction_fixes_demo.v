(** * Fixes to the elpi tactics of rocq-coinduction: demo

    This patch is based on master at 07d2a09. The patch fixes three problems:

    1. a seeming elpi bug (https://github.com/LPCIC/coq-elpi/issues/1136) led to
       a section hypothesis shadowed by [specialize] coming back at its general
       type in the goals created by [coinduction], [accumulate] and [symmetric],
       leading to an ill-typed proof term rejected at [Qed] (Part 1);
    2. [symmetric] lost the user's bound names in the symmetry requirement it
       produces, which is the point of the complexity of the plugin (Part 2);
    3. that symmetry requirement also quantified over a candidate of reified
       type [reification.REL' (reification.ABS ...) Prop], which is an
       unbeautiful goal (Part 2).

    Each proof's comments show what the master branch currently does, while the
    actual code is with master + this patch.

    To compile from a tree with the patch applied: rocq compile -R
      <tree>/theories Coinduction -I <tree>/src coinduction_fixes_demo.v
 *)

From Coinduction Require Import all.
Import CoindNotations.

(** ** Part 1: section hypotheses shadowed by [specialize]

    [specialize (HP 0)] on a section hypothesis [HP] hides it, and introduces a
    local hypothesis with the same name [HP : 0 = 0].

    On master, the elpi tactics ([coinduction], [accumulate], [symmetric])
    create their new goals with elpi's [refine], which rebuilds the goal
    context. In that rebuilt context, the name [HP] points back to the *section*
    hypothesis. The tactic engine thus lets us use [HP] with its original,
    general type, while the proof term still refers to the local [HP : 0 = 0].
    The proof term is ill-typed, which is only detected by the kernel at [Qed].
    This is documented here: https://github.com/LPCIC/coq-elpi/issues/1136

    (This was found in [interp_pi_eqit_secure_state] in itrees'
    extra/Secure/SecureStateHandlerPi.v. Currently it uses a [pose proof]
    workaround, which is fine but this should be fixed for now IMO.)

    Fix: the elpi code only computes the arguments of the reification lemmas
    while small Ltac wrappers actually apply them, so the new goals are created
    by Ltac's [refine] in the actual Rocq context of the goal. *)

Section shadowing.

  Variable b : mon (nat -> Prop).
  Hypothesis HP : forall n : nat, n = n.
  Hypothesis Hb : forall (R : Chain b) n, b `R n.

  (** [accumulate] *)
  Lemma accumulate_keeps_specialized : forall R : Chain b, `R 0.
  Proof.
    intro R. specialize (HP 0).
    (* HP : 0 = 0 *)
    accumulate H.
    Check HP.
    (* master:  HP : forall n : nat, n = n     <- the section hypothesis is back
       now:     HP : 0 = 0 *)
    Fail pose proof (HP 1) as H1.
    (* master:  accepted; the proof then fails at Qed, with
                  Error: Illegal application (Non-functional construction):
                  The expression "HP0" of type "0 = 0"
                  cannot be applied to the term "1" : "nat"
       now:     rejected right away (HP has type 0 = 0):
                  Error: Illegal application (Non-functional construction):
                  The expression "HP" of type "0 = 0"
                  cannot be applied to the term "1" : "nat" *)
    apply Hb.
  Qed.

  (** [coinduction] had the same problem *)
  Lemma coinduction_keeps_specialized : forall n, gfp b n.
  Proof.
    specialize (HP 0).
    coinduction R H.
    Check HP.
    (* master:  HP : forall n : nat, n = n
       now:     HP : 0 = 0 *)
    Fail pose proof (HP 1) as H1.
    (* master:  accepted, so Qed fails with the same kernel error as above *)
    intro n. apply Hb.
  Qed.

End shadowing.


(** ** Part 2: the symmetry requirement produced by [symmetric]

    [symmetric] applies [reification.by_symmetry], which produces two goals. On
    master, goal 1 was the raw reified statement [forall R, pT R x -> pT R
    (converse_fT x)]. After [simpl reification.pT], all the bound variables were
    then named after [reification.pT]'s internal binder ([b], [b0], [b1], ...),
    and anonymous hypotheses as well. Proofs written against the old names
    (e.g., with the OCaml version of the tactics, which keeps them) thus broke.

    (This was found in ctrees, theories/Eq/WBisim.v (two proofs) and
    examples/Yield/Par.v, which needed explicit [intros] names.)

    Also, the candidate [R0] quantified in goal 1 had the reified type
    [reification.REL' (reification.ABS nat (fun _ => ...)) Prop], on master as
    well as with the OCaml version of the tactics, which is less pretty than the
    standard unfolding which gets "real" Rocq back.

    Fix: an extra elpi step restates goal 1 using the names of the original
    goal, as the OCaml version of [symmetric] does, and gives [R0] the plain
    relation type ([nat -> nat -> Prop] below) by unfolding just
    [reification.REL']. *)

Section symmetric_names.

  Variable s : mon (nat -> nat -> Prop).
  Abbreviation b := (cap s (converse ° s ° converse)).

  Goal forall n m, n = m -> gfp b n m.
  Proof.
    coinduction R H.
    symmetric using idtac.
    (* goal 1, master:
         forall
           R0 : reification.REL'
                  (reification.ABS nat
                     (fun _ : nat =>
                      reification.ABS nat (fun _ : nat => reification.PRP)))
                  Prop,
         (forall b b0 : nat, b = b0 -> R0 b b0) ->
         forall b b0 : nat, b = b0 -> R0 b0 b
       goal 1, now:
         forall R0 : nat -> nat -> Prop,
         (forall n m : nat, n = m -> R0 n m) -> forall n m : nat, n = m -> R0 m n
       goal 2 (unchanged):
         forall n m : nat, n = m -> s `R n m *)
    { intros.
      (* master:  H0 : forall b b0 : nat, b = b0 -> R0 b b0
                  b, b0 : nat
                  b1 : b = b0
                  (and the context now displays [R : Chain sym.b], since [b]
                   is also the name of the coinductive function)
         now:     H0 : forall n m : nat, n = m -> R0 n m
                  n, m : nat
                  H1 : n = m
         and [R0 : reification.REL' (...) Prop] (master) vs
             [R0 : nat -> nat -> Prop] (now) *)
      lazymatch type of R0 with nat -> nat -> Prop => idtac end.
      (* master:  fails, the type of [R0] is [reification.REL' (...) Prop] *)
      apply (H0 m n).
      (* master:  Error: The variable m was not found in the current environment. *)
      symmetry. exact H1.
      (* master:  [H1] does not exist either: the hypothesis is called [b1] *)
    }
  Abort.

End symmetric_names.
