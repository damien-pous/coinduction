
(** * tests for the boxing elpi tactic *)

Require Import lattice tower.
From elpi Require Import elpi.
From Coinduction Extra Dependency "box_gfp.elpi" as box_gfp.

Definition box_gfp {T} (x: T) := x.
Lemma gfp_prop {X} {L : CompleteLattice X} [b : mon X] (P : X -> Prop):
  (forall x : Chain b, P (elem x)) -> P (box_gfp (gfp b)).
Proof. exact (gfp_prop P). Qed.

Elpi Tactic box_gfp.
Elpi Accumulate File box_gfp.

Section s.  
  Variable b : mon (nat -> nat -> Prop).  
  Let sim := gfp b.

  Goal sim 2 3.
  Proof.
    unfold sim. elpi box_gfp.
    Restart.
    unfold sim. elpi box_gfp 42. (* magic arity for testing alternative elpi code *)
    Restart.
    elpi box_gfp 2.
    Restart.
    Fail elpi box_gfp 3.        (* duly failing (wrong arity) *)
    Restart.
    elpi box_gfp (sim).
    (* Restart. *)
    (* elpi box_gfp. *)
    apply gfp_prop. 
  Abort.

  Goal sim 1 2 -> sim 2 3.
  Proof.
    elpi box_gfp (sim). 
    apply gfp_prop. 
  Abort.

  Goal forall n, sim n n.
  Proof.
    elpi box_gfp (sim). 
    apply gfp_prop.
    Restart.
    Fail elpi box_gfp.          (* duly failing *)
  Abort.
    
  Goal forall n, sim n 2 -> sim n 4 /\ forall m, sim 2 m.
  Proof.
    elpi box_gfp (sim). 
    apply gfp_prop. 
  Abort.

  Goal forall n, sim n 2 -> sim n 4 /\ forall m, gfp b 2 m.
  Proof.
    elpi box_gfp.
    Restart.
    elpi box_gfp (sim).
    Restart. 
    elpi box_gfp 2.
  Abort.

  Goal forall n, sim n 2 -> gfp b n 4 /\ forall m, sim 2 m.
  Proof.
    elpi box_gfp.
    Restart.
    elpi box_gfp (sim).
    Restart. 
    elpi box_gfp 2.
  Abort.
End s.


Section s.  
  Variables b c : mon (nat -> nat -> Prop).
  Goal gfp b 2 3 /\ gfp c 3 4.
  Proof.
    Fail elpi box_gfp.          (* duly failing: two gfps *)
  Abort.
End s.
    
Section s.  
  Variable b : mon (nat -> Prop).  
  Let sim := gfp b.

  Goal sim 2.
  Proof.
    elpi box_gfp (sim). 
    apply gfp_prop. 
  Abort.

  Goal sim 1 -> sim 2.
  Proof.
    elpi box_gfp (sim). 
    apply gfp_prop. 
  Abort.

  Goal forall n, sim n.
  Proof.
    elpi box_gfp (sim). 
    apply gfp_prop. 
  Abort.
    
  Goal forall n, sim n -> sim 4 /\ forall m, sim m.
  Proof.
    elpi box_gfp (sim). 
    apply gfp_prop. 
  Abort.
End s.

Section s.
  Variable W: Type -> Type.
  Variable b : forall X, mon (W X -> Prop).  
  Let sim X := gfp (b X).
  Variable X: Type.
  
  Goal forall w: W X, sim _ w -> sim _ w.
  Proof.    
    elpi box_gfp (@sim).        (* could/should actually fail *)
    Fail apply gfp_prop.
    Restart.
    elpi box_gfp (sim X).
    apply gfp_prop. 
    Restart.
    elpi box_gfp (sim _).
    apply gfp_prop. 
    Restart.
    elpi box_gfp 1.
    apply gfp_prop. 
  Abort.
End s.

Section s.
  Variable W: Type -> Type.
  Variable b : forall X, mon (W X -> Prop).  
  Let sim {X} := gfp (b X).
  Variable X: Type.
  
  Goal forall w: W X, sim w -> sim w.
  Proof.    
    elpi box_gfp (sim).
    apply gfp_prop. 
    Restart.
    elpi box_gfp (@sim _).
    apply gfp_prop. 
    Restart.
    elpi box_gfp 1.
    apply gfp_prop. 
  Abort.
End s.
