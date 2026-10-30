
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
    elpi box_gfp (sim).
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
  Abort.
    
  Goal forall n, sim n 2 -> sim n 4 /\ forall m, sim 2 m.
  Proof.
    elpi box_gfp (sim). 
    apply gfp_prop. 
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
    Fail elpi box_gfp (@sim). 
    elpi box_gfp (sim X).
    apply gfp_prop. 
    Restart.
    elpi box_gfp (sim _).
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
    Fail elpi box_gfp (@sim). 
    Fail elpi box_gfp sim.
    elpi box_gfp (@sim _).
    apply gfp_prop. 
  Abort.
End s.
