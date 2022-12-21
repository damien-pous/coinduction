(** * Basic theory of complete lattices  *)

Require Export Setoid Morphisms.
Set Implicit Arguments.

(** * Class of complete lattices 
    we require all operations rather than deriving them from least upper bounds: 
    this way we can map them to the natural operations in the various instances *)

Class CompleteLattice (X: Type) := {
  weq: relation X;
  leq: relation X;
  sup: (X -> Prop) -> X;
  inf: (X -> Prop) -> X;
  cup: X -> X -> X;
  cap: X -> X -> X;
  bot: X;
  top: X;
  PreOrder_leq:> PreOrder leq;
  weq_spec: forall x y, weq x y <-> (leq x y /\ leq y x);
  sup_spec: forall P z, leq (sup P) z <-> forall x, P x -> leq x z;
  inf_spec: forall P z, leq z (inf P) <-> forall x, P x -> leq z x;
  cup_spec: forall x y z, leq (cup x y) z <-> (leq x z /\ leq y z);
  cap_spec: forall x y z, leq z (cap x y) <-> (leq z x /\ leq z y);
  leq_bx: forall x, leq bot x;
  leq_xt: forall x, leq x top
                                  }.
Declare Scope lattice.
Open Scope lattice.
Infix "==" := weq (at level 70): lattice.
Infix "<=" := leq: lattice.
Global Hint Extern 0 => reflexivity: core.
Global Hint Resolve leq_bx leq_xt: core.
 

(** * Concrete instances *)

(** Prop is a complete lattice *)
#[export] Program Instance CompleteLattice_Prop: CompleteLattice Prop :=
  {| weq:=iff;
     leq:=Basics.impl;
     sup P:=exists2 p, P p & p;
     inf P:=forall p, P p -> p;
     cup:=or;
     cap:=and;
     bot:=False;
     top:=True |}.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

(** Dependent functions into complete lattices *)
Definition dpointwise_relation A (X: A -> Type) (R: forall {a}, relation (X a)): relation (forall a, X a)
  := fun f g => forall a, R (f a) (g a). 
Arguments dpointwise_relation [_] {_} _ /.

Definition image {A B} (f: A -> B) (P: A -> Prop): B -> Prop :=
  fun b => exists2 a, P a & b = f a.
Lemma in_image {A B} (f: A -> B) (P: A -> Prop) a: P a -> image f P (f a).
Proof. now exists a. Qed.
Lemma forall_image {A B} (f: A -> B) (P: A -> Prop) (Q: B -> Prop):
  (forall b, image f P b -> Q b) <-> forall a, P a -> Q (f a).
Proof. cbv; firstorder (subst; eauto). Qed.

Program Definition CompleteLattice_dfun A (X: A -> Type) (L: forall a, CompleteLattice (X a)): CompleteLattice (forall a, X a) :=
  {| weq := dpointwise_relation (fun _ => weq);
     leq := dpointwise_relation (fun _ => leq);
     sup P a := sup (image (fun f => f a) P);
     inf P a := inf (image (fun f => f a) P);
     cup f g a := cup (f a) (g a);
     cap f g a := cap (f a) (g a);
     bot a := bot;
     top a := top
  |}.
Next Obligation. 
  constructor.
   now intros f x. 
   intros f g h H H' x. now transitivity (g x).
Qed.
Next Obligation. setoid_rewrite weq_spec. firstorder. Qed.
Next Obligation. setoid_rewrite sup_spec. setoid_rewrite forall_image. firstorder. Qed.
Next Obligation. setoid_rewrite inf_spec. setoid_rewrite forall_image. firstorder. Qed.
Next Obligation. setoid_rewrite cup_spec. firstorder. Qed.
Next Obligation. setoid_rewrite cap_spec. firstorder. Qed.

(** Functions into a complete lattice *)
#[export] Instance CompleteLattice_fun {A X} {L: CompleteLattice X}: CompleteLattice (A -> X) :=
  CompleteLattice_dfun (fun _ => X) (fun _ => L). 

(** Dual lattice *)
Program Definition Dual {X} {L: CompleteLattice X}: CompleteLattice X :=
  {| weq:=weq;
     leq x y :=leq y x;
     sup:=inf;
     inf:=sup;
     cup:=cap;
     cap:=cup;
     bot:=top;
     top:=bot
  |}.
Next Obligation. split. now intro. intros ? x ???. now transitivity x. Qed.
Next Obligation. rewrite weq_spec. tauto. Qed.
Next Obligation. apply inf_spec. Qed.
Next Obligation. apply sup_spec. Qed.
Next Obligation. apply cap_spec. Qed.
Next Obligation. apply cup_spec. Qed.

(** * Utilities  *)

(** tactics to solve goals by duality *)
Ltac dual t := apply (t _ (Dual)).


(** any monotone function preserves equality  *)
Lemma op_leq_weq_1 {X Y} {LX: CompleteLattice X} {LY: CompleteLattice Y} {f: X -> Y} 
  {Hf: Proper (leq ==> leq) f}: Proper (weq ==> weq) f.
Proof. intros x y. rewrite 2weq_spec. intro E; split; apply Hf; apply E. Qed.

Lemma op_leq_weq_2 {X Y Z} {LX: CompleteLattice X} {LY: CompleteLattice Y} {LZ: CompleteLattice Z} {f: X -> Y -> Z}
  {Hf: Proper (leq ==> leq ==> leq) f}: Proper (weq ==> weq ==> weq) f.
Proof. 
  intros x y E x' y' E'. rewrite weq_spec in E. rewrite weq_spec in E'.
  apply weq_spec. split; apply Hf; (apply E || apply E').
Qed.

#[export] Instance image_leq {A B} {f: A -> B}: Proper (leq ==> leq) (image f).
Proof. intros P Q PQ b [? ? ?]. eexists; eauto. now apply PQ. Qed.
#[export] Instance image_weq {A B} {f: A -> B}: Proper (weq ==> weq) (image f) := op_leq_weq_1.
Lemma image_id {A} (P: A -> Prop): image id P == P. 
Proof. firstorder (subst; eauto). Qed.
Lemma image_comp {A B C} (f: A -> B) (g: B -> C) (P: A -> Prop): image (fun x => g (f x)) P == image g (image f P).
Proof. firstorder (subst; eauto). Qed.

(** * General properties of complete lattices *)

Section sup.
 Context {X} {L: CompleteLattice X}.

 (** Partial order *)
 Global Instance Equivalence_weq: Equivalence weq.
 Proof.
   constructor.
    intro x. now apply weq_spec.
    intros x y. rewrite 2weq_spec. tauto.
    intros x y z. rewrite 3weq_spec. split; transitivity y; tauto. 
  Qed.
 Global Instance PartialOrder_weq_leq: PartialOrder weq leq.
 Proof.
   intros x y. simpl. now rewrite weq_spec.
 Qed.
 Lemma antisym x y: x <= y -> y <= x -> x == y.
 Proof. rewrite weq_spec. tauto. Qed.

 Lemma antisym' x y: x <= y -> (x <= y -> y <= x) -> x == y.
 Proof. intros. apply antisym; tauto. Qed.
 
 Lemma from_above x y: (forall z, x<=z <-> y<=z) -> x==y.
 Proof. intro E. apply antisym; apply E; reflexivity. Qed.

 Lemma from_below x y: (forall z, z<=x <-> z<=y) -> x==y.
 Proof. intro E. apply antisym; apply E; reflexivity. Qed.

 
 (** Least upper bounds *)
 Global Instance sup_leq:
   Proper (leq ==> leq) sup.
 Proof.
   intros P P' HP. apply sup_spec. 
   intro x. rewrite (HP x). now apply sup_spec.
 Qed.
 Global Instance sup_weq: Proper (weq ==> weq) sup := op_leq_weq_1.
 
 Lemma leq_xsup (P: X -> Prop) x: P x -> x <= sup P.
 Proof. now apply sup_spec. Qed.

 Lemma eleq_xsup (P: X -> Prop) y x: P y -> x <= y -> x <= sup P.
 Proof. intros ? H. rewrite H. now apply leq_xsup. Qed.

 Lemma sup_bot: sup bot == bot.
 Proof. apply antisym. now apply sup_spec. apply leq_bx. Qed.
 Lemma sup_single x: sup (eq x) == x.
 Proof. apply antisym. apply sup_spec. now intros ? <-. now apply leq_xsup. Qed.
 Lemma sup_top: sup top == top.
 Proof. apply antisym. apply leq_xt. now apply leq_xsup. Qed.
 
 
 (** Binary join *)
 Lemma leq_xcup x y z: z <= x \/ z <= y -> z <= cup x y.
 Proof.
   destruct (cup_spec x y (cup x y)) as [H _].
   now intros [E|E]; rewrite E; apply H.
 Qed.
 Lemma cup_l x y: x <= cup x y.
 Proof. auto using leq_xcup. Qed.
 Lemma cup_r x y: y <= cup x y.
 Proof. auto using leq_xcup. Qed.

 Lemma cupA x y z: cup x (cup y z) == cup (cup x y) z.
 Proof. apply from_above. intro. rewrite 4cup_spec. tauto. Qed.
 Lemma cupC x y: cup x y == cup y x.
 Proof. apply from_above. intro. rewrite 2cup_spec. tauto. Qed.
 Lemma cupI x: cup x x == x.
 Proof. apply from_above. intro. rewrite cup_spec. tauto. Qed.
 Lemma cupbx x: cup bot x == x.
 Proof. apply antisym. apply cup_spec. now split. apply cup_r. Qed.
 Lemma cupxb x: cup x bot == x.
 Proof. rewrite cupC. apply cupbx. Qed.
 Lemma cuptx x: cup top x == top.
 Proof. apply antisym. apply leq_xt. apply cup_l. Qed.
 Lemma cupxt x: cup x top == top.
 Proof. rewrite cupC. apply cuptx. Qed.
 
 Global Instance cup_leq: Proper (leq ==> leq ==> leq) cup.
 Proof.
   intros x x' Hx y y' Hy.
   apply cup_spec. rewrite Hx, Hy.
   now apply cup_spec.
 Qed.
 Global Instance cup_weq: Proper (weq ==> weq ==> weq) cup := op_leq_weq_2.
 
End sup.
Global Hint Resolve cup_l cup_r: core.

Section sup_cup.
 Context {X} {L: CompleteLattice X}.
 Lemma sup_cup P Q: sup (cup P Q) == cup (sup P) (sup Q).
 Proof.
   apply antisym. apply sup_spec. intros i [H|H]; apply leq_xcup.
   now left; apply leq_xsup. 
   now right; apply leq_xsup.
   apply cup_spec. now split; apply sup_leq. 
 Qed.
End sup_cup. 


(** * Properties obtained by duality *)
Section inf.
 Context {X} {L: CompleteLattice X}.

 (** Greatest lower bounds *)
 Global Instance inf_leq: Proper (leq --> leq) inf.
 Proof. intros ???. now dual @sup_leq. Qed.
 Global Instance inf_weq: Proper (weq ==> weq) inf.
 Proof. apply (@sup_weq _ (@Dual _ L)). Qed.
 
 Lemma leq_infx (P: X -> Prop) x: P x -> inf P <= x.
 Proof. dual @leq_xsup. Qed.
 Lemma eleq_infx (P: X -> Prop) y x: P y -> y <= x -> inf P <= x.
 Proof. dual @eleq_xsup. Qed.

 Lemma inf_bot: inf bot == top.
 Proof. dual @sup_bot. Qed.
 Lemma inf_single x: inf (eq x) == x.
 Proof. dual @sup_single. Qed.
 Lemma inf_cup P Q: inf (cup P Q) == cap (inf P) (inf Q).
 Proof. dual @sup_cup. Qed.
 Lemma inf_top: inf top == bot.
 Proof. dual @sup_top. Qed.

 (** Binary meet *)
 Lemma leq_capx x y z: x <= z \/ y <= z -> cap x y <= z.
 Proof. dual @leq_xcup. Qed.
 Lemma cap_l x y: cap x y <= x.
 Proof. dual @cup_l. Qed.
 Lemma cap_r x y: cap x y <= y.
 Proof. dual @cup_r. Qed.
 
 Lemma capA x y z: cap x (cap y z) == cap (cap x y) z.
 Proof. dual @cupA. Qed.
 Lemma capC x y: cap x y == cap y x.
 Proof. dual @cupC. Qed.
 Lemma capI x: cap x x == x.
 Proof. dual @cupI. Qed.
 Lemma captx x: cap top x == x.
 Proof. dual @cupbx. Qed.
 Lemma capxt x: cap x top == x.
 Proof. dual @cupxb. Qed.
 Lemma capbx x: cap bot x == bot.
 Proof. dual @cuptx. Qed.
 Lemma capxb x: cap x bot == bot.
 Proof. dual @cupxt. Qed.

 Global Instance cap_leq: Proper (leq ==> leq ==> leq) cap.
 Proof. intros ??????. now dual @cup_leq. Qed.
 Global Instance cap_weq: Proper (weq ==> weq ==> weq) cap := op_leq_weq_2.

End inf.
Global Hint Resolve cap_l cap_r: core.

(** * The complete lattice of monotone endofunctions *)

Section mon. 
 Context {X} {L: CompleteLattice X}.
 
 (** monotone endofunctions *)
 Record mon := { body:> X -> X; Hbody: Proper (leq ==> leq) body }.
 
 (** the following instances are not global: more powerful ones are 
    given at the end of the section *)
 Existing Instance Hbody.
 Instance Hbody' (f: mon): Proper (weq ==> weq) f.
 Proof. intros x y. rewrite 2weq_spec. now split; apply f. Qed.

 (** constant function *)
 Program Definition const x: mon := {| body y := x |}.
 Next Obligation. intros ? ? ?. reflexivity. Qed.

 (** identity and composition
     the monotonicity proofs are transparent to get strong equalities
     - [id ° f = f ° id = f], and
     - [f ° (g ° h) = (f ° g) ° h]
  *)
 Definition id: mon := {| 
   body x := x; 
   Hbody x y H := H 
 |}.

 Definition comp (f g: mon): mon := {|
   body := fun x => f (g x); 
   Hbody x y H := Hbody f _ _ (Hbody g _ _ H) 
 |}.
 Infix "°" := comp (at level 20): lattice.
 
 (** monotone endofunctions form a new complete lattice *)
 Global Program Instance CompleteLattice_mon: CompleteLattice mon := {|
   weq := pointwise_relation X weq;
   leq := pointwise_relation X leq;
   sup P := {| body := fun x => sup (image (fun f: mon => f x) P) |};
   inf P := {| body := fun x => inf (image (fun f: mon => f x) P) |};
   cup f g := {| body := fun x => cup (f x) (g x) |};
   cap f g := {| body := fun x => cap (f x) (g x) |};
   bot := const bot;
   top := const top
 |}.
 Next Obligation.
   intros x y H. apply sup_spec. apply forall_image. intros f Pf.
   rewrite H. apply leq_xsup. now exists f. 
 Qed.
 Next Obligation.
   intros x y H. apply inf_spec. apply forall_image. intros f Pf.
   rewrite <-H. apply leq_infx. now exists f. 
 Qed.
 Next Obligation. intros x y H. now rewrite H. Qed.
 Next Obligation. intros x y H. now rewrite H. Qed.
 Next Obligation. constructor. now intros f x. intros f g h H H' x. now transitivity (g x). Qed.
 Next Obligation. unfold pointwise_relation. setoid_rewrite weq_spec. firstorder. Qed.
 Next Obligation.
   unfold pointwise_relation. setoid_rewrite sup_spec.
   setoid_rewrite forall_image. firstorder.
 Qed.
 Next Obligation.
   unfold pointwise_relation. setoid_rewrite inf_spec.
   setoid_rewrite forall_image. firstorder.
 Qed.
 Next Obligation. unfold pointwise_relation. setoid_rewrite cup_spec. firstorder. Qed.
 Next Obligation. unfold pointwise_relation. setoid_rewrite cap_spec. firstorder. Qed.
 Next Obligation. intro. apply leq_bx. Qed.
 Next Obligation. intro. apply leq_xt. Qed.

 Global Instance comp_leq: Proper (leq ==> leq ==> leq) comp.
 Proof. intros f f' Hf g g' Hg x. simpl. rewrite (Hg x). apply Hf. Qed.
 Global Instance comp_weq: Proper (weq ==> weq ==> weq) comp := op_leq_weq_2.

 (** trivial properties of composition *)
 Lemma compA f g h: f ° (g ° h) = (f ° g) ° h.
 Proof. reflexivity. Qed.
 Lemma compIx f: id ° f = f.
 Proof. now case f. Qed. 
 Lemma compxI f: f ° id = f.
 Proof. now case f. Qed. 

 (** monotone functions applied to infs/sups *)
 Lemma mon_sup (f: mon) P: sup (image f P) <= f (sup P).
 Proof. apply sup_spec. apply forall_image. intros. apply f. now apply leq_xsup. Qed.
 Lemma mon_cup (f: mon) x y: cup (f x) (f y) <= f (cup x y).
 Proof. apply cup_spec; split; apply f; auto. Qed.
 Lemma mon_inf (f: mon) P: f (inf P) <= inf (image f P).
 Proof. apply inf_spec. apply forall_image. intros. apply f. now apply leq_infx. Qed.
 Lemma mon_cap (f: mon) x y: f (cap x y) <= cap (f x) (f y).
 Proof. apply cap_spec; split; apply f; auto. Qed.

 (** operations on [mon X] behave as expected on the left of compositions *)
 Lemma mcup_o f g h: (cup f g) ° h == cup (f ° h) (g ° h).
 Proof. now intro. Qed.
 Lemma mbot_o f: bot ° f == bot.
 Proof. now intro. Qed.
 Lemma mcap_o f g h: (cap f g) ° h == cap (f ° h) (g ° h).
 Proof. now intro. Qed. 
 Lemma mtop_o f: top ° f == top.
 Proof. now intro. Qed.

 (** instead, only one inclusion holds in general when they are on the left *)
 Lemma o_msup (P: mon -> Prop) (h: mon): sup (image (fun f => h ° f) P) <= h ° sup P.
 Proof. intro. setoid_rewrite <-mon_sup. apply sup_leq. now rewrite <-2image_comp. Qed.
 Lemma o_mcup h f g: cup (h ° f) (h ° g) <= h ° (cup f g).
 Proof. intro. apply (mon_cup h). Qed.
 Lemma o_minf (P: mon -> Prop) (h: mon): h ° inf P <= inf (image (fun f => h ° f) P).
 Proof. intro. setoid_rewrite mon_inf. apply inf_leq. now rewrite <-2image_comp. Qed.
 Lemma o_mcap h f g: h ° (cap f g) <= cap (h ° f) (h ° g).
 Proof. intro. apply (mon_cap h). Qed.

End mon.
Arguments mon X {L}.
Infix "°" := comp (at level 20): lattice.
Global Opaque cup bot cap top.  (* TODO: check that we still need this *)

(** application as a function [X->X]->X->X is monotone in its two arguments *)
#[export] Instance app_leq {X} {L: CompleteLattice X}: Proper (leq ==> leq ==> leq) body.
Proof. intros f g fg x y xy. transitivity (f y). now apply f. now apply fg. Qed.
#[export] Instance app_weq {X} {L: CompleteLattice X}: Proper (weq ==> weq ==> weq) body := op_leq_weq_2.
