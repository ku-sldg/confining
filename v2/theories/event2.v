Require Import Relations. 
Require Import Coq.Classes.RelationClasses.

Print LoadPath.
(* Add LoadPath "/Users/annarosefritz/Documents/EECS_research/GitHubRepos/confining/v2" as MS. *)

From v2 Require Import MS.

(* Definition 2: Events. There are 3 labels for event. Measurement event (ms), adversary events (corruption (cor) and repair (rep)) and an attestation start event (att_start) *)

Inductive event :=
| ms : object -> object -> event
| cor : object -> event
| rep : object -> event 
| att_start : event.  

(* event e touches o iff o is argument to e. *)
Inductive touches : object -> event -> Prop :=
| touch_ms1: forall o1 o2, touches o2 (ms o1 o2)
| touch_ms2 : forall o1 o2, touches o1 (ms o1 o2)
| touch_cor: forall o, touches o (cor o)  
| touch_rep: forall o, touches o (rep o)
| touch_start : forall o, touches o (att_start).

(* Definition touches' : forall o o', touches o' o iff M1 (o',o). *)

Check touches o1 (ms o1 o2) .
Theorem touches' : touches  o2 (ms o1 o2).
Proof.
    constructor.
Qed.

Theorem touches2' : touches  o1 (ms o1 o2).
Proof.
    constructor.
Qed.
 
(* What do we want the event system to accomplish? *)
Inductive E1 : event -> event -> Prop :=
(* attestation start can be followed by any event *)
| e_ms_start : forall e,  e <> att_start -> E1 (att_start) (e)
(* the second event needs to touch o *)
| e_rtm_o : forall e o, e <> att_start -> touches o e -> E1 (ms rtm o) e
(* again, the second event needs to touch the first *)
| e_ms_o : forall e o o', e <> att_start -> touches o e -> E1 (ms o' o) e
(* this event catches the corruption and repair events *)
| e_o_o : forall e e', E1 e e'.

Check E1 (att_start) (ms rtm o1).
Definition e1' : E1 (att_start) (ms rtm o1).
Proof. constructor. discriminate. Qed. 

Definition e1'' : E1 (ms rtm o1) (ms o1 o2).
Proof. constructor. discriminate. constructor. Qed.  


(* As Perry has mentioned, we need the TRC to 
have more than just a sigle step of events. *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z, R x y -> trc R y z -> trc R x z.

(* May need to prove transitivity later on... I'm not sure. *)
Theorem trc_trans : forall {A} (R : A -> A -> Prop) x y, 
    trc R x y -> forall z, trc R y z -> trc R x z.
Proof.  
(* the key to this proof is induction on the hypothesis *)
intros A R x y. intros H1 z H2. induction H1.
+ apply H2.
+ eapply TrcFront. apply H. apply IHtrc. apply H2.
Qed. 

(* Transitive-reflexive closure is so common that it deserves a shorthand notation! *)
Set Warnings "-notation-overridden". (* <-- needed while we play with defining one
* of the book's notations ourselves locally *)
Notation "R ^*" := (trc R) (at level 0).

(* (ms o1 o2) is in the transitive reflexive closure of the start event. 
This is must easier to prove then the former with E1 because E1' is more general. *)
Example measure_o2' : E1^* (att_start) (ms o1 o2).
Proof.
    eapply TrcFront; constructor. discriminate.
Qed.

Class PartialOrder' {A} (R: relation A) := {
    refl :> Reflexive R ; 
    anti_sym :> Antisymmetric _ eq R ;
    trans :> Transitive R 
}.

Theorem att' : att_start <> att_start .
Proof. Abort. 

Instance E : PartialOrder' E1.
Proof.
    constructor.
    + unfold Reflexive. intros. induction x; try constructor.
    ++ discriminate.
    ++ constructor.
    ++ unfold not. Abort.
    
Instance E' : PartialOrder' E1^*.
Proof.
    constructor. 
    + unfold Reflexive. apply TrcRefl.
    + unfold Antisymmetric. intros x y H. induction H.
    ++ intros. reflexivity.
    ++ Abort.
    
Axiom E'' : PartialOrder' E1.
Axiom E_trans : Transitive E1.

Definition E_o := forall o : object, {e : event | touches o e}.

Definition e1 := (att_start).
Definition e2 := (ms rtm o1). 

Check E''.
Check (E_trans e1 e2). 
(* every event that happened before e *)
Definition E_down := forall e e',  {e | (E_trans e e') }.

(* the minimum may be rtm ... nothing comes before the rtm measurement *)

(* what are the properties of a semi lattice?

rtm properties 
- talk about it's touches relation? 
- properties about the bottom *)

(* every event that happened after e *)
