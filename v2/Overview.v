(******************************
Proofs and definitions adapted from 
"Confining Adversary Actions via Measurements" by Paul Rowe
******************************)

Require Import Relations. 
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.

(* Our work starts when Rowe introduces the measurement system *)
(* Definition 1 is a measurement system (MS). 

    MS = (O, M, C)
        - O is set of object, M is the measures relation, C is the context relation 
        - M & C are binary relations on O 
*)

(* This is our set of objects. Objects are the things we measure.  *)
Inductive object : Type :=
| rtm : object
| o1 : object 
| o2 : object
| o3 : object. 

(* This is the measurement relation. It describes what objects are measured by who. *)
Inductive M1 : object -> object -> Prop := 
| rtm_o : M1 rtm o1
| o1_o2 : M1 o1 o2
| o2_o3 : M1 o2 o3. 

(* for the time being, we forgot about the context relation*)

(* After defining the measurement system, Rowe continues by defining he event system.

(* Definition 2: Events. There are 3 labels for event. Measurement event (ms), adversary events (corruption (cor) and repair (rep)) and an attestation start event (att_start)*) *)
Inductive event :=
| ms : object -> object -> event
| cor : object -> event
| rep : object -> event 
| att_start : event.  


(* Example event system. 
    1. attestation starts then the rtm can measure any component. 
    2. after the rtm measure o1, o1 measures o2. 
    3. after that o2 measures o3 *)
Inductive E1 : relation event :=
| start : E1 (att_start) (ms rtm o1)
| mo1_o2 : E1 (ms rtm o1) (ms o1 o2)
| mo2_o3 : E1 (ms o1 o2) (ms o2 o3). 


(* The transitive closure. This will allow us to get to different events. *)
Inductive tc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TcStep : forall x y , R x y -> tc R x y
| TcFront : forall x y z, R x y -> tc R y z -> tc R x z.

(* May need to prove transitivity later on... I'm not sure. *)
Theorem tc_trans : forall {A} (R : A -> A -> Prop) x y, tc R x y
    -> forall z, tc R y z
    -> tc R x z.
Proof.  
    (* the key to this proof is induction on the hypothesis *)
    intros A R x y. intros H1. induction H1; intros.
    + eapply TcFront. apply H. apply H0.
    + eapply TcFront.
    ++  apply H. 
    ++ apply IHtc. apply H0.
Qed. 

Notation "R ^*" := (tc R) (at level 0).

(* (ms o1 o2) is in the transitive reflexive closure of the start event. *)
Example measure_o2 : E1^* (att_start) (ms o1 o2).
Proof.
eapply TcFront. 
+ apply start.
+ eapply TcStep. apply mo1_o2.
Qed.


(************************************
PROPERTIES OF THE RELATIONS
************************************)

(* Lemma E_irr says some object should never be able to measure itself*)
Lemma E_irr : forall x, E1 x x -> False.
Proof.
    intros. inversion H.
Qed.

(* Lemma E_asym says if you have an event x measures y then you should not be able to have an event y measures x *) 
Lemma E_asym : forall x y, ~ (E1 x y /\ E1 y x).
Proof. 
    cbv in *; intros. destruct H as [HA HB]. 
    destruct HA; subst; inversion HB.
Qed. 

(* define these Ltac commands to help in strict order proof *)
Ltac inv H := inversion H; subst.
Ltac invc H := inv H; clear H.

(* Rowe says the event system is a partial order. We believe it is a Strict order. That is, it is irreflexive and transitive. We use the transtive closure of the event system to make this work. *)
Instance tcE_irr : Irreflexive (tc E1).
Proof using.
  unfold Irreflexive, Reflexive, complement.
  intros e H.
  invc H.
  - eapply E_irr. eassumption.
  - (*0*)invc H0; (*1*)invc H1; (*2*)invc H.
    + invc H0; invc H.
      invc H1; invc H.
    + invc H0; invc H.
Qed.

Instance E_strict : StrictOrder (tc E1).
Proof.
    constructor.
    (* Irreflexive *)
     + cbv in *. intros e H; invc H.   
     ++ invc H0.
(*1*)++ invc H0.
(*2*)+++ invc H1.
(*3*)++++ invc H.
(*3*)++++ invc H0.
(*4*)+++++ invc H. invc H1. 
(*4*)+++++ invc H. invc H1. invc H2. invc H. invc H.   
(*2*)+++ invc H1.
(*3*)++++ invc H.
(*3*)++++ invc H0.
(*4*)+++++ invc H. invc H1.
(*4*)+++++ invc H. invc H1.
(*3*)+++ invc H1.
(*4*)+++++ invc H. 
(*4*)+++++ invc H.
    (* Transitive *)
    + cbv in *. intros x y z H. generalize dependent z. eapply tc_trans. eapply H.
Qed. 
