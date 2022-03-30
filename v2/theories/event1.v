(* PURPOSE: This file is one example of an event system. It is a less generalized one where the events are concrete measurement actions. There are not corruption or repair actions. 

The measurement systems are defined in and imported from MS.v.

This is a continuation of our attempt at Coq model of Paul Rowe's paper titled "Confining Adversary Actions via Measurements" *)

(* CURRENT PROBLEMS: Due to the event system definition, it is difficult (if not impossible) to prove that the event system is partially ordered. Specifically, the antisymmetric property *)

Require Import Relations. 
Require Import Coq.Classes.RelationClasses.

Print LoadPath.
(* Add LoadPath "/Users/annarosefritz/Documents/EECS_research/GitHubRepos/confining/v2". *)

From v2 Require Import MS_noContext.
Print MS.

Section event1. 

(* Definition 2: Events. There are 3 labels for event. Measurement event (ms), adversary events (corruption (cor) and repair (rep)) and an attestation start event (att_start)*)

Inductive event :=
| ms : object -> object -> event
| cor : object -> event
| rep : object -> event 
| att_start : event.  

Check ms o1 o2.

(* example event system. 
    attestation starts then the rtm can measure any component. 
    after the rtm measure o1, o1 measures o2. 
    after that o2 measures o3 *)
Inductive E1 : relation event :=
| start : E1 (att_start) (ms rtm o1)
| mo1_o2 : E1 (ms rtm o1) (ms o1 o2)
| mo2_o3 : E1 (ms o1 o2) (ms o2 o3). 

(* As Perry has mentioned, we need the TRC to 
have more than just a sigle step of events. *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z, R x y -> trc R y z -> trc R x z.

(* May need to prove transitivity later on... I'm not sure. *)
Theorem trc_trans : forall {A} (R : A -> A -> Prop) x y, trc R x y
-> forall z, trc R y z
-> trc R x z.
Proof.  
(* the key to this proof is induction on the hypothesis *)
intros A R x y. intros H1 z H2. induction H1.
+ apply H2.
+ eapply TrcFront. apply H. apply IHtrc. apply H2.
Qed. 

(* this is just the transitive closure *)
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
+ eapply TcFront. apply H. apply IHtc. apply H0.
Qed. 


(* Transitive-reflexive closure is so common that it deserves a shorthand notation! *)
Set Warnings "-notation-overridden". (* <-- needed while we play with defining one
* of the book's notations ourselves locally *)
Notation "R ^**" := (trc R) (at level 0).
Notation "R ^*" := (tc R) (at level 0).

(* (ms o1 o2) is in the transitive reflexive closure of the start event. *)
Example measure_o2 : E1^* (att_start) (ms o1 o2).
Proof.
eapply TcFront. 
+ apply start.
+ eapply TcStep. apply mo1_o2.
Qed.

Example measure_o3 : E1^* (att_start) (ms o2 o3).
Proof.
eapply TcFront.
+ apply start.
+ eapply TcFront.
++ apply mo1_o2.
++ eapply TcStep. apply mo2_o3.    
Qed.   

Check E1^*. 

(* execution is a poset of events *)
(* a partial order is a preorder that is anti symmetric *)
Definition E' : PreOrder E1.
Proof.
constructor.
+ (* proof events are reflexive...  *)
unfold Reflexive. induction x.  
Abort.

(* A preorder is reflexive and transitive. Proving this as a prerec to the partial order. *)
Instance E'' : PreOrder E1^**.
Proof.
constructor. 
+ unfold Reflexive. intros. apply TrcRefl.
+ unfold Transitive. intros x y z H1 H2. 
induction H1. apply H2. eapply TrcFront. apply H. apply IHtrc. apply H2.        

(* can also solve proof with these commands 
generalize dependent z. apply trc_trans. apply H.*)
Qed.  

Class PartialOrder' {A} (R: relation A) := {
    refl :> Reflexive R ; 
    anti_sym :> Antisymmetric _ eq R ;
    trans :> Transitive R 
    }.



Instance E : PartialOrder' E1^**.
Proof.
    constructor.
    (* proving reflexivity is easy ... *)  
    * unfold  Reflexive. intros. apply TrcRefl.
    (* proving antisymmetric is more difficult ... *)
    * unfold Antisymmetric. intros. eapply TrcFront in H. 
    ** inversion H.
    *** reflexivity.
    *** subst. inversion H1.  Abort. 
    (* more difficult... maybe impossible. At this point, we realize is must be a strict partial order. *)

Lemma E_trans : Transitive E1^*.
Proof.
    Abort.
    
Class StrictPartialOrder {A} (R: relation A) := {
    arefl :> Irreflexive R ; 
    asym :> Asymmetric R ; 
    strans :> Transitive R 
}.

Check MS.
Check E1.  

Lemma m_irr : forall x, E1 x x -> False.
Proof.
    intros. Check m_irreflexive. destruct E1.  

Instance E_strict : StrictPartialOrder E1^*.
Proof. 
    constructor. 
    + cbv in *. intros x h. absurd (E1 x x). assert m_irreflexive.  apply m_irreflexive.   eapply TcFront in h. inversion h; subst. apply H. inversion H.    Search "irreflexive". inversion h; subst. apply m_irreflexive in h. .  

Class StrictPartialOrder' {A} (R: relation A) := {
    (* arefl :> Irreflexive R ; 
    asym :> Asymmetric R ; *)
    strans' :> Transitive R 
}.
        
Instance E_strict' : StrictPartialOrder' E1. 
Proof.
    constructor. unfold Transitive. intros x y z H. induction H.
    + intros. (* no where to go, need transitive closure *) Abort.    

            
Instance E_strict' : StrictPartialOrder' E1^*. 
Proof.
    constructor.
    + unfold Transitive. intros x y z. intros h1. induction h1; intros.
    ++ eapply TcFront.
    +++ apply H.
    +++ apply H0.
    ++ eapply TcFront. 
    +++ apply H. 
    +++ apply IHh1. apply H0.
Qed. 
            
End event1. 
            
(* *)
                