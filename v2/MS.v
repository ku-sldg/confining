Require Import Relations. 
Require Import Coq.Classes.RelationClasses.


Section MS. 

(* This document is a Coq model of Paul Rowe's paper titled "Confining Adversary Actions via Measurements" *)


(* Here, everything takes place within the measurement system *)
(*Section Measurement_System.*) 

(* Definition 1 is a measurement system (MS). 

    MS = (O, M, C)

    O is set of object, M is the measures relation, C is the context relation 

    M & C are binary relations on O 

*)

Class MS {object: Type}(rtm: object) (m: relation object) (c:relation object) : Type := {
    (* nothing can measure the root of trust *)
    rtm_not_target : forall o o', (m o o') -> o' <> rtm ;
    (* no context can measure root of trust *)
    rtm_not_context : forall o o', c o o' -> o' <> rtm ;
    (* if one object measures another then the measured object cannot be the measurer *)
    m_asymmetric : forall o1 o2, m o1 o2 -> ~ (m o2 o1) ;
    (* nothing can measure itself *)
    m_irreflexive: forall o1, ~(m o1 o1) 
}.

(* this is our set of objects *)
Inductive object : Type :=
| rtm : object
| o1 : object 
| o2 : object
| o3 : object. 

(* Hint Constructors object. *)

(* the first measurement relation. Just an example. *)
Inductive M1 : object -> object -> Prop := 
| rtm_o : M1 rtm o1
| o1_o2 : M1 o1 o2
| o2_o3 : M1 o2 o3. 
    
(* the first context relation *)
Inductive C1 : object -> object -> Prop :=
| c1_c2 : C1 o1 o2
| c2_c3 : C1 o2 o3. 

(* Here we create an instance of the measurement system. It has the root of trust rtm, the measurement relation M1, and the context relation C1. When instancating the class, we must prove it satisfies all properties.  *)
Instance MS_1 : (MS rtm M1 C1).
Proof.
    constructor; intros; try unfold not; repeat (try intros; try subst; try inversion H; try inversion H0; subst).
Qed.

(* These are mearly facts metioned in the paper. There is nothing to prove about them -- I don't think. *)
Definition measurers_of_o := forall o' : object, {o : object | M1 o' o}.
Definition not_RTM := {o : object | o <> rtm}.
Definition context_trans := transitive _ C1. 
(* M+ is the transitive closure of M. When you take transitive closure, you now have a chain of measurements *)
Definition M_plus := clos_trans _ M1.
 
(* the rtm must be distinugished *)
Theorem rtm_dist: rtm <> o1 /\ rtm <> o2 /\ rtm <> o3.
Proof.
    split. discriminate.
    split; discriminate.
Qed.

End MS. 