(* define record triple that defines O M and C so each is defined seperately but you can put them together 

could also use module types like we did for the Galois connections 

coq Object system 

TO DO: 
- branch the confining repo 
- then during 1-1 decide how to merge them *)


(* This document is a Coq model of Paul Rowe's paper titled "Confining Adversary Actions via Measurements" *)

Require Import Relations. 


(* Section used here so that we can create section-local declarations that can be reused elsewhere. 

Here, everything takes place within the measurement system *)
Section Measurement_System. 

(* Definition 1 is a measurement system (MS). 

    MS = (O, M, C)

    O is set of object, M is the measures relation, C is the context relation 

    M & C are binary relations on O 

*)


(* this is our set of objects *)
Inductive object : Type :=
| rtm : object
| a1 : object 
| vc : object
| sys : object
| ker : object
| context : object.

Hint Constructors object. 

(* M is the measurement relation 
   C is the context relation *)
Inductive M : object -> object -> Prop := 
    | m_rtm : forall o1 o2: object, o2 <> rtm -> M o1 o2.  

Definition M' : relation object.
Check M'. (*: Type*)

Check le. (* nat -> nat -> Prop*)
Check le : relation nat.  

Check M. (* : object -> object -> Prop *)
Check M : relation object. 

(* https://softwarefoundations.cis.upenn.edu/lf-current/Rel.html according to software foundations, this should work. *)

(* Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c). *)

Check relation. (*: Type -> Type*) 
Check transitive. (* : forall A : Type, relation A -> Prop*)

Theorem trans_C : transitive object M.
Proof.
    unfold transitive. intros.
    induction x; destruct z.  
Abort. 

(* a subset type for all the object that does not include the RTM

I think here we are showing this is a acyclic *)
Definition notRTM := {o : object | o <> rtm}.

Check clos_trans. (*: forall A : Type, relation A -> A -> A -> Prop *)
(* the transitive closure needs a variable and a relation. *)


Definition M_plus := clos_trans _ M.

(* why can't we prove this? shouldn't we be able to prove this?? Or at least get it to type check. *)
(* Theorem trans_clos': clos_trans _ M. *)



(* the rtm must be distinugished *)
Theorem rtm_dist: rtm <> vc /\ rtm <> sys /\ rtm <> ker.
Proof.
    split. discriminate.
    split; discriminate.
Qed.

(* Definition 2: Events. There are 3 labels for event. Measurement event (ms), adversary events (corruption (cor) and repair (rep)) and an attestation start event (att_start)*)

Inductive event :=
| ms : object -> object -> event
| cor : object -> event
| rep : object -> event 
| att_start : event.  


Check ms vc sys.
(* there is no way to embed the context relation... wondering if something is wrong with the defintion. *)
(* Check ms context ker (ms vc sys). *)

(* execution is a partially ordered set of events *)

(* event e touches o iff o is argument to e. *)
Inductive touches : event -> object -> Prop :=
| touch_ms: forall o1 o2, touches (ms o2 o1) o1
| touch_cor: forall o, touches (cor o) o  
| touch_rep: forall o, touches (rep o) o
| touch_start : forall o, touches (att_start) o. 

(* execution is a poset of events *)
(* a partial order is a preorder that is anti symmetric *)


End Measurement_System. 

(* *)
