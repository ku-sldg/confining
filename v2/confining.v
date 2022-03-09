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
| o1 : object 
| o2 : object
| o3 : object. 

Hint Constructors object. 

(* this definition is simply saying there is a relation among objects. We have not defined the realtion yet. *)
Definition M' : Type := relation object.
Definition C' : Type := relation object. 

(* you cannot put relations inside a record in coq. 

So, so far the record will only hold objects and not the relation until we have it. *)
Record MS : Set := mkMS 
 { obj : object
 }. 

(* Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c). *)

Check relation. (*: Type -> Type*) 
Check transitive. (* : forall A : Type, relation A -> Prop*)

(* TO SAY M IS ROOTED*)
(* a subset type for all the object that does not include the RTM *)
Definition notRTM := {o : object | o <> rtm}.

Inductive M1 : object -> object -> Prop := 
    | rtm_o : M1 rtm o1
    | o1_o2 : M1 o1 o2
    | o2_o3 : M1 o2 o3. 
    
Check M1. (* : object -> object -> Prop *)
Check M1 : relation object. 


Check clos_trans. (*: forall A : Type, relation A -> A -> A -> Prop *)
(* the transitive closure needs a variable and a relation. *)

Definition M_plus := clos_trans _ M1.

Lemma o_antisym : forall o, ~(M1 o o).
Proof.
    unfold not. intros. induction o; inversion H.
Qed.    

(* I am stuck on this proof. If you destruct H' then it goes away. I think the rewrite should work. I'm not sure why it doesnt.  *)
Example o_tran : transitive _ M1.
Proof.
    unfold transitive. intros. induction x; destruct y; destruct z; try apply H; try apply H0. 
    + assert ( H': forall o, ~(M1 o o)). { apply o_antisym. } specialize H' with rtm. unfold not in H'. (* rewrite <- H'. *) 
Abort. 

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
