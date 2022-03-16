
(*
  https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html
*)

Require Import Relations.
Require Import Arith.
Require Import Lia.
Require Import Partial_Order.
Require Export Pset.

(** Definition of a well-formed measurement system.  Requires an [Obj] type
 that represents the universe, a measurement relation [m] and a context
 relation [c].  If the measurement system is well-formed:

 - both [m] and [c] are reflexive and assymetric.
 - nothing measures the RTM
 - the RTM has no context
 - the RTM is unique.
*)

Class Measurement {Obj : Type}(rtm:Obj)(m:relation Obj)(c:relation Obj):Type :=
{
  distinct_rtm: forall o o', o=rtm -> o'=rtm -> o=o';
  irreflexive_m: forall o, ~(m o o);
  asymmetric_m: forall o p, ~((m o p) /\ (m p o));
  no_measures_rtm_m: forall o o': Obj, (m o o') -> o' <> rtm;
  irreflexive_c: forall o, ~(c o o);
  asymmetric_c: forall o p, ~((c o p) /\ (c p o));
  no_depends_rtm_c: forall o o': Obj, (c o o') -> o <> rtm;
  coverage: forall o:Obj, o=rtm \/ exists o':Obj, m o' o
}.

(* Define [Obj], [m], and [c] for a silly example system.  Nothing special
 about these definitions.  They are just here as examples. *)

(* 4 objects, [RTM] and [o1]-[o3]. *)

Inductive Obj : Type :=
| RTM : Obj 
| o1 : Obj
| o2 : Obj
| o3 : Obj.

(* Measurement relation defining what objects measure other objects.
 [m o1 o2] states that [o1] measures [o2]. *)

Inductive m : relation Obj :=
| mrtmo1 : m RTM o1
| mo1o2 : m o1 o2
| mo1o3 : m o1 o3.

(* Context relation defining what objects are in other objects contexts.
 [c o1 o2] states that [o1] is in the context of [o2] *)

Inductive c : relation Obj :=
| o1o2 : c o2 o1.

(** Define [MeasurementObj] to be an isntance of [Measurement] over [RTM], [m]
  and [c]. *)

Instance MeasurementObj: (Measurement RTM m c).

(** Must now prove that all the properties hold for this system.  Coq makes
 this happen automatically. [constructor] breaks up the record into its
 constituent parts.  If a value does not exist for a field, then the prover
 is called to create one. Each of the following produce one proof value for
 each of the 7 theorem types. *)

Proof.
  constructor.
  
  intros. subst. reflexivity.
  
  intros. unfold not. intros. inversion H.
  
  intros. unfold not. intros H. inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H0; subst; clear H0.
  inversion H0.
  inversion H0.
  
  intros. unfold not. intros H0.
  inversion H; subst; clear H.
  inversion H2.
  inversion H2.
  inversion H2.
  
  intros. unfold not. intros. inversion H.

  intros. unfold not. intros H. inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H0; subst; clear H0.

  intros o o'.
  intros H.
  unfold not. intros H0.
  inversion H; subst; clear H.
  inversion H1.

  intros.
  induction o;
  try (left; reflexivity);
  try (right; eexists; constructor).
Qed.

(** Check the type of [distinct_rtm] as an example *)

Check MeasurementObj.(distinct_rtm).

(** Check the type of [no_depends_rtm_c] as an example *)

Check MeasurementObj.(no_depends_rtm_c).

(** Define an event system that allows specifying instances in time of
 attestation startup, measurement, corruption, and repair. Parameterized
 over [Obj] to allow different object types. *)

Inductive event(O:Type):Type :=
| att_start : (event O)
| ms : O -> O -> (event O)
| cor : O -> (event O)
| rep : O -> (event O).

(** A simple even system defined over the inductive type [Obj] *)
Definition EventObj := (event Obj).

(** A silly transition function from event to event.  Places a partial order
 on events.  [att_start] preceds [RTM] measurement of [o1] and [o2].
 Measurement of [o3] by [o2] occurs after measurement of [o2]. *)

Inductive e: (relation EventObj) :=
| e1 : e (att_start _) (ms _ RTM o1)
| e2 : e (att_start _) (ms _ RTM o2)
| e3 : e (ms _ RTM o1) (ms _ o1 o3).

Instance ordered_e : (pset eq e).

(* Define transitive reflexive closure of a relation *)
Inductive trc{A}(R : (relation A)): A -> A -> Prop :=
| TrcRefl : forall a:A, trc R a a
| TrcFront : forall x y z,
    R x y -> trc R y z -> trc R x z.

(* An event system is an event ordering defined by [delta] and sequences
 of events defined by [traces]. *)
Class eventSystem(Event:Type) := {
    delta: (relation Event);
    leq := (trc delta)
    }.

(* A concrete event system defined over [EventObj] using [e] as the value
 for [delta].  Nothing to prove here. *)
Instance eventSystemObj: (eventSystem EventObj) := {delta := e}.

Example ex0: traces (att_start _) (ms _ RTM o1).
Proof.
  unfold traces.
  unfold delta.
  simpl. eapply TrcFront.
  apply e1.
  apply TrcRefl.
Qed.

Example ex1: traces (att_start _) (ms _ RTM o3).
Proof.
  unfold traces; unfold delta.
  simpl. eapply TrcFront.
  eapply e1.
  eapply TrcFront.
  eapply e3.
  eapply TrcFront
  apply e3.

