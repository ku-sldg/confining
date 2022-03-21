(*
  https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html
*)

Require Import Relations.
Require Import Arith.
Require Import Lia.
Require Import Partial_Order.
Require Export Pset.

Section MeasurementClass.

Ltac inverts H := inversion H; subst; clear H.
  
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

(** Each of the following produce one proof value for
 each of the theorem types defined in [Measurement] *)

Lemma distinct_rtm_Obj: forall o o' : Obj, o = RTM -> o' = RTM -> o = o'.
Proof.
  intros o o'; intros H1 H2; subst; reflexivity.
Qed.

Hint Resolve distinct_rtm_Obj : core.

Lemma irreflexive_m_Obj:  forall o : Obj, ~ m o o.
Proof.
  intros. unfold not. intros. inverts H.
Qed.

Hint Resolve irreflexive_m_Obj : core.

Lemma asymmetric_m_Obj: forall o p, ~((m o p) /\ (m p o)).
  intros. unfold not. intros H.
  inverts H;
    inverts H1;
    inverts H0;
    inverts H0;
    inverts H0.
Qed.

Hint Resolve asymmetric_m_Obj : core.

Lemma no_measures_rtm_m_Obj: forall o o': Obj, (m o o') -> o' <> RTM.
Proof.
  intros o o'; unfold not. intros H H1;
  inverts H;
  inverts H2.
Qed.

Hint Resolve no_measures_rtm_m_Obj : core.

Lemma irreflexive_c_Obj: forall o:Obj, ~(c o o).
Proof.
  intros o; unfold not; intros H;
  inverts H.
Qed.

Hint Resolve irreflexive_c_Obj : core.

Lemma asymmetric_c_Obj: forall o p:Obj, ~((c o p) /\ (c p o)).
Proof.
  intros o o'; unfold not; intros H.
  inverts H.
  inverts H0.
  inverts H1.
Qed.
  
Hint Resolve asymmetric_c_Obj : core.

Lemma no_depends_rtm_c_Obj: forall o o': Obj, (c o o') -> o <> RTM.
Proof.
  intros o o'; intros H. unfold not. intros.
  inverts H0. inverts H.
Qed.

Hint Resolve no_depends_rtm_c_Obj : core.

Lemma coverage_Obj: forall o:Obj, o=RTM \/ exists o':Obj, m o' o.
Proof.
  intros o;
  induction o;
  try (left; reflexivity);
  try (right; eexists; constructor).
Qed.

Hint Resolve coverage_Obj : core.

(** Define [MeasurementSys] to be an isntance of [Measurement] over [RTM], [m]
  and [c]. *)

Instance MeasurementSys: (Measurement RTM m c).
(** Must now prove that all the properties hold for this system.  Coq makes
 this happen automatically. [constructor] breaks up the record into its
 constituent parts.  If a value does not exist for a field, then the prover
 is called to create one. All the proof fields are defined previously and
 installed as [auto] hints.  Thus the proofs are just calls to [eauto].*)

Proof.
  constructor; eauto.
Qed.

(** Define an event system that allows specifying instances of
 attestation startup, measurement, corruption, and repair. Parameterized
 over [O] to allow different object types. *)

Inductive event(O:Type):Type :=
| att_start : (event O)
| ms : O -> O -> (event O)
| cor : O -> (event O)
| rep : O -> (event O).

(** A simple even system defined over the inductive type [Obj] *)
Definition EventObj := (event Obj).

(** A silly relation that  Places a partial order
 on events.  [att_start] preceds [RTM] measurement of [o1] and [o2].
 Measurement of [o3] by [o2] occurs after measurement of [o2]. *)

Inductive e: (relation EventObj) :=
| e1 : e (att_start _) (ms _ RTM o1)
| e2 : e (att_start _) (ms _ RTM o2)
| e3 : e (ms _ RTM o1) (ms _ o1 o3).

Hint Constructors e : core.

(* Define transitive reflexive closure of a relation *)
Inductive trc{A}(R : (relation A)): A -> A -> Prop :=
| TrcRefl : forall a:A, trc R a a
| TrcFront : forall x y z,
    R x y -> trc R y z -> trc R x z.

Hint Constructors trc : core.

Instance ordered_e : (preset eq (trc e)).
Proof.
  constructor;

  (* Shockingly, the transitive reflexive closure of e is in fact transitive
     and reflexive. *)

  try (intros; subst; auto).
  
  induction H. assumption. eauto.
Qed.

(* An event system is an event ordering defined by [(trc leq0)] and sequences
 of events defined by [traces]. *)
Class eventSystem(Event:Type) := {
    leq0: (relation Event);
    leq := (trc leq0)
    }.

(* A concrete event system defined over [EventObj] using [e] as the value
 for [delta].  Nothing to prove here. *)
Instance eventSystemObj: (eventSystem EventObj) := {leq0 := e}.

Example ex0: leq (att_start _) (ms _ RTM o1).
Proof.
  unfold leq,leq0.
  simpl. eapply TrcFront.
  apply e1.
  apply TrcRefl.
Qed.

(* Prove that [att_start] occurs before [o1] measures [o3] *)

Example ex1: leq (att_start _) (ms _ o1 o3).
Proof.
  unfold leq, leq0; simpl.
  eauto.
Qed.

(* Prove that [RTM] measures [o1] before [o1] measures [o3] *)

Example ex2: leq (ms _ RTM o1) (ms _ o1 o3).
Proof.
  unfold leq, leq0; simpl.
  eauto.
Qed.

(* Prove that [RTM] measuring [o2] and [RTM] measuring [o1] are not ordered
 events. *)

Example ex3: ~ (leq (ms _ RTM o1) (ms _ RTM o2)) /\ ~(leq (ms _ RTM o2) (ms _ RTM o1)).
Proof.
  unfold not,leq,leq0; simpl; split; intros.
  inversion H; subst; destruct y.
  inversion H0.
  inversion H0; subst. inversion H1; subst. inversion H2. inversion H1. inversion H2.
  inversion H0.
  inversion H; subst; destruct y.
  inversion H0.
  inversion H0; subst. inversion H1; subst. inversion H2. inversion H1. inversion H2.
Qed.

End MeasurementClass.
