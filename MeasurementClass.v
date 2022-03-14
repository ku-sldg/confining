
(*
  https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html
*)

Require Import Relations.
Require Import Arith.
Require Import Lia.
Require Import Partial_Order.

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
  no_depends_rtm_c: forall o o': Obj, (c o o') -> o <> rtm
}.

(* Define [Obj], [m], and [c] for a silly example system.  Nothing special
 about these definitions.  They are just here as examples. *)

Inductive Obj : Type :=
| RTM : Obj 
| o1 : Obj
| o2 : Obj
| o3 : Obj.

Inductive m : relation Obj :=
| mrtmo1 : m RTM o1
| mo1o2 : m o1 o2
| mo1o3 : m o1 o3.

Inductive c : relation Obj :=
| o1o2 : c o2 o1.

(** Define [MeasurementObj] to be an isntance of [Measurement] over [RTM], [m]
  and [c]. *)

Instance MeasurementObj: (Measurement RTM m c).

(** Must now prove that all the properties hold for this system.  Coq makes
 this happen automatically. *)

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
Qed.

(** Check the type of [distinct_rtm] *)

Check MeasurementObj.(distinct_rtm).

(** Check the type of [no_depends_rtm_c] *)

Check MeasurementObj.(no_depends_rtm_c).
