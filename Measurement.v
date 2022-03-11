(** Measurement Semantics

 Experimental theory describing the semantics of measurement and attacker 
 event ordering.

 Todo:
  - Introduce the dependent type for everything but RTM

  Basic Approach:
  + Defined well-formedness of M and M+.  Irreflexive, nothing measures RTM
  + Define event type
  - Define event partial orders including measurements, corruptions, and repairs
  - Define specifications, executions, and admit
  - Show that all corruptions are measured prior to associated repairs
  - The resulting measurement sequence is what must occur as a result of
    the attestation protocol

  If we can find the measurement , we know what we must look for
  in the attestation bundling evidence.

*)

Require Import Relations.
Require Import Arith.
Require Import Lia.
Require Import Partial_Order.

(* Set Implicit Arguments. *)

Module Type Measurement.

(** Object type is either RTM or an indexed object *)

(** Simple definition of objects that measure and get measured.  The
  distinguished value [rtm] is the root of trust for measurement.  Three
  additional objects are defined making the set finite. *)

  Parameter Obj : Type.
  Parameter RTM : Obj.

(** Define a subset type that contains all objects other than the RTM. *)
  Definition noRTM: Type := {o:Obj | o <> RTM}.

(** Simple proof that no object constructed with `obj` can be the RTM. 
  Follows immediately from the definition of an inductive type. Not
  entirely necessary as `discriminate` or `inversion` will pop this out
  pretty quickly in a larger proof.*)

  Axiom distinct_rtm: forall o o', o=RTM -> o'=RTM -> o=o'.
  
(** An [event] is a measurement ([ms]) performed by an object on another
    object, a corruption event ([cor]) performed by an adversary, a repair
    event ([rep]) performed by an adversary, or the beginning of runtime
    attestation [att_start].

    Note that the base type no longer trys to capture well-formedness.
    Instead well-formedness is captured by a subset type.
 *)

  Inductive event : Type :=
  | att_start : event
  | ms : Obj -> Obj -> event
  | cor : Obj -> event
  | rep : Obj -> event.

  (** Captures well-formedness for events.  The target can never be the RTM *)
  
  Definition is_well_formed_event(e:event):Prop :=
    match e with
    | ms o o' => o' <> RTM
    | cor o => o <> RTM
    | rep o => o <> RTM
    | att_start => True
    end.

(** Define the subset type of well-formed events *)

  Definition well_formed_event : Type := {e : event | is_well_formed_event e}.
  
  Parameter m : relation Obj.
  
  (** Simple examples over `m` to exercise the structure *)
  
  (** Prove that `m` is not reflexive - nothing measures itself *)

  Axiom irreflexive_m: forall o, ~(m o o).

  Hint Resolve irreflexive_m.

  (** Prove that `m` is not symmetric. Should be picked up later *)

  (* Axiom asymmetric_m: forall o p, ~((m o p) /\ (m p o)). *)

  (** Prove that RTM is not measured *)

  Axiom no_measures_rtm_m: forall o o': Obj, (m o o') -> o' <> RTM.

  Hint Resolve no_measures_rtm_m : core.

  (** [M] is well-formed if [RTM] is not measured by anything, nothing
      measures itself, and measurement is asymmetric. *)

  Definition is_well_formed_M (m:(relation Obj)):Prop :=
    (forall o o' : Obj, (m o o') -> o' <> RTM) /\ (forall o, ~(m o o)).

  Axiom is_well_formed_m : is_well_formed_M m.

  (** Define the subset type containing well-formed elements of M *)

  Definition well_formed_M : Type := {m:(relation Obj) | is_well_formed_M m}.

  (** [M_plus] is the transitive closure of [M] and captures measurement 
      chains. *)

  Definition M_plus(m:relation Obj):relation Obj := clos_trans Obj m.

  (** Define well-formedness of `M_plus` starting from `well_formed_M`. This
    uses subset types to capture only well-formed M in the domain type.  M_plus
    is well-formed if it is irreflexive and every object's measurement chain
    is rooted on RTM. *)

Definition is_well_formed_M_plus(m:well_formed_M) : Prop := 
  match m with
    | exist _ v p => forall o, ~(M_plus v o o) /\ (M_plus v RTM o)
  end.

(** Define the type of well-formed `M_plus` *)

Definition well_formed_M_plus: Type := {m:well_formed_M | is_well_formed_M_plus m}.

(** Need to find a problem caused by `clos_trans m o o`.  Specifically, need
 to identify some fact that somes from this term that contradicts an existing
 term. *)

Definition complement {A} (R : relation A) : relation A :=
  fun x y => R x y -> False.
  
(*
Example is_well_formed_m_plus : forall o, ~(m_plus o o).
Proof.
  intros; unfold not; intros.
  induction o.
  inversion H.
  assert (~ (m RTM RTM)).
    apply irreflexive_m.
  contradiction.
  clear H2 z.
  inversion H1; subst.
  apply no_measures_rtm_m in H2.
Abort.
 *)

(** Alternate definition of well-formedness using a subset type to capture
 that that `m` is well-formed before creating `m_plus`. Remember that `exist`
 takes two arguments - a value and a proof that the value belongs in the
 associated subtype. *)

(*
Definition well_formed_m_plus (m:{m:M | is_well_formed_M m}): Prop := 
  match m with
    | exist m' p => forall o, ((clos_trans Obj m') o o) -> False
  end.
 *)

(*
Lemma well_formed_m2: well_formed_m_plus ((exist is_well_formed_M m) is_well_formed_m).
Proof.
  unfold well_formed_m_plus.
  intros.
  induction o.
  assert (is_well_formed_M m).
  apply is_well_formed_m.
  unfold is_well_formed_M in H0.
  assert ((m RTM RTM) -> RTM <> RTM).
  apply H0.
Abort.
*)
(** Prove there is a measurement chain from RTM to obj 2 *)

(*
Example rtml2_ex: m_plus RTM o2.
Proof.
  unfold m_plus. apply t_trans with o1; auto.
Qed.
*)
(** Measurement of [o] is rooted if the transitive closure of [m] contains
  [(RTM,o)]. *)

(*
Definition rootedM (o: Obj) :=
  (m_plus RTM o).
 *)

(** Prove that obj 2 measurement is rooted in the RTM *)

(*
Example rooted_obj_2: rootedM o2.
Proof.
  unfold m_plus. apply t_trans with o1; auto.
Qed.
 *)

(** All measurements are rooted.  This theorem is badly stated.  It says
  that _every_ object is rooted, not just the objects in [M].  Need to work
  through this.*)

(*
Theorem all_rooted: forall (o:Obj), o<>RTM -> rootedM o.
Proof.
  intros.
  induction o.
Abort.
 *)

(** [C] is a relation among objects representing the context that defines
  when one object provides a clean runtime context for another *)

(*
Definition C : Type := relation O.

(** A system, [T], is a triple of objects, measurement relation and C.*)

Definition T : Type := (O * M * C)%type.
*)
End Measurement.

Module Example <: Measurement.

  (** Collection of Objects measuring, being measured, and forming contexts *)
  Inductive Obj : Type :=
  | RTM : Obj 
  | o1 : Obj
  | o2 : Obj
  | o3 : Obj.
  
  (** An example measurement relation, [m]. [RTM] measures [o1],
    [o1] measures [o2][o2] and [o3].  Should be well-formed *)
  Inductive m : relation Obj :=
  | mrtmo1 : m RTM o1
  | mo1o2 : m o1 o2
  | mo1o3 : m o1 o3.

  Hint Constructors m : core.
  
  (** An example [c].  [o2] depends on [o1]. *)
  Inductive c : relation Obj :=
  | o1o2 : c o2 o1.

  Hint Constructors c : core.

  Lemma irreflexive_m: forall o, ~(m o o).
  Proof.
    intros. unfold not. intros. induction o; inversion H.
  Qed.
  
  Hint Resolve irreflexive_m.

  Lemma asymmetric_m: forall o p, ~((m o p) /\ (m p o)).
  Proof.
    intros. unfold not. intros.
    inversion H.
    inversion H0. subst.
    inversion H1. subst.
    inversion H1. subst.
    inversion H1.
  Qed.

  Hint Resolve asymmetric_m : core.

  Lemma no_measures_rtm_m: forall o o': Obj, (m o o') -> o' <> RTM.
  Proof.
    intros; unfold not; subst; intros; induction o'; try discriminate.
    inversion H; subst.
  Qed.

  Hint Resolve no_measures_rtm_m : core.
  
  Lemma irreflexive_c: forall o, ~(c o o).
  Proof.
    intros; intros H; inversion H.
  Qed.
  
  Hint Resolve irreflexive_c : core.

  Lemma asymmetric_c: forall o p, ~((c o p) /\ (c p o)).
  Proof.
    intros. unfold not. intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    inversion H1.
  Qed.

  Hint Resolve asymmetric_c : core.

  Lemma no_depends_rtm_c: forall o o': Obj, (c o o') -> o <> RTM.
  Proof.
    intros o o'.
    intros. destruct H. discriminate.
  Qed.

  Hint Resolve no_depends_rtm_c : core.




  Definition is_well_formed_M (m:(relation Obj)):Prop :=
    (forall o o' : Obj, (m o o') -> o' <> RTM) /\ (forall o, ~(m o o)).
  
  Lemma is_well_formed_m: is_well_formed_M m.
  Proof.
    unfold not; subst. split. eauto. eauto.
  Qed.

  Definition is_well_formed_C (c:(relation Obj)):Prop :=
    (forall o o' : Obj, (c o o') -> o <> RTM).

  Lemma is_well_formed_c: is_well_formed_C c.
  Proof.
    intros o o'. intros. inversion H. discriminate.
  Qed.
  
  (* Subset type of well-formed measurement relations over some set of objects
     [Obj].
   *)
  Definition well_formed_M : Type := {m:(relation Obj) | is_well_formed_M m}.

  Definition well_formed_C : Type := {c:(relation Obj) | is_well_formed_C c}.

  (* Example of a measurement relation that is well-formed *)
  Definition m':well_formed_M := exist is_well_formed_M m is_well_formed_m.

  Definition c':well_formed_C := exist is_well_formed_C c is_well_formed_c.

  Record S : Type := mkS {mr:(relation Obj) ; cr:(relation Obj)}.

  Definition ex := {|mr:=m; cr:=c|}.

  Check mr ex.

  Check cr ex.

  Definition is_well_formed_S(s:S):Prop := is_well_formed_M (mr s) /\ is_well_formed_C (cr s).

  Example is_well_formed_s: is_well_formed_S ex.
  Proof.
    split.
    apply is_well_formed_m.
    apply is_well_formed_c.
  Qed.
  
End Example.
