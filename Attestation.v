Require Import Relations.
Require Import Arith.
Require Import Lia.
Require Import Partial_Order.

Inductive Obj : Type :=
| RTM : Obj 
| o1 : Obj
| o2 : Obj
| o3 : Obj.

Definition noRTM: Type := {o:Obj | o <> RTM}.

(** Simple proof that no object constructed with `obj` can be the RTM. 
 Follows immediately from the definition of an inductive type. Not
 entirely necessary as `discriminate` or `inversion` will pop this out
 pretty quickly in a larger proof.*)

Lemma distinct_rtm: o1 <> RTM /\ o2 <> RTM /\ o3 <> RTM.
Proof.
  split. discriminate.
  split. discriminate.
  discriminate.
Qed.

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

(** Define an event graph as a partial ordering over events. *)

Module PO_experiment1.

(** Avoiding Coq's partial ordering infrastructure for the moment... *)

  Inductive lte : relation event :=
  | a: lte (ms RTM o1) (ms o1 o2)
  | b: lte (ms RTM o1) (ms o1 o3).

  Hint Constructors lte.
  
  Inductive lte2 : relation event :=
  | a1: lte2 (ms RTM o1) (ms o1 o2)
  | b1: lte2 (ms o1 o2) (ms o1 o3)
  | trans1: forall e e' e'', lte2 e e' -> lte2 e' e'' ->  lte2 e e''.

  Hint Constructors lte2.
  
  (** A specification, `S` is a partial order over events.  All elements
    of `S` are partial orderings over `event`.  Remember that the subset type
    will require a proof as one element whenever a value is specified. *)

  Definition S : Type := {r:relation event | (transitive event r)
                                             /\ (reflexive event r)
                                             /\ (antisymmetric event r)}.

  (** A specification, `S` admits an execution `E` if `E` is included in `S`.

   Note that this is different than that from Definition 3 in the Semantics
   paper.  I think this definition is not right as it does not capture the
   surjective property from Defintion 2.

   *)

  Theorem admitted1: forall e e', lte e e' -> lte2 e e'.
  Proof.
    intros.
    destruct e; destruct e'; (try inversion H).
    auto.
    apply trans1 with (ms o1 o2).
    auto.
    auto.
  Qed.
  
End PO_experiment1.

