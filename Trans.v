Require Import Relations.
Require Import Arith.
Require Import Omega.
Require Import LibTactics.
Require Import SfLib.
Require Import CpdtTactics.

Inductive Obj : Type :=
| RTM : Obj 
| o1 : Obj
| o2 : Obj
| o3 : Obj.

Inductive m : (relation Obj) :=
| rtmo1 : m RTM o1
| o1o2 : m o1 o2
| o1o3 : m o1 o3.

Hint Constructors m.

Hint Constructors clos_trans.

Print t_step.

Print m.

Theorem yep : ((clos_trans Obj m RTM) o1).
Proof.
  eapply t_step. apply rtmo1.
Qed.

Theorem yep' : ((clos_trans Obj m RTM) o2).
Proof.
  eapply t_trans.
  apply t_step. apply rtmo1.
  apply t_step. apply o1o2.
Qed.

Theorem yep'' : ((clos_trans Obj m RTM) o2).
Proof. debug eauto. Qed.

Theorem nope' : ((clos_trans Obj m RTM) RTM).
Proof. debug eauto.

Theorem nope'' : forall o, ~(m o o).
Proof. intros. unfold not. intros. induction o; inversion H. Qed.

Theorem nope''' : forall o p, ~((m o p) /\ (m p o)).
Proof.
  destruct o,p; unfold not; intros; inverts H;
  try (inverts H0);
  try (inverts H1).
Qed.

Definition complement {A} (R : relation A) : relation A := fun x y => R x y -> False.

Theorem irreflexive: forall o, ((complement m) o o).
Proof.
  intros. unfold complement. intros. induction o; inverts H.
Qed.

(* This is *not* the right proof.  The complement of the transitive closure
  is not the same as the transitive closure of the complement. *)

Theorem irreflexive': forall o, ((clos_trans Obj (complement m)) o o).
Proof.
  intros.
  destruct o.
  apply t_step.
  unfold complement. intros. inversion H.
  apply t_step.
  unfold complement. intros. inversion H.
  apply t_step.
  unfold complement. intros. inversion H.
  apply t_step.
  unfold complement. intros. inversion H.
Qed.

  unfold complement. intros.
  destruct o in H.
  inverts H. inversion H0.
  destruct y.
  try (apply t_step in H).
  destruct o in H.
  try (apply t_step with RTM in H).
Qed.










Theorem irreflexive: ~((clos_trans Obj m RTM) RTM).
Proof.
  unfold not.
  intros.
  inverts H.
  inverts H0.
  inverts H0.
  inverts H1.
  induction y.
  inverts H0.
  inverts H0.
  inverts H0.
  inverts H0.
  induction y.
  inverts H.
  eapply t_step in H2.
  induction H0.
  eapply t_trans in H2.