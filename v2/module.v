(* In Coq, a module is a way of putting pieces of a system together in an abstract way. 

Once the module is created, it can be used in another implementation to ensure the new system follows the module's constraints. *)

(* In the case of the "confining" paper, a poset is a set, E, with an ordering operation where the ordering is a transitive, acyclic relation on E*)

Module Type Poset. 

(* In the module system, use parameter instead of variables. *)
Parameter Obj : Type. 
Parameter eq : Obj -> Obj -> Prop. 

Notation " t1 '==' t2 " := (eq t1 t2) (at level 40).

Parameter order: Obj -> Obj -> Prop.

(* when we use the poset, we will have to prove axioms in order to use them. *)
Axiom order_trans : forall x y z, order x y -> order y z -> order x z. 