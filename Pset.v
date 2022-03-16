(**

 [Pset] defines a partially ordered set.
 
*)

  
  Class pset{A:Type}(eq:A->A->Prop)(order:A->A->Prop):Type :=
    { Eq_refl : forall x, (eq x x);
      Eq_sym : forall x y, (eq x y)->(eq y x);
      Eq_trans: forall x y z, (eq x y)->(eq y z)->(eq x z);

      Order_refl : forall x y, eq x y -> order x y;
      Order_antisym: forall x y, order x y -> order y x -> order x y;
      Order_trans : forall x y z, order x y -> order y z -> order x z
    }.

