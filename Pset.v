(**

 [Pset] defines a partially ordered set.
 
*)

  
  Class pset{A:Type}(eq:A->A->Prop)(order:A->A->Prop):Type :=
    { eq_refl : forall x, (eq x x);
      eq_sym : forall x y, (eq x y)->(eq y x);
      eq_trans: forall x y z, (eq x y)->(eq y z)->(eq x z);

      order_refl : forall x y, eq x y -> order x y;
      order_antisym: forall x y, order x y -> order y x -> eq x y;
      order_trans : forall x y z, order x y -> order y z -> order x z
    }.

    Class preset{A:Type}(eq:A->A->Prop)(order:A->A->Prop):Type :=
    { pre_eq_refl : forall x, (eq x x);
      pre_eq_sym : forall x y, (eq x y)->(eq y x);
      pre_eq_trans: forall x y z, (eq x y)->(eq y z)->(eq x z);

      pre_order_refl : forall x y, eq x y -> order x y;
      pre_order_trans : forall x y z, order x y -> order y z -> order x z
    }.

