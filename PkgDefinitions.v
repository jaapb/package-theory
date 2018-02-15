Set Implicit Arguments.

Require Import Coq.Structures.OrdersEx.
Require Export MSetAux.

Module Type PACKAGE <: OrderedType.
  Parameter t: Set.

  Parameter eq: t -> t -> Prop.
  Parameter lt: t -> t -> Prop.

  Axiom eq_refl: forall x: t, eq x x.
  Axiom eq_sym: forall x y: t, eq x y -> eq y x.
  Axiom eq_trans: forall x y z: t, eq x y -> eq y z -> eq x z.
  Instance eq_equiv : Equivalence eq := Build_Equivalence eq eq_refl eq_sym eq_trans. 
  
  Axiom lt_trans: forall x y z: t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq: forall x y: t, lt x y -> ~ eq x y.
  Axiom lt_strorder: StrictOrder lt.
  Axiom lt_compat : Proper (eq==>eq==>iff) lt.
 
  Parameter compare: t -> t -> comparison.
  Parameter compare_spec : forall s s', CompSpec eq lt s s' (compare s s'). 

  Parameter eq_dec: forall x y, { eq x y } + { ~ eq x y }.
End PACKAGE.

Declare Module Package: PACKAGE.

Module Conflict := PairOrderedType Package Package.

Declare Module PackageSet : MSetInterface.Sets with Module E := Package.
Export PackageSet.
Declare Module ConflictSet : MSetInterface.Sets with Module E := Conflict.

Axiom conflicts_sym: forall (C: ConflictSet.t) (p q: Package.t),
  ConflictSet.In (p, q) C -> ConflictSet.In (q, p) C. 

Axiom conflicts_irrefl: forall (C: ConflictSet.t) (p: Package.t),
  ~ ConflictSet.In (p, p) C.

Module Export PAux := MSetAux.Aux PackageSet.
Export Props.
Export Facts.
Module CAux := Aux ConflictSet.

(* Definition alternative := PackageSet.t. *)

Unset Implicit Arguments.
