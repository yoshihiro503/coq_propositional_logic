Require Import OrderedType.
Require Import String.
Definition T := nat.

Definition eq_dec : forall (x y:T), {x=y}+{x<>y} :=
  Peano_dec.eq_nat_dec.

Definition lt : T -> T -> Prop := lt.

(* Orderes.OrderedType *)
Module OT <: Orders.OrderedType.
  Definition t := T.
  Definition eq := @eq t.
  Definition lt := lt.
  Program Instance eq_equiv : Equivalence eq | 10.

  Program Instance lt_strorder : StrictOrder lt.

  Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Obligation 1.
  Admitted.

  Definition compare : t -> t -> comparison := Compare_dec.nat_compare.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Admitted.

  Definition eq_dec := eq_dec.
End OT.

Require Import Orders.
(*
Module VarOrder <: TotalLeBool.
  Definition t := T.
  Variable leb : t -> t -> bool.
  Infix "<=?" := leb (at level 35).
  Theorem leb_total : forall a1 a2, a1 <=? a2 = true \/ a2 <=? a1 = true.
  Admitted.
End VarOrder.
*)

Require Mergesort.
Module VarOrder <: TotalLeBool := Mergesort.NatOrder.

(* おまけ *)
Variable neq_lt_gt_dec : forall x y, x <> y -> {lt x y} + {lt y x}.
Axiom lt_irrefl : forall x, ~ lt x x.
