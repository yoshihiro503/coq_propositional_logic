Require Import OrderedType.
Definition t := bool.

Definition eq := @eq bool.

Inductive lt_ : t -> t -> Prop :=
 | BLt : lt_ false true.

Definition lt := lt_.

Lemma eq_refl : forall x : t, eq x x.
Proof. reflexivity. Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. Admitted.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. Admitted.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. Admitted.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. Admitted.

Definition compare : forall (x y: t), Compare lt eq x y.
 intros x y.
 refine (match x, y with
   | true,  true  => EQ _
   | true,  false => GT _
   | false, true  => LT _
   | false, false => EQ _
   end).

 - now apply eq_refl.
 - now constructor.
 - now constructor.
 - now apply eq_refl.
Defined.

Definition eq_dec (x y : t): {eq x y} + {~ eq x y} := Bool.bool_dec x y.


(* Orderes.OrderedType *)
Module OT <: Orders.OrderedType.
  Definition t := t.
  Definition eq := eq.
  Definition lt := lt.
  Program Instance eq_equiv : Equivalence eq.

  Program Instance lt_strorder : StrictOrder lt.
  Obligation 1.
  Admitted.
  Obligation 2.
  Admitted.

  Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Obligation 1.
  Admitted.


  Definition compare (x y: t) :=
    match x, y with
    | true,  true  => Eq
    | true,  false => Gt
    | false, true  => Lt
    | false, false => Eq
    end.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Admitted.

  Definition eq_dec := eq_dec.
End OT.


(* おまけ *)
Definition neq_lt_gt_dec : forall x y, x <> y -> {lt x y} + {lt y x}.
 intros x y Hneq. destruct x, y; [now elim Hneq | now right | now left| now elim Hneq].
Defined.

Axiom lt_irrefl : forall x, ~ lt x x.
