Require Import Coq.Lists.List.
Require Export TypeClassLib.Auxilary.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

(** * Monoid Type Class *)

Class Monoid (A : Type) :=
  { (** The "empty" value. *)
    mempty : A;
    (** "Append". *)
    mappend : A -> A -> A;
    (** Appending [mempty] commutes and is idempotent. *)
    mempty_app_l : forall (a : A), mappend mempty a = a;
    mempty_app_r : forall (a : A), mappend a mempty = a;
    (** Appending is associative. *)
    mappend_assoc : forall (x y z : A),
        mappend (mappend x y) z = mappend x (mappend y z) }.

(** Monid Specification. *)
Module Type MonoidSpec.
  Parameter A : Type.
  Parameter mempty : A.
  Parameter mappend : A -> A -> A.
  Parameter mempty_app_l : forall (a : A), mappend mempty a = a.
  Parameter mempty_app_r : forall (a : A), mappend a mempty = a.
  Parameter mappend_assoc : forall (x y z : A),
      mappend (mappend x y) z = mappend x (mappend y z).
End MonoidSpec.

Module MonoidFactory (MS : MonoidSpec).
  Instance MonoidInstance : Monoid MS.A :=
    { mempty := MS.mempty;
      mappend := MS.mappend;
      mempty_app_l := MS.mempty_app_l;
      mempty_app_r := MS.mempty_app_r;
      mappend_assoc := MS.mappend_assoc }.
End MonoidFactory.

(** Addition of Naturals. *)
Module AdditionMonoidSpec <: MonoidSpec.

  Definition A : Type := nat.

  Definition mempty : nat := 0.

  Definition mappend : nat -> nat -> nat := add.

  Lemma mempty_app_l : forall (a : A), 0 + a = a.
  Proof. lia. Qed.

  Lemma mempty_app_r : forall (a : A), a + 0 = a.
  Proof. lia. Qed.

  Lemma mappend_assoc : forall (x y z : A), x + y + z = x + (y + z).
  Proof. lia. Qed.
End AdditionMonoidSpec.
