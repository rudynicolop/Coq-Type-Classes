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
(**[]*)

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
Module AddMonoidSpec <: MonoidSpec.
  Definition A : Type := nat.

  Definition mempty : nat := 0.

  Definition mappend : nat -> nat -> nat := add.

  Lemma mempty_app_l : forall (a : nat), 0 + a = a.
  Proof. lia. Qed.

  Lemma mempty_app_r : forall (a : nat), a + 0 = a.
  Proof. lia. Qed.

  Lemma mappend_assoc : forall (x y z : nat), x + y + z = x + (y + z).
  Proof. lia. Qed.
End AddMonoidSpec.

Module AddMonoidFactory := MonoidFactory AddMonoidSpec.
Instance AddMonoid : Monoid nat :=
  AddMonoidFactory.MonoidInstance.
(**[]*)

(** Multiplication of Naturals. *)
Module MulMonoidSpec <: MonoidSpec.
  Definition A : Type := nat.

  Definition mempty : nat := 1.

  Definition mappend : nat -> nat -> nat := mul.

  Lemma mempty_app_l : forall (a : nat), 1 * a = a.
  Proof. lia. Qed.

  Lemma mempty_app_r : forall (a : nat), a * 1 = a.
  Proof. lia. Qed.

  Lemma mappend_assoc : forall (x y z : nat),
      x * y * z = x * (y * z).
  Proof. lia. Qed.
End MulMonoidSpec.

Module MulMonoidFactory := MonoidFactory MulMonoidSpec.
Instance MulMonoid : Monoid nat :=
  MulMonoidFactory.MonoidInstance.
(**[]*)

(** * Parameterized Monoids *)

Module Type ParamMonoidSpec.
  Parameter M : Type -> Type.
  Section Spec.
    Context {A : Type}.
    Parameter mempty : M A.
    Parameter mappend : M A -> M A -> M A.
    Parameter mempty_app_l : forall (m : M A), mappend mempty m = m.
    Parameter mempty_app_r : forall (m : M A), mappend m mempty = m.
    Parameter mappend_assoc : forall (x y z : M A),
      mappend (mappend x y) z = mappend x (mappend y z).
  End Spec.
End ParamMonoidSpec.

Module ParamMonoidFactory (MS : ParamMonoidSpec).
  Instance ParamMonoidInstance (A : Type) : Monoid (MS.M A) :=
    { mempty := @MS.mempty A;
      mappend := @MS.mappend A;
      mempty_app_l := @MS.mempty_app_l A;
      mempty_app_r := @MS.mempty_app_r A;
      mappend_assoc := @MS.mappend_assoc A }.
End ParamMonoidFactory.

(** Lists. *)
Module ListMonoidSpec <: ParamMonoidSpec.
  Import ListNotations.

  Definition M : Type -> Type := list.

  Section Spec.
    Context {A : Type}.

    Definition mempty : list A := [].

    Definition mappend : list A -> list A -> list A := @app A.

    Lemma mempty_app_l : forall (m : list A), [] ++ m = m.
    Proof. reflexivity. Qed.

    Lemma mempty_app_r : forall (m : list A), m ++ [] = m.
    Proof. intros. apply app_nil_r. Qed.

    Lemma mappend_assoc : forall (x y z : list A),
     (x ++ y) ++ z = x ++ (y ++ z).
    Proof. intros. rewrite app_assoc. reflexivity. Qed.
  End Spec.
End ListMonoidSpec.

Module ListMonoidFactory := ParamMonoidFactory ListMonoidSpec.
Instance ListMonoid (A : Type) : Monoid (list A) :=
  ListMonoidFactory.ParamMonoidInstance A.

(** Function Composition. *)
Module ArrowMonoidSpec <: ParamMonoidSpec.
  Definition M : Type -> Type := fun A => A -> A.

  Section Spec.
    Context {A : Type}.

    Definition mempty : A -> A := id.

    Definition mappend : (A -> A) -> (A -> A) -> (A -> A) := compose.

    Lemma mempty_app_l : forall (m : A -> A), id ∘ m = m.
    Proof. intros. reflexivity. Qed.

    Lemma mempty_app_r : forall (m : A -> A), m ∘ id = m.
    Proof. intros. reflexivity. Qed.

    Lemma mappend_assoc : forall (x y z : A -> A),
      x ∘ y ∘ z = x ∘ (y ∘ z).
    Proof. intros. reflexivity. Qed.
  End Spec.
End ArrowMonoidSpec.

Module ArrowMonoidFactory := ParamMonoidFactory ArrowMonoidSpec.
Instance ArrowMonoid (A : Type) : Monoid (A -> A) :=
  ArrowMonoidFactory.ParamMonoidInstance A.
(**[]*)
