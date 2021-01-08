Require Export Coq.Logic.FunctionalExtensionality.

(** * Auxilary Definitions *)

(** Function compition combinators. *)

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C := fun a => g (f a).

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := compose (at level 40, left associativity).

Definition uncurry {A B C : Type} (f : A -> B -> C) : A * B -> C :=
  fun '(a,b) => f a b.
(**[]*)

Definition curry {A B C : Type} (f : A * B -> C) : A -> B -> C :=
  fun a b => f (a, b).
(**[]*)

Fact curry_uncurry : forall {A B C : Type} (f : A -> B -> C),
    curry (uncurry f) = f.
Proof. intros. reflexivity. Qed.

Fact uncurry_curry : forall {A B C : Type} (f : A * B -> C),
    uncurry (curry f) = f.
Proof. intros. extensionality ab. destruct ab; reflexivity. Qed.

Lemma f_2_arg :
  forall {A B C : Type}
    (f : A -> B -> C) (a1 a2 : A) (b : B),
    a1 = a2 -> f a1 b = f a2 b.
Proof. intros; subst; reflexivity. Qed.

(** The Either data type. *)
Inductive either (A B : Type) : Type :=
| Left  (a : A)
| Right (b : B).

Arguments Left  {A} {B}.
Arguments Right {A} {B}.

(** Binary Trees. *)
Inductive tree (K V : Type) :=
| Leaf
| Node (k : K) (v : V) (l r : tree K V).

Arguments Leaf {K} {V}.
Arguments Node {K} {V}.

(** Because Coq disallows
    Modules parameterized by types... *)
Module Type TypeParam.
  Parameter T : Type.
End TypeParam.

(** State. *)
Definition state (S A : Type) : Type := S -> A * S.

(** Continuations. *)
Definition cont (R A : Type) : Type := (A -> R) -> R.

(** Ternary Trees (just for fun) *)
Inductive ternary (A : Type) : Type :=
| LF
| N2 (a : A) (l r : ternary A)
| N3 (x y : A) (l m r : ternary A).

Arguments LF {A}.
Arguments N2 {A}.
Arguments N3 {A}.
