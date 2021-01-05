(** * Auxilary Definitions *)

(** Function compition combinators. *)

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C := fun a => g (f a).

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := compose (at level 40, left associativity).

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
