Require Import Coq.Lists.List.
Require Export TypeClassLib.Monoid.

(** * The Foldable Class *)

Class Foldable (T : Type -> Type) :=
  { foldr : forall {A B : Type}, (A -> B -> B) -> B -> T A -> B; }.

Definition foldMap {T : Type -> Type} `{Foldable T}
           {A M : Type} `{Monoid M}
           (f : A -> M) (t : T A) : M :=
  foldr (mappend ∘ f) mempty t.
(**[]*)

Definition fold {T : Type -> Type} `{Foldable T}
           {M : Type} `{Monoid M} (t : T M) : M := foldMap id t.
(**[]*)
