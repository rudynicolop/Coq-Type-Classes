Require Import Coq.Lists.List.
Require Export TypeClassLib.Monoid.

(** * The Foldable Class *)

Class Foldable (T : Type -> Type) :=
  { foldr : forall {A B : Type}, (B -> A -> A) -> A -> T B -> A;
    foldl : forall {A B : Type}, (A -> B -> A) -> A -> T B -> A }.

Definition foldMap {T : Type -> Type} `{Foldable T}
           {A M : Type} `{Monoid M}
           (f : A -> M) (t : T A) : M :=
  foldr (mappend ∘ f) mempty t.
(**[]*)

Definition fold {T : Type -> Type} `{Foldable T}
           {M : Type} `{Monoid M} (t : T M) : M := foldMap id t.
(**[]*)

Instance ListFoldable : Foldable list :=
  { foldr := fold_right; foldl _ _ f a l := fold_left f l a }.

(** Binary Trees. *)

Fixpoint foldr_tree {A K V : Type}
         (f : K -> V -> A -> A) (a : A) (t : tree K V) : A :=
  match t with
  | Leaf         => a
  | Node k v l r => foldr_tree f (f k v (foldr_tree f a r)) l
  end.

Fixpoint foldl_tree {A K V : Type}
         (f : A -> K -> V -> A) (a : A) (t : tree K V) : A :=
  match t with
  | Leaf         => a
  | Node k v l r => foldl_tree f (f (foldl_tree f a l) k v) r
  end.

(** Note that this instance ignores keys. *)
Instance TreeFoldable {K : Type} : Foldable (tree K) :=
  { foldr A V f := @foldr_tree A K V (fun _ => f);
    foldl A V f := @foldl_tree A K V (fun a _ => f a) }.
