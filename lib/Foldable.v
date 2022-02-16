Require Import Coq.Lists.List.
Require Export TypeClasses.Monoid.

(** * The Foldable Class *)

Class Foldable (T : Type -> Type) :=
  { foldr : forall {A B : Type}, (B -> A -> A) -> A -> T B -> A;
    foldl : forall {A B : Type}, (A -> B -> A) -> A -> T B -> A }.
(**[]*)

Definition foldMap {T : Type -> Type} `{Foldable T}
           {A M : Type} `{Monoid M}
           (f : A -> M) (t : T A) : M :=
  foldr (mappend ∘ f) mempty t.
(**[]*)

Definition fold {T : Type -> Type} `{Foldable T}
           {M : Type} `{Monoid M} (t : T M) : M := foldMap id t.
(**[]*)

Instance IdentityFoldable : Foldable (fun X => X) :=
  { foldr _ _ f a b := f b a; foldl _ _ f a b := f a b }.

Definition fold_option {A B : Type}
           (f : B -> A -> A) (a : A) (t : option B) : A :=
  match t with
  | None   => a
  | Some b => f b a
  end.
(**[]*)

Instance OptionFoldable : Foldable option :=
  { foldr _ _ f := fold_option f;
    foldl _ _ f := fold_option (fun a b => f b a) }.
(**[]*)

Instance ListFoldable : Foldable list :=
  { foldr := fold_right; foldl _ _ f a l := fold_left f l a }.
(**[]*)

(** Binary Trees. *)

Fixpoint foldr_tree {A K V : Type}
         (f : K -> V -> A -> A) (a : A) (t : tree K V) : A :=
  match t with
  | Leaf         => a
  | Node k v l r => foldr_tree f (f k v (foldr_tree f a r)) l
  end.
(**[]*)

Fixpoint foldl_tree {A K V : Type}
         (f : A -> K -> V -> A) (a : A) (t : tree K V) : A :=
  match t with
  | Leaf         => a
  | Node k v l r => foldl_tree f (f (foldl_tree f a l) k v) r
  end.
(**[]*)

(** Note that this instance ignores keys. *)
Instance TreeFoldable (K : Type) : Foldable (tree K) :=
  { foldr A V f := @foldr_tree A K V (fun _ => f);
    foldl A V f := @foldl_tree A K V (fun a _ => f a) }.
(**[]*)

(** Ternary Trees. *)

Fixpoint foldr_ternary {A B : Type}
         (f : B -> A -> A) (a : A) (t : ternary B) : A :=
  match t with
  | LF           => a
  | N2 b l r     => foldr_ternary f (f b (foldr_ternary f a r)) r
  | N3 x y l m r => foldr_ternary f (f x (foldr_ternary f (f y (foldr_ternary f a r)) m)) l
  end.
(**[]*)

Fixpoint foldl_ternary {A B : Type}
         (f : A -> B -> A) (a : A) (t : ternary B) : A :=
  match t with
  | LF           => a
  | N2 b l r     => foldl_ternary f (f (foldl_ternary f a l) b) r
  | N3 x y l m r => foldl_ternary f (f (foldl_ternary f (f (foldl_ternary f a l) x) m) y) r
  end.
(**[]*)

Instance TernaryFoldable : Foldable ternary :=
  { foldr := @foldr_ternary; foldl := @foldl_ternary }.
(**[]*)
