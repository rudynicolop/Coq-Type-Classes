Require Export Coq.Logic.FunctionalExtensionality.
Require Coq.Lists.List.

(** * Auxilary Definitions *)

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C := fun a => g (f a).

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := compose (at level 40, left associativity).

(** * Functor Typeclass *)

Class Functor (F : Type -> Type) : Type :=
  {
    fmap {A B : Type} : (A -> B) -> F A -> F B;
    (** Laws *)
    fmap_id : forall {A : Type},
        fmap (fun x : A => x) = (fun x : F A => x);
    fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
        fmap (g ∘ f) = (fmap g) ∘ (fmap f)
  }.

(** * Identity *)
Module FIdentity.
  Definition I : Type -> Type := fun t => t.

  Definition fmap' {A B : Type} (f : A -> B) (a : I A) : I B := f a.

  Arguments fmap' {A B}.

  Lemma fmap_id' : forall (A : Type),
      fmap' (fun x : A => x) = (fun x : I A => x).
  Proof. intros. unfold fmap', I. reflexivity. Qed.

  Lemma fmap_compose' : forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap' (g ∘ f) = (fmap' g) ∘ (fmap' f).
  Proof. intros. unfold fmap', compose. reflexivity. Qed.

  Instance IdentityFunctor : Functor I :=
    { fmap _ _ := fmap'; fmap_id := fmap_id'; fmap_compose := fmap_compose' }.

  Compute fmap S 4.
End FIdentity.

(** * Option *)
Module FOption.
  Definition fmap' {A B : Type} (f : A -> B) (oa : option A) :=
    match oa with
    | None   => None
    | Some a => Some (f a)
    end.

  Lemma fmap_id' : forall (A : Type),
      fmap' (fun x : A => x) = (fun x : option A => x).
  Proof.
    intros. unfold fmap'. extensionality oa.
    destruct oa as [a |]; reflexivity.
  Qed.

  Lemma fmap_compose' : forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap' (g ∘ f) = (fmap' g) ∘ (fmap' f).
  Proof.
    intros. unfold fmap', compose.
    extensionality oa. destruct oa as [a |]; reflexivity.
  Qed.

  Instance OptionFunctor : Functor option :=
    { fmap _ _ := fmap'; fmap_id := fmap_id'; fmap_compose := fmap_compose' }.

  Compute fmap S None.
  Compute fmap S (Some 41).
End FOption.

(** * List *)
Module FList.
  Import Coq.Lists.List.
  Import ListNotations.

  Lemma fmap_id' : forall (A : Type),
      map (fun x : A => x) = (fun x : list A => x).
  Proof.
    intros. extensionality l.
    Search (map (fun x => x)). rewrite map_id. reflexivity.
  Qed.

  Lemma fmap_compose' : forall (A B C : Type) (f : A -> B) (g : B -> C),
      map (g ∘ f) = (map g) ∘ (map f).
  Proof.
    intros. extensionality l.
    induction l as [| h t IHt]; auto.
    cbn. rewrite IHt. unfold compose. reflexivity.
  Qed.

  Instance ListFunctor : Functor list :=
    { fmap := map; fmap_id := fmap_id'; fmap_compose := fmap_compose' }.
End FList.
