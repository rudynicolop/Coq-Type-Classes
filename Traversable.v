Require Import Coq.Lists.List.
Require Export TypeClassLib.Applicative.
Require Export TypeClassLib.Foldable.

(** * The Traversable Type Class *)
Class Traversable (T : Type -> Type) `{Functor T} `{Foldable T} :=
  { traverse : forall {F : Type -> Type} `{Applicative F}
                 {A B : Type}, (A -> F B) -> T A -> F (T B);
    (** Laws. *)
    traverse_id : forall {A : Type},
        @traverse (fun X : Type => X) IdentityFunctor _ _ _
                  (fun a : A => a) = fun t : T A => t;
    (* traverse_compose :
      forall {Q R : Type -> Type} `{Applicative Q} {Applicative R}
        {A B C : Type} (f : A -> Q B) (h : B -> R C),
        traverse (fmap h ∘ f) =
        fmap (@traverse R _ _ _ _ h) ∘ (@traverse Q _ _ _ _ f) *)
    }.
(**[]*)

Print Traversable.

Module Type TraversableSpec.
  (** The Traversable. *)
  Parameter T : Type -> Type.

  (** Functor Requirement. *)
  Parameter TFunctor : Functor T.

  (** Foldable Requirement. *)
  Parameter TFoldable : Foldable T.

  Parameter traverse : forall {A : Type -> Type} `{Applicative A}
                         {B C : Type}, (B -> A C) -> T B -> A (T C).
  (**[]*)

  (** Laws. *)

  (** The "identity" traversal. *)
  Parameter traverse_id : forall {B : Type},
      @traverse (fun X => X) IdentityFunctor _ _ _
                (fun b : B => b) = fun t : T B => t.
  (**[]*)

  (** Traversals compose. *)
  (* Parameter traverse_compose :
    forall {A : Type -> Type} `{Applicative A}
      {B C D : Type} (f : B -> A C) (h : C -> A D),
      traverse (fmap h ∘ f) = fmap (traverse h) ∘ (traverse f). *)
  (**[]*)
End TraversableSpec.

Module TraversableFactory (TS : TraversableSpec).
  Instance TFunctor : Functor TS.T := TS.TFunctor.
  Instance TFoldable : Foldable TS.T := TS.TFoldable.

  Instance TraversableInstance : Traversable TS.T :=
  { traverse := @TS.traverse;
    traverse_id := @TS.traverse_id;
    (* traverse_compose := @TS.traverse_compose *)
  }.
End TraversableFactory.

(** Identity. *)
Module IdentityTraversableSpec <: TraversableSpec.
  Definition T : Type -> Type := (fun X => X).

  Definition TFunctor : Functor T := IdentityFunctor.

  Definition TFoldable : Foldable T := IdentityFoldable.

  Definition traverse {A : Type -> Type} `{Applicative A}
             {B C : Type} (f : B -> A C) : B -> A C := f.
  (**[]*)

  Lemma traverse_id : forall {B : Type},
      @traverse (fun X => X) IdentityFunctor _ _ _
                (fun b : B => b) = (fun b : B => b).
  Proof. intros. reflexivity. Qed.
  (**[]*)

  (* Lemma traverse_compose :
    forall {A : Type -> Type} `{Applicative A}
      {B C D : Type} (f : B -> A C) (h : C -> A D),
      traverse (fmap h ∘ f) = fmap (traverse h) ∘ (traverse f).
  Proof. intros. unfold traverse. reflexivity. Qed. *)
  (**[]*)
End IdentityTraversableSpec.

Module IdentityTraversableFactory := TraversableFactory IdentityTraversableSpec.
Instance IdentityTraversable : Traversable (fun X => X) :=
  IdentityTraversableFactory.TraversableInstance.
(**[]*)

(** Option. *)
Module OptionTraversableSpec <: TraversableSpec.
  Definition T : Type -> Type := option.

  Instance TFunctor : Functor option := OptionFunctor.

  Instance TFoldable : Foldable option := OptionFoldable.

  Definition traverse {A : Type -> Type} `{Applicative A} {B C : Type}
             (f : B -> A C) (o : option B) : A (option C) :=
    match o with
    | None   => pure None
    | Some b => Some <$> f b
    end.
  (**[]*)

  Lemma traverse_id : forall {B : Type},
      @traverse (fun X => X) IdentityFunctor _ _ _
                (fun b : B => b) = (fun o : option B => o).
  Proof. intros. extensionality o. destruct o; auto. Qed.

  (*Lemma traverse_compose :
    forall {A : Type -> Type} `{Applicative A}
      {B C D : Type} (f : B -> A C) (h : C -> A D),
      traverse (fmap h ∘ f) = fmap (traverse h) ∘ (traverse f).
  Proof.
    intros. extensionality o. destruct o as [b |]; simpl.
    - unfold fmap. *)
End OptionTraversableSpec.

Module OptionTraversableFactory := TraversableFactory OptionTraversableSpec.
Instance OptionTraversable : Traversable option :=
  OptionTraversableFactory.TraversableInstance.
(**[]*)
