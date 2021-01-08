Require Import Coq.Lists.List.
Require Export TypeClassLib.Applicative.
Require Export TypeClassLib.Foldable.

(** * The Traversable Type Class *)
Class Traversable (T : Type -> Type) :=
  { Traversable_Applicative :> Applicative T;
    Traversable_Foldable :> Foldable T;
    traverse : forall {F : Type -> Type} `{Applicative F}
                 {A B : Type}, (A -> F B) -> T A -> F (T B);
    (** Laws. *)
    traverse_id : forall {A : Type},
        @traverse (fun X : Type => X) IdentityApplicative _ _
                  (fun a : A => a) = fun t : T A => t;
    traverse_compose :
      forall {Q R : Type -> Type} `{Applicative Q} `{Applicative R}
        {A B C : Type} (f : A -> Q B) (h : B -> R C),
        @traverse (Q ∘ R) _ _ _ (@fmap Q _ B (R C) h ∘ f) =
        @fmap Q _ (T B) (R (T C)) (@traverse R _ B C h) ∘ (@traverse Q _ A B f) }.
(**[]*)

Module Type TraversableSpec.
  (** The Traversable. *)
  Parameter T : Type -> Type.

  (** Functor Requirement. *)
  Parameter TApplicative : Applicative T.

  (** Foldable Requirement. *)
  Parameter TFoldable : Foldable T.

  Parameter traverse : forall {F : Type -> Type} `{Applicative F}
                         {A B : Type}, (A -> F B) -> T A -> F (T B).
  (**[]*)

  (** Laws. *)

  (** The "identity" traversal. *)
  Parameter traverse_id : forall {A : Type},
      @traverse (fun X => X) IdentityApplicative _ _
                (fun a : A => a) = fun t : T A => t.
  (**[]*)

  (** Traversals compose. *)
  Parameter traverse_compose :
    forall {Q R : Type -> Type} `{Applicative Q} `{Applicative R}
      {A B C : Type} (f : A -> Q B) (h : B -> R C),
      @traverse (Q ∘ R) _ _ _ (@fmap Q _ B (R C) h ∘ f) =
      @fmap Q _ (T B) (R (T C)) (@traverse R _ B C h) ∘ (@traverse Q _ A B f).
  (**[]*)
End TraversableSpec.

Module TraversableFactory (TS : TraversableSpec).
  Instance TApplicative : Applicative TS.T := TS.TApplicative.
  Instance TFoldable : Foldable TS.T := TS.TFoldable.

  Instance TraversableInstance : Traversable TS.T :=
  { traverse := @TS.traverse;
    traverse_id := @TS.traverse_id;
    traverse_compose := @TS.traverse_compose }.
End TraversableFactory.

(** Identity. *)
Module IdentityTraversableSpec <: TraversableSpec.
  Definition T : Type -> Type := (fun X => X).

  Definition TApplicative : Applicative T := IdentityApplicative.

  Definition TFoldable : Foldable T := IdentityFoldable.

  Definition traverse {F : Type -> Type} `{Applicative F}
             {A B : Type} (f : A -> F B) : A -> F B := f.
  (**[]*)

  Lemma traverse_id : forall {A : Type},
      @traverse (fun X => X) IdentityApplicative _ _
                (fun a : A => a) = (fun a : A => a).
  Proof. intros. reflexivity. Qed.
  (**[]*)

  Lemma traverse_compose :
    forall {Q R : Type -> Type} `{Applicative Q} `{Applicative R}
      {A B C : Type} (f : A -> Q B) (h : B -> R C),
      @traverse (Q ∘ R) _ _ _ (@fmap Q _ B (R C) h ∘ f) =
      @fmap Q _ B (R C) (@traverse R _ B C h) ∘ (@traverse Q _ A B f).
    Proof. intros. reflexivity. Qed.
  (**[]*)
End IdentityTraversableSpec.

Module IdentityTraversableFactory := TraversableFactory IdentityTraversableSpec.
Instance IdentityTraversable : Traversable (fun X => X) :=
  IdentityTraversableFactory.TraversableInstance.
(**[]*)

(** Option. *)
Module OptionTraversableSpec <: TraversableSpec.
  Definition T : Type -> Type := option.

  Instance TApplicative : Applicative option := OptionApplicative.

  Instance TFoldable : Foldable option := OptionFoldable.

  Definition traverse {F : Type -> Type} `{Applicative F} {A B : Type}
             (f : A -> F B) (o : option A) : F (option B) :=
    match o with
    | None   => pure None
    | Some a => Some <$> f a
    end.
  (**[]*)

  Lemma traverse_id : forall {A : Type},
      @traverse (fun X => X) IdentityApplicative _ _
                (fun a : A => a) = (fun o : option A => o).
  Proof. intros. extensionality o. destruct o; auto. Qed.

  Lemma traverse_compose :
    forall {Q R : Type -> Type} `{Applicative Q} `{Applicative R}
      {A B C : Type} (f : A -> Q B) (h : B -> R C),
      @traverse (Q ∘ R) _ _ _ (@fmap Q _ B (R C) h ∘ f) =
      @fmap Q _ (option B) (R (option C))
            (@traverse R _ B C h) ∘ (@traverse Q _ A B f).
  Proof.
    intros. extensionality o. destruct o; simpl.
    - unfold fmapc. unfold compose. cbn.
      repeat rewrite app_fmap_pure.
      repeat rewrite app_composition. apply f_2_arg.
      repeat rewrite app_homomorphism. unfold compose.
      unfold traverse. rewrite app_fmap_pure. reflexivity.
    - unfold purec. unfold compose. cbn.
      rewrite app_fmap_pure. rewrite app_homomorphism.
      reflexivity.
  Qed.
End OptionTraversableSpec.

Module OptionTraversableFactory := TraversableFactory OptionTraversableSpec.
Instance OptionTraversable : Traversable option :=
  OptionTraversableFactory.TraversableInstance.
(**[]*)
