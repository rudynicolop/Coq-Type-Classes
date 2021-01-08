Require Import Coq.Lists.List.
Require Export TypeClassLib.Applicative.
Require Export TypeClassLib.Foldable.

Lemma fapp_compose :
  forall {F : Type -> Type} `{Applicative F} {A B C : Type}
    (f : A -> B) (h : B -> C),
    fapp (pure (h ∘ f)) = fapp (pure h) ∘ fapp (pure f).
Proof.
  intros. repeat rewrite <- app_fmap_pure.
  apply fmap_compose.
Qed.

Lemma fapp_compose_unfolded :
  forall {F : Type -> Type} `{FA : Applicative F} {A B C : Type}
    (f : A -> B) (h : B -> C) (t : F A),
    fapp (pure (fun a => h (f a))) t = fapp (pure h) ((fapp (pure f)) t).
Proof.
  intros. pose proof fapp_compose f h as H.
  unfold compose in H. rewrite H. reflexivity.
Qed.

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

  (** Applicative Requirement. *)
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

(** Lists. *)
Module ListTraversableSpec <: TraversableSpec.
  Import Coq.Lists.List.
  Import ListNotations.

  Definition T : Type -> Type := list.

  Definition TApplicative : Applicative list := ListApplicative.

  Definition TFoldable : Foldable list := ListFoldable.

  Fixpoint traverse {F : Type -> Type} `{Applicative F}
           {A B : Type} (f : A -> F B) (l : list A) : F (list B) :=
    match l with
    | []    => pure []
    | a :: l => cons <$> f a <*> traverse f l
    end.
  (**[]*)

  Lemma traverse_id : forall {A : Type},
      @traverse (fun X => X) IdentityApplicative _ _
                (fun a : A => a) = fun t : list A => t.
  Proof.
    intros. extensionality t.
    induction t as [| h t IHt]; simpl; auto.
    rewrite IHt. reflexivity.
  Qed.
  (**[]*)

  (** This is true in my heart of hearts. *)
  Axiom switch_fun_args_app :
    forall {F : Type -> Type} `{Applicative F}
      {A B C : Type} (f : A -> B -> C) (a : F A) (b : F B),
      (fun x y => f x y) <$> a <*> b = (fun y x => f x y) <$> b <*> a.

  (** Traversals compose. *)
  Lemma traverse_compose :
    forall {Q R : Type -> Type} `{QA : Applicative Q} `{RA : Applicative R}
      {A B C : Type} (f : A -> Q B) (h : B -> R C),
      @traverse (Q ∘ R) _ _ _ (@fmap Q _ B (R C) h ∘ f) =
      @fmap Q _ (list B) (R (list C)) (@traverse R _ B C h) ∘ (@traverse Q _ A B f).
  Proof.
    intros. extensionality t.
    induction t as [| a t IHt]; simpl.
    - unfold purec. unfold compose. cbn.
      rewrite app_fmap_pure. rewrite app_homomorphism.
      reflexivity.
    - rewrite IHt; clear IHt.
      unfold fappc, fmapc. unfold compose. cbn.
      repeat rewrite app_fmap_pure.
      rewrite app_composition with (h0 := pure (fapp (pure cons))).
      rewrite app_composition with (h0 := pure (traverse h)).
      rewrite app_composition with (f0 := pure (traverse h)).
      rewrite app_composition with (h0 := pure fapp).
      apply f_2_arg. clear t. repeat rewrite app_homomorphism.
      repeat rewrite app_composition with (a0 := f a).
      repeat rewrite app_homomorphism.
      repeat rewrite fapp_compose. unfold compose.
      rewrite app_composition with (f0 := pure cons).
      rewrite app_composition with (f0 := pure h). rewrite app_composition.
      repeat rewrite app_homomorphism. unfold compose. cbn.
      rewrite app_fmap_pure. rewrite app_composition.
      repeat rewrite app_homomorphism. unfold compose.
      repeat rewrite <- app_fmap_pure.
      pose proof switch_fun_args_app
          (fun x y a1 => cons <$> h x <*> y a1) (f a) (pure (traverse h)) as H.
      simpl in H. rewrite H. rewrite app_fmap_pure.
      rewrite app_homomorphism. rewrite <- app_fmap_pure. reflexivity.
  Qed.
End ListTraversableSpec.

Module ListTraversableFactory := TraversableFactory ListTraversableSpec.
Instance ListTraversable : Traversable list :=
  ListTraversableFactory.TraversableInstance.
(**[]*)
