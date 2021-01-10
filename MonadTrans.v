Require Coq.Lists.List.
Require Export TypeClassLib.Monad.

(** * The Monad Transformer Type Class *)

Class MonadTrans
      (T : (Type -> Type) -> Type -> Type) :=
  { (** Monadic Substructure *)
    Trans_Monad :> forall (M : Type -> Type) `{Monad M}, Monad (T M);
    lift : forall {M : Type -> Type} `{Monad M}
             {A : Type}, M A -> T M A;
    (** Lift with pure is idempotent. *)
    lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
        @lift M _ A ∘ (@pure M _ A) = @pure (T M) _ A;
    (** Lift composes with bind. *)
    lift_bind : forall {M : Type -> Type} `{Monad M}
                  {A B : Type} (m : M A) (f : A -> M B),
        lift (bind m f) = bind (lift m) (lift ∘ f); }.
(**[]*)

(** Specification. *)
Module Type MonadTransSpec.
  Parameter T : (Type -> Type) -> Type -> Type.

  Parameter TMonad : forall (M : Type -> Type) `{Monad M}, Monad (T M).

  Parameter lift : forall {M : Type -> Type} `{Monad M}
                     {A : Type}, M A -> T M A.
  (**[]*)

  Axiom lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
      @lift M _ A ∘ (@pure M _ A) =
      @pure (T M) (@Monad_Applicative (T M) (TMonad M)) A.
  (**[]*)

  Axiom lift_bind : forall {M : Type -> Type} `{Monad M}
                          {A B : Type} (m : M A) (f : A -> M B),
      lift (bind m f) = @bind (T M) (TMonad M) _ _ (lift m) (lift ∘ f).
  (**[]*)
End MonadTransSpec.

Module MonadTransFactory (MS : MonadTransSpec).
  Include MS.

  Instance MonadTransInstance : MonadTrans MS.T :=
    { lift := @MS.lift;
      lift_pure := @MS.lift_pure;
      lift_bind := @MS.lift_bind }.
  (**[]*)
End MonadTransFactory.

(** Identity. *)
Module IdentityMonadTransSpec <: MonadTransSpec.
  Definition T : (Type -> Type) -> Type -> Type := fun M => M.

  Instance TMonad (M : Type -> Type) `{HM : Monad M} : Monad M := HM.

  Definition lift {M : Type -> Type} `{Monad M}
             {A : Type} : M A -> M A := fun m => m.
  (**[]*)

  Lemma lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
      @lift M _ A ∘ (@pure M _ A) =
      @pure M (@Monad_Applicative M (TMonad M)) A.
  Proof. intros. unfold lift. extensionality m. reflexivity. Qed.

  Lemma lift_bind : forall {M : Type -> Type} `{Monad M}
                      {A B : Type} (m : M A) (f : A -> M B),
      lift (bind m f) = @bind M (TMonad M) _ _ (lift m) (lift ∘ f).
  Proof. intros. reflexivity. Qed.
End IdentityMonadTransSpec.

Module IdentityMonadTransFactory :=
  MonadTransFactory IdentityMonadTransSpec.
Instance IdentityMonadTrans : MonadTrans (fun M : Type -> Type => M) :=
  IdentityMonadTransFactory.MonadTransInstance.
(**[]*)

(** Option. *)
Module OptionMonadTransSpec <: MonadTransSpec.
  Definition T (M : Type -> Type) : Type -> Type := M ∘ option.

  Instance TApplicative (M : Type -> Type)
           `{HM : Monad M} : Applicative (M ∘ option) :=
    ComposeApplicative option M.
  (**[]*)

  Section TMonadSpec.
    Context {M : Type -> Type}.

    Context `{HM : Monad M}.

    Definition bindt {A B : Type}
               (m : M (option A)) (f : A -> M (option B)) : M (option B) :=
      o <- m ;;
      match o with
      | None   => pure None
      | Some a => (f a)
      end.
    (**[]*)

    Lemma pure_leftt : forall {A B : Type} (a : A) (f : A -> M (option B)),
        bindt (@pure (M ∘ option) _ A a) f = f a.
    Proof.
      intros. pose proof @pure_left M HM (option A) (option B) as H.
      unfold bindt. simpl. unfold purec. unfold compose.
      rewrite H. simpl. reflexivity.
    Qed.

    Lemma pure_rightt : forall {A : Type} (m : M (option A)),
      bindt m (@pure (M ∘ option) _ A) = m.
    Proof.
      intros. unfold bindt. simpl. unfold purec.
      unfold compose.
      assert (H : (fun o : option A =>
                     match o with
                     | Some a => @pure M _ _ (@pure option _ _ a)
                     | None => @pure M _ _ None
                     end) = (fun o : option A =>
                               @pure M _ _
                                     (match o with
                                      | Some a => @pure option _ _ a
                                      | None => None
                                      end))).
      { extensionality o; destruct o; auto. }
      rewrite H; clear H.
      assert (H : (fun o : option A =>
                     @pure M _ _
                           match o with
                           | Some a => pure a
                           | None => None
                           end) =
                  (fun o : option A => @pure M _ _ o)).
      { extensionality o; destruct o; auto. }
      rewrite H. apply pure_right.
    Qed.

    Lemma bind_assoct :
      forall {A B C : Type} (m : M (option A))
        (k : A -> M (option B)) (h : B -> M (option C)),
        bindt m (fun a => bindt (k a) h) = bindt (bindt m k) h.
    Proof.
      intros. unfold bindt.
      rewrite <- (@bind_assoc M). apply f_equal.
      extensionality o. destruct o as [a |]; auto.
      Search pure. rewrite pure_left. reflexivity.
    Qed.
  End TMonadSpec.

  Instance TMonad : forall (M : Type -> Type) `{Monad M}, Monad (M ∘ option) :=
    { bind := @bindt M _;
      pure_left := @pure_leftt M _;
      pure_right := @pure_rightt M _;
      bind_assoc := @bind_assoct M _; }.
  (**[]*)

  Definition lift {M : Type -> Type} `{Monad M}
             {A : Type} (m : M A) : M (option A) :=
    @fmap M _ _ _ (@pure option _ _) m.
  (**[]*)

  Lemma lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
      @lift M _ A ∘ (@pure M _ A) =
      @pure (M ∘ option) (@Monad_Applicative (M ∘ option) (TMonad M)) A.
  Proof.
    intros. extensionality a. unfold compose, lift.
    cbn. unfold purec. unfold compose, OptionMonadSpec.pure.
    simpl. unfold OptionMonadSpec.pure.
    Search fmap. rewrite app_fmap_pure.
    apply app_homomorphism.
  Qed.
  (**[]*)

  Lemma lift_bind : forall {M : Type -> Type} `{Monad M}
                      {A B : Type} (m : M A) (f : A -> M B),
      lift (bind m f) =
      @bind (M ∘ option) (TMonad M) _ _ (lift m) (lift ∘ f).
  Proof.
    intros. unfold compose. simpl. unfold lift.
  Admitted.
End OptionMonadTransSpec.
