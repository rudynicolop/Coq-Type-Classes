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

  Section TMonadSpec.
    Context {M : Type -> Type}.

    Context `{HM : Monad M}.

    Definition fmapt {A B : Type} : (A -> B) -> M A -> M B := fmap.

    Lemma fmap_idt : forall {A : Type},
        fmapt (fun x : A => x) = (fun x : M A => x).
    Proof. intros. unfold fmapt. apply fmap_id. Qed.

    Lemma fmap_composet : forall {A B C : Type} (f : A -> B) (g : B -> C),
        fmapt (g ∘ f) = fmapt g ∘ fmapt f.
    Proof. intros. unfold fmapt. apply fmap_compose. Qed.

    Definition puret {A : Type} : A -> M A := pure.

    Definition fappt {A B : Type} : M (A -> B) -> M A -> M B := fapp.

    Lemma app_identityt : forall {A : Type} (a : M A),
        fappt (puret (fun x => x)) a = a.
    Proof. intros. unfold fappt, puret. apply app_identity. Qed.

    Lemma app_homomorphismt : forall {A B : Type} (f : A -> B) (a : A),
        fappt (puret f) (puret a) = puret (f a).
    Proof. intros. unfold fappt, puret. apply app_homomorphism. Qed.

    Lemma app_interchanget : forall {A B : Type} (f : M (A -> B)) (a : A),
        fappt f (puret a) = fappt (puret (fun h => h a)) f.
    Proof. intros. unfold fappt, puret. apply app_interchange. Qed.

    Lemma app_compositiont :
      forall {A B C : Type} (f : M (A -> B)) (h : M (B -> C)) (a : M A),
        fappt h (fappt f a) =
        fappt (fappt (fappt (puret (@compose A B C)) h) f) a.
    Proof. intros. unfold fappt, puret. apply app_composition. Qed.

    Lemma app_fmap_puret : forall {A B : Type} (f : A -> B),
        fmapt f = fappt (puret f).
    Proof. intros. unfold fmapt, puret. apply app_fmap_pure. Qed.

    Definition bindt {A B : Type} : M A -> (A -> M B) -> M B := bind.

    Lemma pure_leftt : forall {A B : Type} (a : A) (f : A -> M B),
        bindt (puret a) f = f a.
    Proof. unfold bindt, puret. intros. apply pure_left. Qed.

    Lemma pure_rightt : forall {A : Type} (m : M A),
        bindt m puret = m.
    Proof. intros. unfold bindt, puret. apply pure_right. Qed.

    Lemma bind_assoct :
      forall {A B C : Type} (m : M A) (k : A -> M B) (h : B -> M C),
        bindt m (fun a => bindt (k a) h) = bindt (bindt m k) h.
    Proof. intros. unfold bindt. apply bind_assoc. Qed.
  End TMonadSpec.

  Instance TMonad (M : Type -> Type) `{Monad M} : Monad M :=
    { bind := @bindt M _;
      pure_left := @pure_left M _;
      pure_right := @pure_right M _;
      bind_assoc := @bind_assoct M _}.
  (**[]*)

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
