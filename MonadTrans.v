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

  Parameter lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
      @lift M _ A ∘ (@pure M _ A) =
      @pure (T M) (@Monad_Applicative (T M) (TMonad M)) A.
  (**[]*)

  Parameter lift_bind : forall {M : Type -> Type} `{Monad M}
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
