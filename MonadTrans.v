Require Coq.Lists.List.
Require Export TypeClassLib.Monad.


(** Example. *)
Definition optionT (M : Type -> Type) (A : Type) := M (option A).

Module OptionTFunctorSpec (MS : MonadSpec) <: FunctorSpec.
  Definition M := MS.M.

  Definition F : Type -> Type := optionT M.

  Definition fmap {A B : Type} (f : A -> B) (m : optionT M A) : optionT M B :=
    MS.fmap (OptionFunctorSpec.fmap f) m.

  Lemma fmap_id : forall {A : Type},
      fmap (fun x : A => x) = (fun x : optionT M A => x).
  Proof.
    intros. unfold fmap.
    rewrite OptionFunctorSpec.fmap_id.
    apply MS.fmap_id.
  Qed.

  Lemma fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
      fmap (g ∘ f) = fmap g ∘ fmap f.
  Proof.
    intros. unfold fmap.
    rewrite OptionFunctorSpec.fmap_compose.
    rewrite MS.fmap_compose. reflexivity.
  Qed.
End OptionTFunctorSpec.


(* Instance OptionTFunctor (M : Type -> Type) `{Monad M} : Functor (optionT M) :=
  { fmap _ _ := ; }. *)

(** * The Monad Transformer Type Class *)

(* TODO: Confusing to properly generalize...
Class MonadTrans
      (T : (Type -> Type) -> Type -> Type)
      (M : Type -> Type) `{Monad M} :=
  { lift : forall {A : Type}, M A -> T M A;
    MonadTrans_Monad :> Monad (T M);
  }.
    lift_bind : forall {A B : Type} (m : M A) (f : A -> M B),
        lift (bind m f) = bind (lift m) (lift ∘ f);
  }. *)
