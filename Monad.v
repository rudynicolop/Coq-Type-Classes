Require Coq.Lists.List.
Require Export TypeClassLib.Applicative.

(** * The Monad Type Class *)
Class Monad (M : Type -> Type) `{Applicative M} :=
  { bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    (** Laws. *)
    pure_left : forall {A B : Type} (a : A) (f : A -> M B),
        bind (pure a) f = f a;
    pure_right : forall {A : Type} (m : M A),
        bind m pure = m;
    bind_assoc : forall {A B C : Type} (m : M A) (k : A -> M B) (h : B -> M C),
        bind m (fun a => bind (k a) h) = bind (bind m k) h }.

(** Haskellites will note the absence of [return : A -> M A].
    [return] has been substituted with [pure] to streamline
    the definitions in the spirit of this proposal:
    [https://gitlab.haskell.org/ghc/ghc/-/wikis/proposal/monad-of-no-return] *)

Infix ">>=" := bind (at level 43, left associativity).

Notation "a <- ma ;; mb" := (bind ma (fun a => mb)) (at level 100, right associativity).

(** * Monad Specification *)
Module Type MonadSpec <: ApplicativeSpec.
  Include ApplicativeSpec.
  Definition M : Type -> Type := F.

  Parameter bind : forall {A B : Type}, M A -> (A -> M B) -> M B.

  (** Laws. *)

  (** Promontion to a Monad has no effect. *)
  Axiom pure_left : forall {A B : Type} (a : A) (f : A -> M B),
      bind (pure a) f = f a.

  (** Binding a Monad with [pure] has no effect. *)
  Axiom pure_right : forall {A : Type} (m : M A),
      bind m pure = m.

  (** Associativity of bind. *)
  Axiom bind_assoc : forall {A B C : Type} (m : M A) (k : A -> M B) (h : B -> M C),
      bind m (fun a => bind (k a) h) = bind (bind m k) h.
End MonadSpec.

Module MonadFactory (MS : MonadSpec).
  Include ApplicativeFactory MS.

  Instance MI : Monad MS.M :=
    { bind _ _ := MS.bind;
      pure_left _ _ := MS.pure_left;
      pure_right _ := MS.pure_right;
      bind_assoc _ _ _ := MS.bind_assoc }.
End MonadFactory.
