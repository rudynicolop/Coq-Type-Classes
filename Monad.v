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

Definition mcompose {A B C : Type} {M : Type -> Type} `{Monad M}
           (f : A -> M B) (h : B -> M C) (a : A) : M C := f a >>= h.

Infix ">=>" := mcompose (at level 44, right associativity).

(** The Monad Laws (more elegeantly)
    in terms of Composition. *)

(** Left [pure] is idempotent. *)
Lemma left_pure_idem :
  forall {A B : Type} {M : Type -> Type} `{HM : Monad M} (f : A -> M B),
    pure >=> f = f.
Proof.
  intros. unfold mcompose.
  extensionality a. apply pure_left.
Qed.

(** Right [pure] is idempotent. *)
Lemma right_pure_idem :
  forall {A B : Type} {M : Type -> Type} `{HM : Monad M} (f : A -> M B),
    f >=> pure = f.
Proof.
  intros. unfold mcompose.
  extensionality a. apply pure_right.
Qed.

(** Composition is associative. *)
Lemma mcompose_assoc :
  forall {A B C D : Type} {M : Type -> Type} `{HM : Monad M}
    (f : A -> M B) (h : B -> M C) (k : C -> M D),
    (f >=> h) >=> k = f >=> h >=> k.
Proof.
  intros. unfold mcompose.
  extensionality a. rewrite bind_assoc.
  reflexivity.
Qed.

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

  Instance MonadInstance : Monad MS.M :=
    { bind _ _ := MS.bind;
      pure_left _ _ := MS.pure_left;
      pure_right _ := MS.pure_right;
      bind_assoc _ _ _ := MS.bind_assoc }.
End MonadFactory.

(** Identity *)
Module IdentityMonadSpec <: MonadSpec.
  Include IdentityApplicativeSpec.
  Definition M : Type -> Type := id.

  Definition bind {A B : Type} : A -> (A -> B) -> B := pipeline.

  Lemma pure_left : forall {A B : Type} (a : A) (f : A -> B),
      bind (pure a) f = f a.
  Proof. intros. reflexivity. Qed.

  Lemma pure_right : forall {A : Type} (m : A),
      bind m pure = m.
  Proof. intros. reflexivity. Qed.

  Lemma bind_assoc : forall {A B C : Type} (m : A) (k : A -> B) (h : B -> C),
      bind m (fun a => bind (k a) h) = bind (bind m k) h.
  Proof. intros. reflexivity. Qed.
End IdentityMonadSpec.

Module IdentityMonadFactory := MonadFactory IdentityMonadSpec.
Definition IdentityMonad : Monad id :=
  IdentityMonadFactory.MonadInstance.
(**[]*)

(** Option *)
Module OptionMonadSpec <: MonadSpec.
  Include OptionApplicativeSpec.

  Definition M : Type -> Type := option.

  Definition bind {A B : Type} (m : option A) (f : A -> option B) : option B :=
    match m with
    | None   => None
    | Some a => f a
    end.
  (**[]*)

  Lemma pure_left : forall {A B : Type} (a : A) (f : A -> option B),
      bind (pure a) f = f a.
  Proof. intros. reflexivity. Qed.

  Lemma pure_right : forall {A : Type} (m : option A),
      bind m pure = m.
  Proof. intros. destruct m; reflexivity. Qed.

  Lemma bind_assoc :
    forall {A B C : Type} (m : option A) (k : A -> option B) (h : B -> option C),
      bind m (fun a => bind (k a) h) = bind (bind m k) h.
  Proof. intros. destruct m; reflexivity. Qed.
End OptionMonadSpec.

Module OptionMonadFactory := MonadFactory OptionMonadSpec.
Definition OptionMonad : Monad option :=
  OptionMonadFactory.MonadInstance.

Compute Some 5 >>= (fun x => pure (x * x)) >>= (fun y => pure (y + y)).
Compute Some 5 >>= (fun _ => None) >>= (fun y => pure (y + y)).
Compute x <- Some 5;; y <- Some 6;; pure (x * y).

(** List *)
Module ListMonadSpec <: MonadSpec.
  Import Coq.Lists.List.
  Import ListNotations.

  Include ListApplicativeSpec.
  Definition M : Type -> Type := list.

  Definition bind {A B : Type} (l : list A) (f : A -> list B) : list B :=
    flat_map f l.
  (**[]*)

  Lemma pure_left : forall {A B : Type} (a : A) (f : A -> list B),
      bind (pure a) f = f a.
  Proof. intros. simpl. apply app_nil_r. Qed.

  Lemma pure_right : forall {A : Type} (m : list A),
      bind m pure = m.
  Proof.
    intros. unfold bind.
    induction m; auto.
    simpl. apply f_equal. assumption.
  Qed.

  Lemma bind_assoc :
    forall {A B C : Type} (m : list A) (k : A -> list B) (h : B -> list C),
      bind m (fun a => bind (k a) h) = bind (bind m k) h.
  Proof.
    intros. unfold bind.
    induction m as [| a t IHt]; simpl in *; auto.
    rewrite IHt; clear IHt. Search (flat_map _ _ ++ flat_map _ _).
    rewrite flat_map_app. reflexivity.
  Qed.
End ListMonadSpec.

Module ListMonadFactory := MonadFactory ListMonadSpec.
Definition ListMonad : Monad list :=
  ListMonadFactory.MonadInstance.
