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

Notation "a <- ma ;; mb" :=
  (bind ma (fun a => mb)) (at level 100, right associativity).

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
(**[]*)

Module ListPlayground.
  Import Coq.Lists.List.
  Import ListNotations.

  Definition list_pairs {A B : Type} (la : list A) (lb : list B) : list (A * B) :=
    a <- la;; b <- lb;; pure (a,b).

  Compute list_pairs [1;2;3;4;5;6] [None; Some 69; None; None; Some 42].
End ListPlayground.

(** * Parameterized Monads *)

Module Type ParamMonadSpec <: ParamApplicativeSpec.
  Include ParamApplicativeSpec.
  Definition M : Type -> Type -> Type := F.

  Section Spec.
    Context {T : Type}.

    Parameter bind : forall {A B : Type}, M T A -> (A -> M T B) -> M T B.

    (** Laws. *)

    (** Promontion to a Monad has no effect. *)
    Axiom pure_left : forall {A B : Type} (a : A) (f : A -> M T B),
        bind (pure a) f = f a.

    (** Binding a Monad with [pure] has no effect. *)
    Axiom pure_right : forall {A : Type} (m : M T A),
        bind m pure = m.

    (** Associativity of bind. *)
    Axiom bind_assoc :
      forall {A B C : Type} (m : M T A) (k : A -> M T B) (h : B -> M T C),
        bind m (fun a => bind (k a) h) = bind (bind m k) h.
  End Spec.
End ParamMonadSpec.

Module ParamMonadFactory (MS : ParamMonadSpec).
  Include ParamApplicativeFactory MS.

  Instance ParamMonadInstance (T : Type) : Monad (MS.M T) :=
    { bind := @MS.bind T;
      pure_left := @MS.pure_left T;
      pure_right := @MS.pure_right T;
      bind_assoc := @MS.bind_assoc T }.
End ParamMonadFactory.

(** Either. *)
Module EitherMonadSpec <: ParamMonadSpec.
  Include EitherApplicativeSpec.
  Definition M : Type -> Type -> Type := either.

  Section Spec.
    Context {T : Type}.

    Definition bind {A B : Type}
               (m : either T A) (f : A -> either T B) : either T B :=
      match m with
      | Left t  => Left t
      | Right a => f a
      end.
    (**[]*)

    Lemma pure_left : forall {A B : Type} (a : A) (f : A -> either T B),
        bind (pure a) f = f a.
    Proof. intros. reflexivity. Qed.

    Lemma pure_right : forall {A : Type} (m : either T A),
        bind m pure = m.
    Proof. intros. destruct m; reflexivity. Qed.

    Lemma bind_assoc :
      forall {A B C : Type} (m : either T A)
        (k : A -> either T B) (h : B -> either T C),
        bind m (fun a => bind (k a) h) = bind (bind m k) h.
    Proof. intros. destruct m; reflexivity. Qed.
  End Spec.
End EitherMonadSpec.

Module EitherMonadFactory := ParamMonadFactory EitherMonadSpec.
Definition EitherMonad (A : Type) : Monad (either A) :=
  EitherMonadFactory.ParamMonadInstance A.
(**[]*)

(** Arrow. *)
Module ArrowMonadSpec <: ParamMonadSpec.
  Include ArrowApplicativeSpec.
  Definition M : Type -> Type -> Type := (fun T R => T -> R).

  Section Spec.
    Context {T : Type}.

    Definition bind {A B : Type}
               (m : T -> A) (f : A -> T -> B) : T -> B := fun t => f (m t) t.
    (**[]*)

    Lemma pure_left : forall {A B : Type} (a : A) (f : A -> T -> B),
        bind (pure a) f = f a.
    Proof. intros. reflexivity. Qed.

    Lemma pure_right : forall {A : Type} (m : T -> A),
        bind m pure = m.
    Proof. intros. reflexivity. Qed.

    Lemma bind_assoc :
      forall {A B C : Type} (m : T -> A) (k : A -> T -> B) (h : B -> T -> C),
        bind m (fun a => bind (k a) h) = bind (bind m k) h.
    Proof. intros. reflexivity. Qed.
  End Spec.
End ArrowMonadSpec.

Module ArrowMonadFactory := ParamMonadFactory ArrowMonadSpec.
Definition ArrowMonad (A : Type) : Monad (fun B => A -> B) :=
  ArrowMonadFactory.ParamMonadInstance A.

(** State. *)
Module StateMonadSpec <: ParamMonadSpec.
  Include StateApplicativeSpec.
  Definition M : Type -> Type -> Type := F.

  Section Spec.
    Context {S : Type}.

    Definition bind {A B : Type}
               (m : state S A) (f : A -> state S B) : state S B :=
      fun st => let (a, st) := m st in f a st.

    Lemma pure_left : forall {A B : Type} (a : A) (f : A -> state S B),
        bind (pure a) f = f a.
    Proof. intros. reflexivity. Qed.

    Lemma pure_right : forall {A : Type} (m : state S A),
        bind m pure = m.
    Proof.
      intros. extensionality st. unfold bind, pure.
      destruct (m st) ; reflexivity.
    Qed.

    Lemma bind_assoc :
      forall {A B C : Type} (m : state S A)
        (k : A -> state S B) (h : B -> state S C),
        bind m (fun a => bind (k a) h) = bind (bind m k) h.
    Proof.
      intros. extensionality st. unfold bind.
      destruct (m st); reflexivity.
    Qed.
  End Spec.
End StateMonadSpec.

Module StateMonadFactory := ParamMonadFactory StateMonadSpec.
Definition StateMonad (S : Type) : Monad (state S) :=
  StateMonadFactory.ParamMonadInstance S.
(**[]*)

(** Continuations. *)
Module ContMonadSpec <: ParamMonadSpec.
  Include ContApplicativeSpec.
  Definition M : Type -> Type -> Type := cont.

  Section Spec.
    Context {R : Type}.

    Definition bind {A B : Type}
               (c : cont R A) (f : A -> cont R B) : cont R B :=
      fun k => c (fun a => f a k).

    Lemma pure_left : forall {A B : Type} (a : A) (f : A -> cont R B),
        bind (pure a) f = f a.
    Proof. intros. reflexivity. Qed.

    (** Binding a Monad with [pure] has no effect. *)
    Lemma pure_right : forall {A : Type} (m : cont R A),
        bind m pure = m.
    Proof. intros. reflexivity. Qed.

    Lemma bind_assoc :
      forall {A B C : Type} (m : cont R A)
        (k : A -> cont R B) (h : B -> cont R C),
        bind m (fun a => bind (k a) h) = bind (bind m k) h.
    Proof. intros. reflexivity. Qed.
  End Spec.
End ContMonadSpec.

Module ContMonadFactory := ParamMonadFactory ContMonadSpec.
Definition ContMonad (R : Type) : Monad (cont R) :=
  ContMonadFactory.ParamMonadInstance R.
(**[]*)
