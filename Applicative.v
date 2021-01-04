Require Export Coq.Logic.FunctionalExtensionality.
Require Coq.Lists.List.
Require Import TypeClassLib.Auxilary.
Require Export TypeClassLib.Functor.

(** * Applicative Functor Type Class *)
Class Applicative (F : Type -> Type) `{Functor F} :=
  { pure {A : Type} : A -> F A;
    fapp {A B : Type} : F (A -> B) -> F A -> F B;
    (** Laws *)
    app_identity : forall {A : Type} (a : F A),
        fapp (pure (fun x => x)) a = a;
    app_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
        fapp (pure f) (pure a) = pure (f a);
    app_interchange : forall {A B : Type} (f : F (A -> B)) (a : A),
        fapp f (pure a) = fapp (pure (fun h => h a)) f;
    app_composition : forall {A B C : Type} (f : F (A -> B)) (h : F (B -> C)) (a : F A),
        fapp h (fapp f a) = fapp (fapp (fapp (pure (@compose A B C)) h) f) a;
    app_fmap_pure : forall {A B : Type} (f : A -> B) (a : F A),
        f <$> a = fapp (pure f) a;
}.

Infix "<*>" := fapp (at level 43, left associativity).

(** * Applicative Functor Specification *)
Module Type ApplicativeSpec <: FunctorSpec.
  Include FunctorSpec.

  Parameter pure : forall {A : Type}, A -> F A.

  Parameter fapp : forall {A B : Type}, F (A -> B) -> F A -> F B.

  (** Laws *)

  (** The identity law. *)
  Axiom app_identity : forall {A : Type} (a : F A),
      fapp (pure (fun x => x)) a = a.

  (** Homomorphism. *)
  Axiom app_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
      fapp (pure f) (pure a) = pure (f a).

  (** Interchange. *)
   Axiom app_interchange : forall {A B : Type} (f : F (A -> B)) (a : A),
      fapp f (pure a) = fapp (pure (fun h => h a)) f.

   (** Composition. *)
   Axiom app_composition :
     forall {A B C : Type} (f : F (A -> B)) (h : F (B -> C)) (a : F A),
       fapp h (fapp f a) = fapp (fapp (fapp (pure (@compose A B C)) h) f) a.

   (** Relation to Functor. *)
   Axiom app_fmap_pure : forall {A B : Type} (f : A -> B) (a : F A),
       fmap f a = fapp (pure f) a.
End ApplicativeSpec.

Module ApplicativeFactory (A : ApplicativeSpec).
  Include FunctorFactory A.

  Instance AI : Applicative A.F :=
    { pure _ := A.pure;
      fapp _ _ := A.fapp;
      app_identity _ := A.app_identity;
      app_homomorphism _ _ := A.app_homomorphism;
      app_composition _ _ _ := A.app_composition;
      app_interchange _ _ := A.app_interchange;
      app_fmap_pure _ _ := A.app_fmap_pure; }.
End ApplicativeFactory.

(** Identity. *)
Module AIdentity <: ApplicativeSpec.
  Include FIdentity.

  Definition pure {A : Type} (a : A) := a.

  Definition fapp {A B : Type} (f : A -> B) : A -> B := f.

  Lemma app_identity : forall {A : Type} (a : A),
      fapp (pure (fun x => x)) a = a.
  Proof. intros. reflexivity. Qed.

  Lemma app_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
      fapp (pure f) (pure a) = pure (f a).
  Proof. intros. reflexivity. Qed.

  Lemma app_interchange : forall {A B : Type} (f : A -> B) (a : A),
      fapp f (pure a) = fapp (pure (fun h => h a)) f.
  Proof. intros. reflexivity. Qed.

  Lemma app_composition :
    forall {A B C : Type} (f : A -> B) (h : B -> C) (a : A),
      fapp h (fapp f a) = fapp (fapp (fapp (pure (@compose A B C)) h) f) a.
  Proof. intros. reflexivity. Qed.

  Lemma app_fmap_pure : forall {A B : Type} (f : A -> B) (a : F A),
      fmap f a = fapp (pure f) a.
  Proof. intros. reflexivity. Qed.
End AIdentity.

Module AId := ApplicativeFactory AIdentity.
Definition IdentityApplicative : Applicative id := AId.AI.
