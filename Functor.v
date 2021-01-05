Require Export Coq.Logic.FunctionalExtensionality.
Require Coq.Lists.List.
Require Import TypeClassLib.Auxilary.

(** * Functor Type Class *)

Class Functor (F : Type -> Type) : Type :=
  { fmap {A B : Type} : (A -> B) -> F A -> F B;
    (** Laws *)
    fmap_id : forall {A : Type},
        fmap (fun x : A => x) = (fun x : F A => x);
    fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
        fmap (g ∘ f) = fmap g ∘ fmap f }.

Infix "<$>" := fmap (at level 43, left associativity).

(** * Functor Specification *)

(** Because Coq Type Classes (ab)use
    cumbersome record syntax, I found it
    more convenient to create namespaces
    for definitions and then to instantiate
    the Type Class with those definitions *)
Module Type FunctorSpec.
  (** The Functor's kind. *)
  Parameter F : Type -> Type.

  Parameter fmap : forall {A B : Type}, (A -> B) -> F A -> F B.

  (** Functor Laws. *)

  Axiom fmap_id : forall {A : Type},
      fmap (fun x : A => x) = (fun x : F A => x).

  Axiom fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
      fmap (g ∘ f) = fmap g ∘ fmap f.
End FunctorSpec.

(** Generate a Functor Instance from a specification. *)
Module FunctorFactory (FS : FunctorSpec).
  Instance FI : Functor FS.F :=
    { fmap _ _ := FS.fmap;
      fmap_id _ := FS.fmap_id;
      fmap_compose _ _ _ := FS.fmap_compose }.
End FunctorFactory.

(** Identity *)
Module FIdentity <: FunctorSpec.
  Definition F : Type -> Type := fun t => t.

  Definition fmap {A B : Type} (f : A -> B) (a : A) : B := f a.

  Lemma fmap_id : forall {A : Type},
      fmap (fun x : A => x) = (fun x : A => x).
  Proof. intros. unfold fmap. reflexivity. Qed.

  Lemma fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
      fmap (g ∘ f) = fmap g ∘ fmap f.
  Proof. intros. unfold fmap, compose. reflexivity. Qed.
End FIdentity.

Module FI := FunctorFactory FIdentity.
Definition IdentityFunctor : Functor (fun t => t) := FI.FI.

Compute S <$> 4.

(** Option *)
Module FOption <: FunctorSpec.
  Definition F : Type -> Type := option.

  Definition fmap {A B : Type} (f : A -> B) (oa : option A) :=
    match oa with
    | None   => None
    | Some a => Some (f a)
    end.

  Lemma fmap_id : forall (A : Type),
      fmap (fun x : A => x) = (fun x : option A => x).
  Proof.
    intros. unfold fmap. extensionality oa.
    destruct oa as [a |]; reflexivity.
  Qed.

  Lemma fmap_compose : forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap (g ∘ f) = fmap g ∘ fmap f.
  Proof.
    intros. unfold fmap, compose.
    extensionality oa. destruct oa as [a |]; reflexivity.
  Qed.
End FOption.

Module FO := FunctorFactory FOption.
Definition OptionFunctor : Functor option := FO.FI.

Compute S <$> None.
Compute S <$> (Some 41).

(** List *)
Module FList <: FunctorSpec.
  Import Coq.Lists.List.
  Import ListNotations.

  Definition F : Type -> Type := list.

  Definition fmap {A B : Type} (f : A -> B) := map f.

  Lemma fmap_id : forall {A : Type},
      map (fun x : A => x) = (fun x : list A => x).
  Proof.
    intros. extensionality l.
    Search (map (fun x => x)). rewrite map_id. reflexivity.
  Qed.

  Lemma fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
      map (g ∘ f) = map g ∘ map f.
  Proof.
    intros. extensionality l.
    induction l as [| h t IHt]; auto.
    cbn. rewrite IHt. unfold compose. reflexivity.
  Qed.
End FList.

Module FL := FunctorFactory FList.
Definition ListFunctor : Functor list := FL.FI.

Module ListPlayground.
  Import Coq.Lists.List.
  Import ListNotations.

  Compute S <$> ((fun x => x * 5) <$> [1;2;3;4;5;6;7]).
  Compute (fun x => x * x) <$>
          ((fun x => match x with None => 0 | Some y => y end) <$>
          [None; Some 1; Some 2; None; None; None; Some 3; Some 4; Some 5; None]).
  Compute fmap (fun x => x * x) <$>
          (fmap (fun x => x + 1) <$>
          [None; Some 1; Some 2; None; None; None; Some 3; Some 4; Some 5; None]).
End ListPlayground.

(** Functor Functor *)
Module FFunctor (M Q : FunctorSpec) <: FunctorSpec.
  Definition F : Type -> Type := fun T => Q.F (M.F T).

  Definition fmap {A B : Type} (f : A -> B) : F A -> F B := Q.fmap (M.fmap f).

  Lemma fmap_id : forall {A : Type},
      fmap (fun a : A => a) = (fun x : F A => x).
  Proof.
    intros. unfold fmap.
    rewrite M.fmap_id. apply Q.fmap_id.
  Qed.

  Lemma fmap_compose : forall {A B C : Type} (f : A -> B) (h : B -> C),
      fmap (h ∘ f) = fmap h ∘ fmap f.
  Proof.
    intros. unfold fmap.
    rewrite M.fmap_compose. apply Q.fmap_compose.
  Qed.
End FFunctor.

Module FFunctorPlayground.
  Module FOL' := FFunctor FOption FList.
  Module FOL  := FunctorFactory FOL'.
  Instance OptionListFunctor : Functor (list ∘ option) := FOL.FI.

  Import Coq.Lists.List.
  Import ListNotations.

  Compute (fun x => x * x) <$>
          [None; Some 1; Some 2; None; None; None; Some 3; Some 4; Some 5; None].
End FFunctorPlayground.

(** * Parameterized Functors *)

(** Either *)
Module FEither.
  Section EitherSpec.
    Context {A : Type}.

    Definition fmap {B C : Type} (f : B -> C) (e : either A B) : either A C :=
      match e with
      | Left  a => Left a
      | Right b => Right (f b)
      end.

    Lemma fmap_id : forall {B : Type},
        fmap (fun x : B => x) = (fun x : either A B => x).
    Proof.
      intros. unfold fmap.
      extensionality e. destruct e as [a | b]; reflexivity.
    Qed.

    Lemma fmap_compose : forall {B C D : Type} (f : B -> C) (g : C -> D),
        fmap (g ∘ f) = fmap g ∘ fmap f.
    Proof.
      intros. extensionality e.
      unfold fmap, compose. destruct e; reflexivity.
    Qed.
  End EitherSpec.
End FEither.

Instance EitherFunctor (A : Type) : Functor (either A) :=
  { fmap := @FEither.fmap A;
    fmap_id := @FEither.fmap_id A;
    fmap_compose := @FEither.fmap_compose A }.

Compute (fun x => x * x) <$> Left 5.
Compute (fun x => x * x) <$> Right 5.

(** Arrow Types *)
Module FArrow.
  Section ArrowSpec.
    Context {A : Type}.

    Definition fmap {B C : Type} (h : B -> C) (f : A -> B) := h ∘ f.

    Lemma fmap_id : forall {B : Type},
        fmap (fun x : B => x) = (fun x : A -> B => x).
    Proof.
      intros. unfold fmap. extensionality f.
      extensionality a. unfold compose. reflexivity.
    Qed.

    Lemma fmap_compose : forall {B C D : Type} (h : B -> C) (g : C -> D),
        fmap (g ∘ h) = fmap g ∘ fmap h.
    Proof.
      intros. unfold fmap. extensionality f.
      extensionality a. unfold compose. reflexivity.
    Qed.
  End ArrowSpec.
End FArrow.

Instance ArrowFunctor (A : Type) : Functor (fun B => A -> B) :=
  { fmap := @FArrow.fmap A;
    fmap_id := @FArrow.fmap_id A;
    fmap_compose := @FArrow.fmap_compose A }.

(** Binary Trees *)
Module FTree.
  Section TreeSpec.
    Context {K : Type}.

    Fixpoint fmap {V R : Type} (f : V -> R) (t : tree K V) : tree K R :=
      match t with
      | Leaf => Leaf
      | Node k v l r => Node k (f v) (fmap f l) (fmap f r)
      end.

    Lemma fmap_id : forall {V : Type},
        fmap (fun v : V => v) = (fun t : tree K V => t).
    Proof.
      intros. extensionality t.
      induction t as [| k v l IHl r IHr]; cbn; auto.
      rewrite IHl. rewrite IHr. reflexivity.
    Qed.

    Lemma fmap_compose : forall {V W Z : Type} (h : V -> W) (g : W -> Z),
        fmap (g ∘ h) = fmap g ∘ fmap h.
    Proof.
      intros. extensionality t.
      induction t as [| k v l IHl r IHr]; cbn; auto.
      rewrite IHl. rewrite IHr. reflexivity.
    Qed.
  End TreeSpec.
End FTree.

Instance TreeFunctor (K : Type) : Functor (tree K) :=
  { fmap := @FTree.fmap K;
    fmap_id := @FTree.fmap_id K;
    fmap_compose := @FTree.fmap_compose K }.
