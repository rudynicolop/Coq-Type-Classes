Require Coq.Lists.List.
Require Export TypeClassLib.Auxilary.

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
  Instance FunctorInstance : Functor FS.F :=
    { fmap _ _ := FS.fmap;
      fmap_id _ := FS.fmap_id;
      fmap_compose _ _ _ := FS.fmap_compose }.
End FunctorFactory.

(** Identity *)
Module IdentityFunctorSpec <: FunctorSpec.
  Definition F : Type -> Type := fun t => t.

  Definition fmap {A B : Type} (f : A -> B) (a : A) : B := f a.

  Lemma fmap_id : forall {A : Type},
      fmap (fun x : A => x) = (fun x : A => x).
  Proof. intros. unfold fmap. reflexivity. Qed.

  Lemma fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
      fmap (g ∘ f) = fmap g ∘ fmap f.
  Proof. intros. unfold fmap, compose. reflexivity. Qed.
End IdentityFunctorSpec.

Module IdentityFunctorFactory := FunctorFactory IdentityFunctorSpec.
Definition IdentityFunctor : Functor id :=
  IdentityFunctorFactory.FunctorInstance.
(**[]*)

Compute S <$> 4.

(** Option *)
Module OptionFunctorSpec <: FunctorSpec.
  Definition F : Type -> Type := option.

  Definition fmap {A B : Type} (f : A -> B) (oa : option A) :=
    match oa with
    | None   => None
    | Some a => Some (f a)
    end.
  (**[]*)

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
End OptionFunctorSpec.

Module OptionFunctorFactory := FunctorFactory OptionFunctorSpec.
Definition OptionFunctor : Functor option :=
  OptionFunctorFactory.FunctorInstance.
(**[]*)

Compute S <$> None.
Compute S <$> (Some 41).

(** List *)
Module ListFunctorSpec <: FunctorSpec.
  Import Coq.Lists.List.
  Import ListNotations.

  Definition F : Type -> Type := list.

  Definition fmap {A B : Type} (f : A -> B) : list A -> list B := map f.

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
End ListFunctorSpec.

Module ListFunctorFactory := FunctorFactory ListFunctorSpec.
Definition ListFunctor : Functor list :=
  ListFunctorFactory.FunctorInstance.
(**[]*)

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

(** Functor Composition *)
Module FunctorCompose (M Q : FunctorSpec) <: FunctorSpec.
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
End FunctorCompose.

Module ComposePlayground.
  Module FOL' := FunctorCompose OptionFunctorSpec ListFunctorSpec.
  Module FOL  := FunctorFactory FOL'.
  Instance OptionListFunctor : Functor (list ∘ option) := FOL.FunctorInstance.

  Import Coq.Lists.List.
  Import ListNotations.

  Compute (fun x => x * x) <$>
          [None; Some 1; Some 2; None; None; None; Some 3; Some 4; Some 5; None].
End ComposePlayground.

(** * Parameterized Functors *)

(* Class ParamFunctor
   (F : Type -> Type -> Type) (A : Type) `{Functor (F A)}. *)

Module Type ParamFunctorSpec.
  (** The Functor's kind. *)
  Parameter F : Type -> Type -> Type.

  Section Spec.
    Context {A : Type}.

    Parameter fmap : forall {B C : Type}, (B -> C) -> F A B -> F A C.

    (** Functor Laws. *)

    Axiom fmap_id : forall {B : Type},
        fmap (fun x : B => x) = (fun x : F A B => x).

    Axiom fmap_compose : forall {B C D : Type} (h : B -> C) (k : C -> D),
        fmap (k ∘ h) = fmap k ∘ fmap h.
  End Spec.
End ParamFunctorSpec.

(** A Parameterized-Functor Factory. *)
Module ParamFunctorFactory (FS : ParamFunctorSpec).
  Instance ParamFunctorInstance (A : Type) : Functor (FS.F A) :=
    { fmap := @FS.fmap A;
      fmap_id := @FS.fmap_id A;
      fmap_compose := @FS.fmap_compose A }.
End ParamFunctorFactory.

(** Either *)
Module EitherFunctorSpec <: ParamFunctorSpec.
  Definition F : Type -> Type -> Type := either.

  Section Spec.
    Context {A : Type}.

    Definition fmap {B C : Type} (f : B -> C) (e : either A B) : either A C :=
      match e with
      | Left  a => Left a
      | Right b => Right (f b)
      end.
    (**[]*)

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
  End Spec.
End EitherFunctorSpec.

Module EitherFunctorFactory := ParamFunctorFactory EitherFunctorSpec.
Definition EitherFunctor (A : Type) : Functor (either A) :=
  EitherFunctorFactory.ParamFunctorInstance A.

Compute (fun x => x * x) <$> Left 5.
Compute (fun x => x * x) <$> Right 5.

(** Arrow Types *)
Module ArrowFunctorSpec <: ParamFunctorSpec.
  Definition F : Type -> Type -> Type := fun A B => A -> B.

  Section Spec.
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
  End Spec.
End ArrowFunctorSpec.

Module ArrowFunctorFactory := ParamFunctorFactory ArrowFunctorSpec.
Definition ArrowFunctor (A : Type) : Functor (fun B => A -> B) :=
  ArrowFunctorFactory.ParamFunctorInstance A.

(** Binary Trees *)
Module TreeFunctorSpec <: ParamFunctorSpec.
  Definition F : Type -> Type -> Type := tree.

  Section Spec.
    Context {K : Type}.

    Fixpoint fmap {V R : Type} (f : V -> R) (t : tree K V) : tree K R :=
      match t with
      | Leaf => Leaf
      | Node k v l r => Node k (f v) (fmap f l) (fmap f r)
      end.
    (**[]*)

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
  End Spec.
End TreeFunctorSpec.

Module TreeFunctorFactory := ParamFunctorFactory TreeFunctorSpec.
Definition TreeFunctor (K : Type) : Functor (tree K) :=
  TreeFunctorFactory.ParamFunctorInstance K.
(**[]*)

(** State *)
Module StateFunctorSpec <: ParamFunctorSpec.
  Definition F : Type -> Type -> Type := state.

  Section Spec.
    Context {S : Type}.

    Definition fmap {A B : Type} (f : A -> B) (sa : state S A) : state S B :=
      (fun '(a, st) => (f a, st)) ∘ sa.

    Lemma fmap_id : forall {A : Type},
        fmap (fun x : A => x) = (fun x : state S A => x).
    Proof.
      intros. extensionality sa. extensionality st.
      unfold fmap. unfold compose. destruct (sa st); auto.
    Qed.

    Lemma fmap_compose : forall {A B C : Type} (h : A -> B) (k : B -> C),
        fmap (k ∘ h) = fmap k ∘ fmap h.
    Proof.
      intros. extensionality sa.
      extensionality st. unfold fmap. unfold compose.
      destruct (sa st) as [a st']. reflexivity.
    Qed.
  End Spec.
End StateFunctorSpec.

Module StateFunctorFactory := ParamFunctorFactory StateFunctorSpec.
Definition StateFunctor (S : Type) : Functor (state S) :=
  StateFunctorFactory.ParamFunctorInstance S.
(**[]*)

(** Continuations. *)
Module ContFunctorSpec <: ParamFunctorSpec.
  Definition F : Type -> Type -> Type := cont.

  Section Spec.
    Context {R : Type}.

    Definition fmap {A B : Type} (f : A -> B) (c : cont R A) : cont R B :=
      fun k => c (fun a => k (f a)).
    (**[]*)

    Lemma fmap_id : forall {A : Type},
        fmap (fun x : A => x) = (fun x : cont R A => x).
    Proof. intros. reflexivity. Qed.

    Lemma fmap_compose : forall {A B C : Type} (h : A -> B) (k : B -> C),
        fmap (k ∘ h) = fmap k ∘ fmap h.
    Proof. intros. reflexivity. Qed.
  End Spec.
End ContFunctorSpec.

Module ContFunctorFactory := ParamFunctorFactory ContFunctorSpec.
Definition ContFunctor (R : Type) : Functor (cont R) :=
  ContFunctorFactory.ParamFunctorInstance R.
(**[]*)
