Require Coq.Lists.List.
Require Export TypeClassLib.Functor.

(** * Applicative Functor Type Class *)
Class Applicative (F : Type -> Type) :=
  { (** Substructure *)
    Applicative_Functor :> Functor F;
    pure {A : Type} : A -> F A;
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
    app_fmap_pure : forall {A B : Type} (f : A -> B),
        fmap f = fapp (pure f) }.
(**[]*)

Infix "<*>" := fapp (at level 43, left associativity).

Definition liftA2 {A B C : Type} {F : Type -> Type} `{Applicative F}
           (h : A -> B -> C) (a : F A) (b : F B) : F C :=
  h <$> a <*> b.
(**[]*)

Definition liftA3 {A B C D : Type} {F : Type -> Type} `{Applicative F}
           (h : A -> B -> C -> D) (a : F A) (b : F B) (c : F C) : F D :=
  h <$> a <*> b <*> c.
(**[]*)

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
  Axiom app_fmap_pure : forall {A B : Type} (f : A -> B),
      fmap f = fapp (pure f).
End ApplicativeSpec.

Module ApplicativeFactory (A : ApplicativeSpec).
  Include FunctorFactory A.

  Instance ApplicativeInstance : Applicative A.F :=
    { pure _ := A.pure;
      fapp _ _ := A.fapp;
      app_identity _ := A.app_identity;
      app_homomorphism _ _ := A.app_homomorphism;
      app_composition _ _ _ := A.app_composition;
      app_interchange _ _ := A.app_interchange;
      app_fmap_pure _ _ := A.app_fmap_pure }.
End ApplicativeFactory.

(** Identity. *)
Module IdentityApplicativeSpec <: ApplicativeSpec.
  Include IdentityFunctorSpec.

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

  Lemma app_fmap_pure : forall {A B : Type} (f : A -> B),
      fmap f = fapp (pure f).
  Proof. intros. reflexivity. Qed.
End IdentityApplicativeSpec.

Module IdentityApplicativeFactory := ApplicativeFactory IdentityApplicativeSpec.
Instance IdentityApplicative : Applicative (fun X => X) :=
  IdentityApplicativeFactory.ApplicativeInstance.
(**[]*)

(** Option. *)
Module OptionApplicativeSpec <: ApplicativeSpec.
  Include OptionFunctorSpec.

  Definition pure {A : Type} : A -> option A := Some.

  Definition fapp {A B : Type} (fo : option (A -> B)) (ao : option A) : option B :=
    match fo,ao with
    | None, _        => None
    | _, None        => None
    | Some f, Some a => Some (f a)
    end.

  Lemma app_identity : forall {A : Type} (a : option A),
      fapp (pure (fun x => x)) a = a.
  Proof. intros. destruct a; reflexivity. Qed.

  Lemma app_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
      fapp (pure f) (pure a) = pure (f a).
  Proof. intros. reflexivity. Qed.

  Lemma app_interchange : forall {A B : Type} (f : F (A -> B)) (a : A),
      fapp f (pure a) = fapp (pure (fun h => h a)) f.
  Proof. intros. reflexivity. Qed.

  Lemma app_composition :
    forall {A B C : Type} (f : option (A -> B)) (h : option (B -> C)) (a : option A),
      fapp h (fapp f a) = fapp (fapp (fapp (pure (@compose A B C)) h) f) a.
  Proof. intros A B C [] [] []; reflexivity. Qed.

  Lemma app_fmap_pure : forall {A B : Type} (f : A -> B),
      fmap f = fapp (pure f).
  Proof.
    intros. extensionality a.
    destruct a; reflexivity.
  Qed.
End OptionApplicativeSpec.

Module OptionApplicativeFactory := ApplicativeFactory OptionApplicativeSpec.
Instance OptionApplicative : Applicative option :=
  OptionApplicativeFactory.ApplicativeInstance.
(**[]*)

Compute (fun x y => x + y) <$> Some 3 <*> Some 4.
Compute (fun x y => (x,y)) <$> Some 42 <*> Some 69.
Compute (fun x y z => x * y + x * z) <$>
        Some 42 <*> Some 2 <*> Some 3.
Compute (fun x y z => x * y + x * z) <$>
        Some 42 <*> None <*> Some 3.

Module ListApplicativeSpec <: ApplicativeSpec.
  Import Coq.Lists.List.
  Import ListNotations.

  Include ListFunctorSpec.

  Definition pure {A : Type} (a : A) : list A := [a].

  Definition fapp {A B : Type} (fs : list (A -> B)) (xs : list A) : list B :=
    concat (map (fun f => map f xs) fs).

  Lemma app_identity : forall {A : Type} (a : list A),
      fapp (pure (fun x => x)) a = a.
  Proof.
    intros A xs. induction xs as [| a t IHt]; auto.
    unfold fapp in IHt. cbn in *. rewrite IHt. reflexivity.
  Qed.

  Lemma app_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
      fapp (pure f) (pure a) = pure (f a).
  Proof. intros. reflexivity. Qed.

  Lemma app_interchange : forall {A B : Type} (f : list (A -> B)) (a : A),
      fapp f (pure a) = fapp (pure (fun h => h a)) f.
  Proof.
    intros. induction f as [| f fs IHfs]; auto.
    unfold fapp in IHfs. cbn in *. rewrite IHfs. reflexivity.
  Qed.

  Lemma concat_map_empty : forall {A B : Type} (l : list A),
      @concat B (map (fun _ => []) l) = [].
  Proof. intros. induction l as [| h t IHt]; auto. Qed.

  Lemma app_composition :
    forall {A B C : Type} (f : list (A -> B)) (h : list (B -> C)) (a : list A),
      fapp h (fapp f a) = fapp (fapp (fapp (pure (@compose A B C)) h) f) a.
  Proof.
    intros. unfold fapp.
    induction f as [| f tf IHtf];
      induction h as [| h th IHth ];
      destruct a as [| a ta ];
      cbn in *; repeat rewrite app_nil_r in *;
        repeat rewrite concat_map_empty in *; cbn in *;
          repeat rewrite app_nil_r in *; auto;
            try apply concat_map_empty. apply f_equal.
    Search (map _ (_ ++ _)). repeat rewrite map_app in *.
    Search (map _ (map _ _)). rewrite map_map in *.
    rewrite <- app_assoc in *. apply f_equal.
    Search (map _ (concat _)). repeat rewrite concat_map in *.
    repeat rewrite map_map in *. cbn in *. rewrite concat_app in *.
    assert (HRewrite :
              (fun x : A -> B => h (x a) :: map h (map x ta)) =
              (fun x : A -> B => (h ∘ x) a :: map (h ∘ x) ta)).
    { extensionality g. rewrite fmap_compose. reflexivity. }
    rewrite HRewrite in *; clear HRewrite. apply f_equal.
    apply app_inv_head in IHtf. auto.
  Qed.

  Lemma app_fmap_pure : forall {A B : Type} (f : A -> B),
      fmap f = fapp (pure f).
  Proof.
    intros. extensionality a. unfold fapp.
    destruct a as [| h t]; auto.
    simpl. rewrite app_nil_r. reflexivity.
  Qed.
End ListApplicativeSpec.

Module ListApplicativeFactory := ApplicativeFactory ListApplicativeSpec.
Instance ListApplicative : Applicative list :=
  ListApplicativeFactory.ApplicativeInstance.
(**[]*)

Module ListPlayground.
  Import Coq.Lists.List.
  Import ListNotations.

  Module AOption := OptionApplicativeSpec.
  Module AList := ListApplicativeSpec.

  Compute pure mult <*> [2;3;4] <*> pure 4.
  Compute mult <$> [2;3;4;5] <*> pure 4.
End ListPlayground.

(** * Parameterized Applicatives *)

Module Type ParamApplicativeSpec <: ParamFunctorSpec.
  Include ParamFunctorSpec.

  Section Spec.
    Context {A : Type}.

    Parameter pure : forall {B : Type}, B -> F A B.

    Parameter fapp : forall {B C : Type}, F A (B -> C) -> F A B -> F A C.

    (** The identity law. *)
    Axiom app_identity : forall {B : Type} (b : F A B),
        fapp (pure (fun x => x)) b = b.

    (** Homomorphism. *)
    Axiom app_homomorphism : forall {B C : Type} (f : B -> C) (b : B),
        fapp (pure f) (pure b) = pure (f b).

    (** Interchange. *)
    Axiom app_interchange : forall {B C : Type} (f : F A (B -> C)) (b : B),
        fapp f (pure b) = fapp (pure (fun h => h b)) f.

    (** Composition. *)
    Axiom app_composition :
      forall {B C D : Type} (f : F A (B -> C)) (h : F A (C -> D)) (b : F A B),
        fapp h (fapp f b) = fapp (fapp (fapp (pure (@compose B C D)) h) f) b.

    (** Relation to Functor. *)
    Axiom app_fmap_pure : forall {B C : Type} (f : B -> C),
        fmap f = fapp (pure f).
  End Spec.
End ParamApplicativeSpec.

Module ParamApplicativeFactory (A : ParamApplicativeSpec).
  Include ParamFunctorFactory A.

  Instance ParamApplicativeInstance (T : Type) : Applicative (A.F T) :=
    { pure := @A.pure T;
      fapp := @A.fapp T;
      app_identity := @A.app_identity T;
      app_homomorphism := @A.app_homomorphism T;
      app_composition := @A.app_composition T;
      app_interchange := @A.app_interchange T;
      app_fmap_pure := @A.app_fmap_pure T }.
End ParamApplicativeFactory.

(** Either *)
Module EitherApplicativeSpec <: ParamFunctorSpec.
  Include EitherFunctorSpec.

  Section Spec.
    Context {A : Type}.

    Definition pure {B : Type} : B -> either A B := Right.

    Definition fapp {B C : Type} (f : F A (B -> C)) (b : F A B) : F A C :=
      match f, b with
      | Left a, _        => Left a
      | _, Left a        => Left a
      | Right f, Right b => Right (f b)
      end.

    Lemma app_identity : forall {B : Type} (b : F A B),
        fapp (pure (fun x => x)) b = b.
    Proof. intros. destruct b; reflexivity. Qed.

    Lemma app_homomorphism : forall {B C : Type} (f : B -> C) (b : B),
        fapp (pure f) (pure b) = pure (f b).
    Proof. intros. reflexivity. Qed.

    Lemma app_interchange : forall {B C : Type} (f : F A (B -> C)) (b : B),
        fapp f (pure b) = fapp (pure (fun h => h b)) f.
    Proof. intros. destruct f; reflexivity. Qed.

    Lemma app_composition :
      forall {B C D : Type} (f : F A (B -> C)) (h : F A (C -> D)) (b : F A B),
        fapp h (fapp f b) = fapp (fapp (fapp (pure (@compose B C D)) h) f) b.
    Proof. intros. destruct f; destruct h; destruct b; reflexivity. Qed.

    Lemma app_fmap_pure : forall {B C : Type} (f : B -> C),
        fmap f = fapp (pure f).
    Proof. intros. reflexivity. Qed.
  End Spec.
End EitherApplicativeSpec.

Module EitherApplicativeFactory := ParamApplicativeFactory EitherApplicativeSpec.
Instance EitherApplicative (A : Type) : Applicative (either A) :=
  EitherApplicativeFactory.ParamApplicativeInstance A.
(**[]*)

(** Arrow *)
Module ArrowApplicativeSpec <: ParamApplicativeSpec.
  Include ArrowFunctorSpec.

  Section Spec.
    Context {A : Type}.

    Definition pure {B : Type} (b : B) : A -> B := fun a => b.

    (** The S-Combinator! Wow! *)
    Definition fapp {B C : Type} (f : A -> B -> C) (h : A -> B) : A -> C :=
      fun a => f a (h a).
    (**[]*)

    Lemma app_identity : forall {B : Type} (b : A -> B),
        fapp (pure (fun x => x)) b = b.
    Proof. intros. reflexivity. Qed.

    Lemma app_homomorphism : forall {B C : Type} (f : B -> C) (b : B),
        fapp (pure f) (pure b) = pure (f b).
    Proof. intros. extensionality a. reflexivity. Qed.

    Lemma app_interchange : forall {B C : Type} (f : A -> B -> C) (b : B),
        fapp f (pure b) = fapp (pure (fun h => h b)) f.
    Proof. intros. extensionality a. reflexivity. Qed.

    Lemma app_composition :
      forall {B C D : Type} (f : A -> B -> C) (h : A -> C -> D) (b : A -> B),
        fapp h (fapp f b) = fapp (fapp (fapp (pure (@compose B C D)) h) f) b.
    Proof. intros. extensionality a. reflexivity. Qed.

    Lemma app_fmap_pure : forall {B C : Type} (f : B -> C),
        fmap f = fapp (pure f).
    Proof. intros. extensionality h. extensionality a. reflexivity. Qed.
  End Spec.
End ArrowApplicativeSpec.

Module ArrowApplicativeFactory := ParamApplicativeFactory ArrowApplicativeSpec.
Instance ArrowApplicative (A : Type) : Applicative (fun B => A -> B) :=
  ArrowApplicativeFactory.ParamApplicativeInstance A.
(**[]*)

(** State. *)
Module StateApplicativeSpec <: ParamApplicativeSpec.
  Include StateFunctorSpec.

  Section Spec.
    Context {S : Type}.

    Definition pure {A : Type} (a : A) : state S A := fun st => (a, st).

    Definition fapp {A B : Type}
               (f : state S (A -> B)) (sa : state S A) : state S B :=
      fun st => let (f, st) := f st in
             let (a, st) := sa st in (f a, st).

    Lemma app_identity : forall {A : Type} (sa : state S A),
        fapp (pure (fun x => x)) sa = sa.
    Proof.
      intros. extensionality st. unfold fapp, pure.
      destruct (sa st) as [a st']. reflexivity.
    Qed.

    Lemma app_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
        fapp (pure f) (pure a) = pure (f a).
    Proof. intros. extensionality st. unfold fapp, pure. reflexivity. Qed.

    Lemma app_interchange : forall {A B : Type} (f : state S (A -> B)) (a : A),
        fapp f (pure a) = fapp (pure (fun h => h a)) f.
    Proof.
      intros. extensionality st.
      unfold fapp, pure. reflexivity.
    Qed.

    Lemma app_composition :
      forall {A B C : Type} (f : state S (A -> B))
        (h : state S (B -> C)) (s : state S A),
        fapp h (fapp f s) = fapp (fapp (fapp (pure (@compose A B C)) h) f) s.
    Proof.
      intros. extensionality st. unfold fapp, pure, compose.
      destruct (h st) as [b st']. destruct (f st') as [k st''].
      destruct (s st'') as [a' st''']. reflexivity.
    Qed.

    Lemma app_fmap_pure : forall {A B : Type} (f : A -> B),
        fmap f = fapp (pure f).
    Proof.
      intros. extensionality s. extensionality st.
      unfold fmap, fapp, pure. unfold compose. reflexivity.
    Qed.
  End Spec.
End StateApplicativeSpec.

Module StateApplicativeFactory :=
  ParamApplicativeFactory StateApplicativeSpec.
Instance StateApplicative (S : Type) : Applicative (state S) :=
  StateApplicativeFactory.ParamApplicativeInstance S.
(**[]*)


(** Continuations. *)
Module ContApplicativeSpec <: ParamApplicativeSpec.
  Include ContFunctorSpec.

  Section Spec.
    Context {R : Type}.

    Definition pure {A : Type} (a : A) : cont R A := fun k => k a.

    Definition fapp {A B : Type}
               (f : cont R (A -> B)) (c : cont R A) : cont R B :=
      fun k => c (fun a => f (fun h => k (h a))).

    Lemma app_identity : forall {A : Type} (c : cont R A),
        fapp (pure (fun x => x)) c = c.
    Proof. intros. reflexivity. Qed.

    Lemma app_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
        fapp (pure f) (pure a) = pure (f a).
    Proof. intros. reflexivity. Qed.

    Lemma app_interchange : forall {A B : Type} (f : cont R (A -> B)) (a : A),
        fapp f (pure a) = fapp (pure (fun h => h a)) f.
    Proof. intros. reflexivity. Qed.

    Lemma app_composition :
      forall {A B C : Type} (f : cont R (A -> B))
        (h : cont R (B -> C)) (a : cont R A),
        fapp h (fapp f a) = fapp (fapp (fapp (pure (@compose A B C)) h) f) a.
    Proof. intros. reflexivity. Qed.

    Lemma app_fmap_pure : forall {A B : Type} (f : A -> B),
        fmap f = fapp (pure f).
    Proof. intros. reflexivity. Qed.
  End Spec.
End ContApplicativeSpec.

Module ContApplicativeFactory := ParamApplicativeFactory ContApplicativeSpec.
Instance ContApplicative (R : Type) : Applicative (cont R) :=
  ContApplicativeFactory.ParamApplicativeInstance R.
(**[]*)

(** * Applicative Composition *)

Section ApplicativeComposition.
  Context {Q R : Type -> Type}.

  (* Context {QF : Functor Q}. *)

  (* Context {RF : Functor R}. *)

  (* Instance QRFunctor : Functor (R ∘ Q) := ComposeFunctor Q R. *)

  Context {QA : Applicative Q}.

  Context {RA : Applicative R}.

  Instance QRFunctor : Functor (R ∘ Q) := ComposeFunctor Q R.

  Definition purec {A : Type} : A -> (R ∘ Q) A :=
    (@pure R _ _) ∘ (@pure Q _ A).
  (**[]*)

  Definition fappc {A B : Type}
             (f : (R ∘ Q) (A -> B)) (a : (R ∘ Q) A) : (R ∘ Q) B :=
    @fapp Q _ _ _ <$> f <*> a.
    (* @fapp R _ _ _ _ (@fmap R _ _ _ (@fapp Q _ _ _ _) f). *)
  (**[]*)

  Lemma app_identityc : forall {A : Type} (a : (R ∘ Q) A),
      fappc (purec (fun x => x)) a = a.
  Proof.
    intros. unfold fappc, purec.
    rewrite app_fmap_pure. unfold compose.
    rewrite app_homomorphism. repeat rewrite <- app_fmap_pure.
    repeat rewrite fmap_id. reflexivity.
  Qed.

  Lemma app_homomorphismc : forall {A B : Type} (f : A -> B) (a : A),
      fappc (purec f) (purec a) = purec (f a).
  Proof.
    intros. unfold fappc, purec.
    rewrite app_fmap_pure. unfold compose.
    repeat rewrite app_homomorphism. reflexivity.
  Qed.

  Lemma app_interchangec : forall {A B : Type} (f : (R ∘ Q) (A -> B)) (a : A),
      fappc f (purec a) = fappc (purec (fun h => h a)) f.
  Proof.
    intros. unfold fappc, purec. unfold compose.
    repeat rewrite app_fmap_pure.
    repeat rewrite app_homomorphism.
    rewrite app_interchange.
    repeat rewrite <- app_fmap_pure.
    pose proof @fmap_compose R _ as H. unfold compose in H.
    pose proof H _ _ _ fapp (fun h : Q A -> Q B => h (pure a)) as H'.
    Check equal_f. apply equal_f with f in H'.
    rewrite <- H'; clear H' H. apply f_2_arg.
    extensionality q. rewrite app_interchange.
    rewrite app_fmap_pure. reflexivity.
  Qed.

  Lemma app_compositionc :
    forall {A B C : Type}
      (f : (R ∘ Q) (A -> B)) (h : (R ∘ Q) (B -> C)) (a : (R ∘ Q) A),
      fappc h (fappc f a) = fappc (fappc (fappc (purec (@compose A B C)) h) f) a.
  Proof.
    intros. unfold fappc, purec.
    repeat rewrite app_fmap_pure.
    repeat rewrite app_composition with
        (h0 := @pure R _ _ (@fapp Q _ _ _)).
    repeat rewrite app_homomorphism.
    rewrite app_composition with
        (@fapp R _ _ _ (@pure R _ _ (@fapp Q _ _ _)) f)
        (@fapp R _ _ _ (@pure R _ _ (@fapp Q _ _ _)) h) a.
    apply f_2_arg. repeat rewrite <- app_fmap_pure.
    pose proof @fmap_compose R _ as H. unfold compose in H.
    pose proof H _ _ _ (@fapp Q _ _ _)
         (@compose (Q A) (Q B) (Q C)) as H'.
    apply equal_f with h in H'. rewrite <- H'; clear H'.
    epose proof H _ _ _ (@fapp Q _ _ _) (compose (@fapp Q _ _ _)) as H'.
    apply equal_f with
        (((@pure R _ _) ∘ (@pure Q _ _)) (@compose A B C)) in H'.
    rewrite <- H'; clear H'. repeat rewrite app_fmap_pure.
    repeat rewrite app_composition. apply f_2_arg.
    repeat rewrite app_homomorphism.
    repeat rewrite app_interchange.
    unfold compose. repeat rewrite app_homomorphism.
    repeat rewrite <- app_fmap_pure.
    pose proof H _ _ _
         (fun (a0 : Q (B -> C))
            (f0 : Q (A -> B) -> Q A -> Q B)
            (a1 : Q (A -> B)) (a2 : Q A)
          => @fapp Q _ _ _ a0 (f0 a1 a2))
         (fun h0 : (Q (A -> B) -> Q A -> Q B) ->
                 Q (A -> B) -> Q A -> Q C => h0 (@fapp Q _ _ _)) as H'.
    apply equal_f with h in H'. rewrite <- H'; clear H'. apply f_2_arg.
    extensionality q. extensionality r. extensionality s.
    repeat rewrite app_composition. unfold compose.
    rewrite <- app_fmap_pure. reflexivity.
  Qed.

  Lemma app_fmap_purec : forall {A B : Type} (f : A -> B),
      fmapc f = fappc (purec f).
  Proof.
    intros. unfold fappc, fmapc, purec. unfold compose.
    repeat rewrite app_fmap_pure. apply f_equal.
    rewrite app_homomorphism. reflexivity.
  Qed.
End ApplicativeComposition.

Instance ComposeApplicative (Q R : Type -> Type)
         `{Applicative Q} `{Applicative R} : Applicative (R ∘ Q) :=
  { pure := @purec Q R _ _;
    fapp := @fappc Q R _ _;
    app_identity := @app_identityc Q R _ _;
    app_homomorphism := @app_homomorphismc Q R _ _;
    app_interchange := @app_interchangec Q R _ _;
    app_composition := @app_compositionc Q R _ _;
    app_fmap_pure := @app_fmap_purec Q R _ _ }.
(**[]*)

Module ApplicativeCompose (Q R : ApplicativeSpec) <: ApplicativeSpec.
  (** Composing the Functors. *)
  Module QR := FunctorComposeSpec Q R.
  Include QR.

  Definition pure {A : Type} : A -> F A := R.pure ∘ Q.pure.

  Definition fapp {A B : Type} (f : F (A -> B)) : F A -> F B :=
    R.fapp (R.fmap Q.fapp f).

  Lemma app_identity : forall {A : Type} (a : F A),
      fapp (pure (fun x => x)) a = a.
  Proof.
    intros. unfold fapp, pure.
    rewrite R.app_fmap_pure. unfold compose.
    Search (R.fapp (R.pure _)). rewrite R.app_homomorphism.
    Search (R.fapp (R.pure _)). rewrite <- R.app_fmap_pure.
    rewrite <- Q.app_fmap_pure.
    Search Q.fmap. rewrite Q.fmap_id.
    rewrite R.fmap_id. reflexivity.
  Qed.

  Lemma app_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
      fapp (pure f) (pure a) = pure (f a).
  Proof.
    intros. unfold fapp, pure.
    rewrite R.app_fmap_pure. unfold compose.
    repeat rewrite R.app_homomorphism. apply f_equal.
    apply Q.app_homomorphism.
  Qed.

  Lemma app_interchange : forall {A B : Type} (f : F (A -> B)) (a : A),
      fapp f (pure a) = fapp (pure (fun h => h a)) f.
  Proof.
    intros. unfold fapp, pure. unfold compose.
    repeat rewrite R.app_fmap_pure.
    repeat rewrite R.app_homomorphism.
    rewrite R.app_interchange. Search (R.fapp (R.pure _)).
    repeat rewrite <- R.app_fmap_pure. Search R.fmap.
    pose proof @R.fmap_compose as H. unfold compose in H.
    pose proof H _ _ _ Q.fapp (fun h : Q.F A -> Q.F B => h (Q.pure a)) as H'.
    Check equal_f. apply equal_f with f in H'.
    rewrite <- H'; clear H' H. apply f_2_arg.
    extensionality q. apply Q.app_interchange.
  Qed.

  Lemma app_composition :
    forall {A B C : Type} (f : F (A -> B)) (h : F (B -> C)) (a : F A),
      fapp h (fapp f a) = fapp (fapp (fapp (pure (@compose A B C)) h) f) a.
  Proof.
    intros. unfold fapp, pure.
    repeat rewrite R.app_fmap_pure.
    repeat rewrite R.app_composition with (h0 := R.pure Q.fapp).
    repeat rewrite R.app_homomorphism.
    rewrite R.app_composition with (R.fapp (R.pure Q.fapp) f)
                                   (R.fapp (R.pure Q.fapp) h) a.
    apply f_2_arg. repeat rewrite R.app_homomorphism.
    repeat rewrite <- R.app_fmap_pure.
    pose proof @R.fmap_compose as H. unfold compose in H.
    pose proof H _ _ _ Q.fapp (@compose (Q.F A) (Q.F B) (Q.F C)) as H'.
    apply equal_f with h in H'. rewrite <- H'; clear H'.
    epose proof H _ _ _ Q.fapp (compose Q.fapp) as H'.
    apply equal_f with ((R.pure ∘ Q.pure) (@compose A B C)) in H'.
    rewrite <- H'; clear H'. repeat rewrite R.app_fmap_pure.
    repeat rewrite R.app_composition. apply f_2_arg.
    repeat rewrite R.app_homomorphism.
    repeat rewrite R.app_interchange.
    unfold compose. repeat rewrite R.app_homomorphism.
    repeat rewrite <- R.app_fmap_pure.
    pose proof H _ _ _
         (fun (a0 : Q.F (B -> C))
            (f0 : Q.F (A -> B) -> Q.F A -> Q.F B)
            (a1 : Q.F (A -> B)) (a2 : Q.F A)
          => Q.fapp a0 (f0 a1 a2))
         (fun h0 : (Q.F (A -> B) -> Q.F A -> Q.F B) ->
                 Q.F (A -> B) -> Q.F A -> Q.F C => h0 Q.fapp) as H'.
    apply equal_f with h in H'. rewrite <- H'; clear H'. apply f_2_arg.
    extensionality q. extensionality r. extensionality s.
    rewrite Q.app_composition. reflexivity.
  Qed.

  Lemma app_fmap_pure : forall {A B : Type} (f : A -> B),
      fmap f = fapp (pure f).
  Proof.
    intros. unfold fapp, fmap, pure. unfold compose.
    Search R.fmap. repeat rewrite R.app_fmap_pure.
    apply f_equal. symmetry. rewrite Q.app_fmap_pure.
    apply R.app_homomorphism.
  Qed.
End ApplicativeCompose.
