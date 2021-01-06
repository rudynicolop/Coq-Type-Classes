Require Coq.Lists.List.
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
    app_fmap_pure : forall {A B : Type} (f : A -> B),
        fmap f = fapp (pure f) }.

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
Definition IdentityApplicative : Applicative id :=
  IdentityApplicativeFactory.ApplicativeInstance.

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
Definition OptionApplicative : Applicative option :=
  OptionApplicativeFactory.ApplicativeInstance.

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
Definition ListApplicative : Applicative list :=
  ListApplicativeFactory.ApplicativeInstance.
(**[]*)

Module ListPlayground.
  Import Coq.Lists.List.
  Import ListNotations.

  Module AOption := OptionApplicativeSpec.
  Module AList := ListApplicativeSpec.

  Compute pure mult <*> [2;3;4] <*> pure 4.
  Compute mult <$> [2;3;4;5] <*> pure 4.

  (* Composing Applicatives is tricky. *)

  Fixpoint list_option_map {A B : Type} (fs : list (option (A -> B)))
           (a : list (option A)) : list (option B) :=
    match fs with
    | [] => []
    | None   :: t => list_option_map t a
    | Some f :: t => fmap f <$> a ++ list_option_map t a
    end.

  Fixpoint list_option_map' {A B : Type} (fs : list (option (A -> B)))
           (a : list (option A)) : list (option B) :=
    match fs with
    | []     => []
    | fo :: t => pure (fapp fo) <*> a ++ list_option_map' t a
    end.

  Definition list_option_map'' {A B : Type} (fs : list (option (A -> B)))
             (a : list (option A)) : list (option B) :=
    concat ((fun fo => fapp (pure (fapp fo)) <$> a) <$> fs).

  Fixpoint list_option_map''' {A B : Type} (fs : list (option (A -> B)))
           (a : list (option A)) : list (option B) :=
    match a with
    | []       => []
    | None   :: t => list_option_map''' fs t
    | Some h :: t => fmap (fun f => f h) <$> fs ++ list_option_map''' fs t
    end.

  Fixpoint list_option_map'''' {A B : Type} (fs : list (option (A -> B)))
           (a : list (option A)) : list (option B) :=
    match a with
    | []     => []
    | ho :: t => (fun f => f <*> ho) <$> fs ++ list_option_map'''' fs t
    end.

  Definition list_option_map''''' {A B : Type} (fs : list (option (A -> B)))
             (a : list (option A)) : list (option B) :=
    concat ((fun ho => (fun f => f <*> ho) <$> fs) <$> a).
  (** [ fun f  => f <*> ho                        : option (A -> B) -> option B]
      [(fun f  => f <*> ho) <$> fs                : option B]
      [ fun ho => (fun f => f <*> ho)                : option A -> list (option B)]
      [(fun ho => (fun f => f <*> ho) <$> fs) <$> a  : list (option B)]
      [(fun ho => (fun f => f <*> ho) <$> fs) <$> a) : list (list (option B))] *)

  (** Definition fapp {A B : Type} (fs : list (A -> B)) (xs : list A) : list B :=
      concat ((fun f => f <$> xs) <$> fs).
      fs <*> xs = concat ((fun f => f <$> xs) <$> fs). *)

  Definition maybe_fapp {A B : Type} (f : option (list (A -> B)))
             (oa : option (list A)) : option (list B) :=
    match f, oa with
    | None, _ => None
    | _, None => None
    | Some f, Some a => Some (f <*> a)
    end.

  Definition maybe_fapp' {A B : Type} (f : option (list (A -> B)))
             (oa : option (list A)) : option (list B) :=
    match f with
    | None => None
    | Some f => (fun a => f <*> a) <$> oa
    end.

  Definition maybe_fapp''' {A B : Type} (f : option (list (A -> B)))
             (oa : option (list A)) : option (list B) :=
    match oa with
    | None => None
    | Some a => (fun h => h <*> a) <$> f
    end.

  (* Why was this so hard to come up with? *)
  Definition maybe_fapp'''' {A B : Type} (fo : option (list (A -> B)))
             (ao : option (list A)) : option (list B) := fapp <$> fo <*> ao.

  Unset Printing Notations.
  Print maybe_fapp''''.

  Definition maybe_fapp''''' {A B : Type} (fo : option (list (A -> B)))
             (ao : option (list A)) : option (list B) :=
    AOption.fapp (AOption.fmap AList.fapp fo) ao.

  Set Printing Notations.

  Definition list_option_map'''''' {A B : Type} (fs : list (option (A -> B)))
             (a : list (option A)) : list (option B) := fapp <$> fs <*> a.
End ListPlayground.

(** Applicative Composition *)
Module ApplicativeCompose (Q R : ApplicativeSpec) <: ApplicativeSpec.
  (** Composing the Functors. *)
  Module QR := FunctorCompose Q R.
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
Definition EitherApplicative (A : Type) : Applicative (either A) :=
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
Definition ArrowApplicative (A : Type) : Applicative (fun B => A -> B) :=
  ArrowApplicativeFactory.ParamApplicativeInstance A.

(** Binary Trees. *)
Module TreeApplicativeSpec <: ParamApplicativeSpec.
  Include TreeFunctorSpec.

  Section Spec.
    Context {K : Type}.

    (** Need a key... *)
    Definition pure {V : Type} : V -> tree K V := fun _ => Leaf.

    Fixpoint fapp {V R : Type} (f : tree K (V -> R)) (t : tree K V) : tree K R.
    (* This is really confusing..
      match f,t with
      | Leaf, _
      | _, Leaf                  => Leaf
      | Node _ f h k, Node k l r =>
        let l := fapp h
      end. *)
    Admitted.

    Lemma app_identity : forall {V : Type} (t : tree K V),
        fapp (pure (fun x => x)) t = t.
    Admitted.

    Lemma app_homomorphism : forall {V R : Type} (f : V -> R) (v : V),
        fapp (pure f) (pure v) = pure (f v).
    Admitted.

    Lemma app_interchange : forall {V R : Type} (f : tree K (V -> R)) (v : V),
        fapp f (pure v) = fapp (pure (fun h => h v)) f.
    Admitted.

    Lemma app_composition :
      forall {B C D : Type} (f : tree K (B -> C)) (h : tree K (C -> D)) (t : tree K B),
        fapp h (fapp f t) = fapp (fapp (fapp (pure (@compose B C D)) h) f) t.
    Admitted.

    Lemma app_fmap_pure : forall {B C : Type} (f : B -> C),
        fmap f = fapp (pure f).
    Admitted.
  End Spec.
End TreeApplicativeSpec.
