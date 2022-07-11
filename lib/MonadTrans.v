Require Coq.Lists.List.
Require Export TypeClasses.Monad.

(** * The Monad Transformer Type Class. *)

Class MonadTrans
      (T : (Type -> Type) -> Type -> Type) :=
  { (** Monadic Substructure *)
    Trans_Monad :> forall (M : Type -> Type) `{Monad M}, Monad (T M);
    lift : forall {M : Type -> Type} `{Monad M}
             {A : Type}, M A -> T M A;
    (** Lift with pure is idempotent. *)
    lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
      lift (M := M) (A := A) ∘ (pure (F := M)) = pure (F := T M);
    (** Lift composes with bind. *)
    lift_bind : forall {M : Type -> Type} `{Monad M}
                  {A B : Type} (m : M A) (f : A -> M B),
      lift (m >>= f) = lift m >>= lift ∘ f }.

(** Specification. *)
Module Type MonadTransSpec.
  Parameter T : (Type -> Type) -> Type -> Type.

  Parameter TMonad : forall (M : Type -> Type) `{Monad M}, Monad (T M).

  Parameter lift : forall {M : Type -> Type} `{Monad M}
                     {A : Type}, M A -> T M A.

  Axiom lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
      @lift M _ A ∘ (@pure M _ A) =
      @pure (T M) (@Monad_Applicative (T M) (TMonad M)) A.

  Axiom lift_bind : forall {M : Type -> Type} `{Monad M}
                          {A B : Type} (m : M A) (f : A -> M B),
      lift (m >>= f) = @bind (T M) (TMonad M) _ _ (lift m) (lift ∘ f).
End MonadTransSpec.

Module MonadTransFactory (MS : MonadTransSpec).
  Include MS.

  Instance MonadTransInstance : MonadTrans MS.T :=
    { lift := @MS.lift;
      lift_pure := @MS.lift_pure;
      lift_bind := @MS.lift_bind }.
End MonadTransFactory.

(** Identity. *)
Module IdentityMonadTransSpec <: MonadTransSpec.
  Definition T : (Type -> Type) -> Type -> Type := fun M => M.

  Instance TMonad (M : Type -> Type) `{HM : Monad M} : Monad M := HM.

  Definition lift {M : Type -> Type} `{Monad M}
             {A : Type} : M A -> M A := fun m => m.

  Lemma lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
      @lift M _ A ∘ (@pure M _ A) =
      @pure M (@Monad_Applicative M (TMonad M)) A.
  Proof. intros. unfold lift. extensionality m. reflexivity. Qed.

  Lemma lift_bind : forall {M : Type -> Type} `{Monad M}
                      {A B : Type} (m : M A) (f : A -> M B),
      lift (m >>= f) = lift m >>= lift ∘ f.
  Proof. intros. reflexivity. Qed.
End IdentityMonadTransSpec.

Module IdentityMonadTransFactory :=
  MonadTransFactory IdentityMonadTransSpec.
Instance IdentityMonadTrans : MonadTrans (fun M : Type -> Type => M) :=
  IdentityMonadTransFactory.MonadTransInstance.

(** Option. *)
Module OptionMonadTransSpec <: MonadTransSpec.
  Definition T (M : Type -> Type) : Type -> Type := M ∘ option.

  Instance TApplicative (M : Type -> Type)
           `{HM : Monad M} : Applicative (M ∘ option) :=
    ComposeApplicative option M.

  Section TMonadSpec.
    Context {M : Type -> Type}.

    Context `{HM : Monad M}.

    Definition bindt {A B : Type}
               (m : M (option A)) (f : A -> M (option B)) : M (option B) :=
      let* o := m in
      match o with
      | None   => pure None
      | Some a => (f a)
      end.

    Lemma pure_leftt : forall {A B : Type} (a : A) (f : A -> M (option B)),
        bindt (pure (F := M ∘ option)a) f = f a.
    Proof.
      intros. pose proof @pure_left M HM (option A) (option B) as H.
      unfold bindt. simpl. unfold purec. unfold compose.
      rewrite H. simpl. reflexivity.
    Qed.

    Lemma pure_rightt : forall {A : Type} (m : M (option A)),
        bindt m (pure (F := M ∘ option) (A:=A)) = m.
    Proof.
      intros. unfold bindt. simpl. unfold purec.
      unfold compose.
      assert (H : (fun o : option A =>
                     match o with
                     | Some a => @pure M _ _ (@pure option _ _ a)
                     | None => @pure M _ _ None
                     end) = (fun o : option A =>
                               @pure M _ _
                                     (match o with
                                      | Some a => @pure option _ _ a
                                      | None => None
                                      end))).
      { extensionality o; destruct o; auto. }
      rewrite H; clear H.
      assert (H : (fun o : option A =>
                     @pure M _ _
                           match o with
                           | Some a => pure a
                           | None => None
                           end) =
                  (fun o : option A => @pure M _ _ o)).
      { extensionality o; destruct o; auto. }
      rewrite H. apply pure_right.
    Qed.

    Lemma bind_assoct :
      forall {A B C : Type} (m : M (option A))
        (k : A -> M (option B)) (h : B -> M (option C)),
        bindt m (fun a => bindt (k a) h) = bindt (bindt m k) h.
    Proof.
      intros. unfold bindt.
      rewrite <- (@bind_assoc M). apply f_equal.
      extensionality o. destruct o as [a |]; auto.
      rewrite pure_left. reflexivity.
    Qed.
    
    Lemma fmap_bindt : forall {A B : Type} (m : M (option A)) (f : A -> B),
        fmap (F := M ∘ option) f m = bindt m (pure (F := M ∘ option) ∘ f).
    Proof.
      intros. unfold bindt.
      assert (hanon :
               (fun o =>
                  match o with
                  | Some a => (pure (F := M ∘ option) ∘ f) a
                  | None => pure (F := M) None
                  end)
               = pure (F := M) ∘ (fmap f)).
      { extensionality o. unfold "∘".
        destruct o; reflexivity. }
      unfold "∘" in *.
      rewrite hanon; clear hanon.
      pose proof fmap_bind m (fmap f) as h.
      unfold "∘" in *.
      unfold OptionMonadSpec.F in h.
      rewrite <- h; clear h. reflexivity.
    Qed.
  End TMonadSpec.

  Instance TMonad : forall (M : Type -> Type) `{Monad M}, Monad (M ∘ option) :=
    { bind := @bindt M _;
      pure_left := @pure_leftt M _;
      pure_right := @pure_rightt M _;
      bind_assoc := @bind_assoct M _;
      fmap_bind := @fmap_bindt M _ }.

  Definition lift {M : Type -> Type} `{Monad M}
             {A : Type} (m : M A) : M (option A) :=
    @fmap M _ _ _ (@pure option _ _) m.

  Lemma lift_pure : forall {M : Type -> Type} `{Monad M} {A : Type},
      @lift M _ A ∘ (@pure M _ A) =
      @pure (M ∘ option) (@Monad_Applicative (M ∘ option) (TMonad M)) A.
  Proof.
    intros. extensionality a. unfold compose, lift.
    cbn. unfold purec. unfold compose, OptionMonadSpec.pure.
    simpl. unfold OptionMonadSpec.pure.
    rewrite app_fmap_pure.
    apply app_homomorphism.
  Qed.

  Lemma lift_bind : forall {M : Type -> Type} `{Monad M}
                      {A B : Type} (m : M A) (f : A -> M B),
      lift (m >>= f) =
        @bind (M ∘ option) (TMonad M) _ _ (lift m) (lift ∘ f).
  Proof.
    intros. unfold compose. simpl. unfold lift.
    unfold bindt. cbn.
    unfold OptionMonadSpec.pure.
    unfold fmapc, purec, "∘"(*,"<$>"*) in *. cbn in *.
    do 2 rewrite fmap_bind; unfold "∘".
    do 2 rewrite <- bind_assoc. f_equal.
    extensionality a.
    rewrite pure_left. rewrite fmap_bind; reflexivity.
  Qed.
End OptionMonadTransSpec.

Module OptionMonadTransFactory :=
  MonadTransFactory OptionMonadTransSpec.
Instance OptionMonadTrans : MonadTrans (fun M : Type -> Type => M ∘ option) :=
  OptionMonadTransFactory.MonadTransInstance.

Definition StateT (ST : Type) (M : Type -> Type) (A : Type) : Type :=
  ST -> M (A * ST)%type.

Lemma StateT_state : forall ST A, StateT ST (fun x => x) A = state ST A.
Proof. intros; reflexivity. Qed.

Definition map_fst {A B C : Type} (f : A -> B) '((a,c) : A * C) : B * C :=
  (f a, c).

Module StateTransformer.
  Section Transformers.
    Context {ST : Type} {M : Type -> Type} `{M_Functor : Functor M}.
    
    Definition fmapt {A B : Type} (f : A -> B) (m : StateT ST M A)
      : StateT ST M B :=
      fun st => map_fst f <$> m st.

    Lemma fmapt_id : forall {A : Type},
        fmapt (fun x : A => x) = (fun x : StateT ST M A => x).
    Proof.
      intros; extensionality bruh.
      extensionality st; unfold fmapt, map_fst.
      assert (duh : (fun '((a, c) : A * ST) => (a, c)) = fun x => x).
      { extensionality ast. destruct ast; reflexivity. }
      rewrite duh; rewrite fmap_id; reflexivity.
    Qed.
    
    Lemma fmapt_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
        fmapt (g ∘ f) = fmapt g ∘ fmapt f.
    Proof.
      intros; unfold fmapt; extensionality bruh;
        extensionality st; unfold map_fst.
      unfold "∘".
      pose proof fmap_compose
           (A := A * ST) (B := B * ST)
           (C := C * ST) (F := M) as h.
      unfold "∘" in h.
      specialize h with
        (f := fun '(a,st) => (f a, st))
        (g := fun '(b,st) => (g b, st)).
      apply equal_f with (bruh st) in h.
      rewrite <- h; clear h; f_equal.
      extensionality ast.
      destruct ast as [a st']; reflexivity.
    Qed.
  End Transformers.
  
  Instance StateTransFunctor (ST : Type) (M : Type -> Type)
           `{M_Functor : Functor M} : Functor (StateT ST M) :=
    { fmap := @fmapt ST M M_Functor
    ; fmap_id := @fmapt_id ST M M_Functor
    ; fmap_compose := @fmapt_compose ST M M_Functor }.

  Section Transformers.
    Context {ST : Type} {M : Type -> Type} `{M_Monad : Monad M}.

    Definition puret {A : Type} (a : A) : StateT ST M A :=
      fun st => pure (a, st).
    
    Definition
      fappt
      {A B : Type} (f : StateT ST M (A -> B))
      (m : StateT ST M A) : StateT ST M B :=
      fun st : ST => let* '((f,st) : (A -> B) * ST) := f st in
                  map_fst f <$> m st.
    
    Lemma appt_identity : forall {A : Type} (m : StateT ST M A),
        fappt (puret (fun x => x)) m = m.
    Proof.
      intros; extensionality st; unfold fappt, puret.
      rewrite pure_left. unfold map_fst.
      assert (h: (fun '(a, c) => (a, c)) = fun x : A * ST => x)
        by (extensionality ac; destruct ac; reflexivity).
      rewrite h, fmap_id; reflexivity.
    Qed.

    Lemma appt_homomorphism : forall {A B : Type} (f : A -> B) (a : A),
        fappt (puret f) (puret a) = puret (f a).
    Proof.
      intros; unfold fappt, puret.
      extensionality st; rewrite pure_left.
      rewrite app_fmap_pure.
      rewrite app_homomorphism.
      reflexivity.
    Qed.

    Lemma appt_interchange : forall {A B : Type} (f : StateT ST M (A -> B)) (a : A),
        fappt f (puret a) = fappt (puret (fun h => h a)) f.
    Proof.
      intros; unfold fappt, puret.
      extensionality st.
      rewrite pure_left.
      rewrite fmap_bind. unfold "∘".
      f_equal. extensionality gst; clear st f.
      destruct gst as [g st']; cbn.
      rewrite app_fmap_pure, app_homomorphism; reflexivity.
    Qed.
                               
    Lemma appt_composition :
      forall {A B C : Type}
        (f : StateT ST M (A -> B)) (h : StateT ST M (B -> C)) (a : StateT ST M A),
        fappt h (fappt f a) = fappt (fappt (fappt (puret (@compose A B C)) h) f) a.
    Proof.
      intros; unfold fappt,puret.
      extensionality st.
      repeat rewrite <- bind_assoc.
      rewrite pure_left.
      rewrite fmap_bind.
      rewrite <- bind_assoc.
      f_equal. clear st.
      unfold "∘". extensionality gst.
      destruct gst as [g st].
      rewrite pure_left; cbn.
      do 2 rewrite fmap_bind.
      do 2 rewrite <- bind_assoc; unfold "∘".
      f_equal. clear st.
      extensionality wst.
      destruct wst as [w st].
      rewrite pure_left, fmap_bind,<- bind_assoc.
      unfold "∘". cbn. rewrite fmap_bind; unfold "∘".
      f_equal; clear st.
      extensionality ast.
      rewrite pure_left.
      destruct ast; reflexivity.
    Qed.
      
    Lemma appt_fmapt_puret : forall {A B : Type} (f : A -> B),
        fmapt f = fappt (puret f).
    Proof.
      intros; unfold fmapt, fappt, puret.
      extensionality m. extensionality st.
      rewrite pure_left; reflexivity.
    Qed.
  End Transformers.
  
  Instance StateTransApplicative (ST : Type) (M : Type -> Type)
           `{HM : Monad M} : Applicative (StateT ST M) :=
    { pure := @puret ST M HM
    ; fapp := @fappt ST M HM
    ; app_identity := @appt_identity ST M HM
    ; app_homomorphism := @appt_homomorphism ST M HM
    ; app_interchange := @appt_interchange ST M HM
    ; app_composition := @appt_composition ST M HM
    ; app_fmap_pure := @appt_fmapt_puret ST M HM }.

  Section Transformers.
    Context {ST : Type} {M : Type -> Type} `{M_Monad : Monad M}.

    Definition
      bindt {A B : Type} (m : StateT ST M A)
      (f : A -> StateT ST M B) : StateT ST M B :=
      fun st => let* '(a,st) := m st in f a st.
    
    Lemma puret_left : forall {A B : Type} (a : A) (f : A -> StateT ST M B),
        bindt (puret a) f = f a.
    Proof.
      intros; unfold bindt, puret.
      extensionality st. rewrite pure_left; reflexivity.
    Qed.
      
    Lemma puret_right : forall {A : Type} (m : StateT ST M A),
        bindt m puret = m.
    Proof.
      intros; unfold bindt, puret.
      extensionality st.
      assert (h: (fun '(a, st) => pure (F := M) (a, st)) = (fun ast : A * ST => pure ast))
        by (extensionality ast; destruct ast; reflexivity).
      rewrite h, pure_right. reflexivity.
    Qed.
      
    Lemma bindt_assoc :
      forall {A B C : Type} (m : StateT ST M A)
        (k : A -> StateT ST M B) (h : B -> StateT ST M C),
        bindt m (fun a => bindt (k a) h) = bindt (bindt m k) h.
    Proof.
      intros; unfold bindt; extensionality st.
      rewrite <- bind_assoc. f_equal.
      clear st. extensionality ast.
      destruct ast as [a ast]; reflexivity.
    Qed.
      
    Lemma fmapt_bindt : forall {A B : Type} (m : StateT ST M A) (f : A -> B),
        fmapt f m = bindt m (puret ∘ f).
    Proof.
      intros; unfold fmapt, bindt, puret, "∘".
      extensionality st.
      rewrite fmap_bind.
      f_equal. clear st; extensionality ast.
      destruct ast; reflexivity.
    Qed.
  End Transformers.

  Instance StateTransFormerMonad (M : Type -> Type) (ST : Type)
           `{HM : Monad M} : Monad (StateT ST M) :=
    { bind := @bindt ST M HM
    ; pure_left := @puret_left ST M HM
    ; pure_right := @puret_right ST M HM
    ; bind_assoc := @bindt_assoc ST M HM
    ; fmap_bind := @fmapt_bindt ST M HM }.
  
  Section Transformers.
    Context {ST : Type} {M : Type -> Type} `{M_Monad : Monad M}.
    
    Definition liftt {A : Type} (m : M A) : StateT ST M A :=
      fun st => let* a := m in pure (a, st).
      
    Lemma liftt_pure : forall {A : Type},
        liftt (A := A) ∘ (pure (F := M)) = puret.
    Proof.
      intros; unfold liftt, puret.
      extensionality m. extensionality st.
      unfold compose. rewrite pure_left.
      reflexivity.
    Qed.
    
    Lemma liftt_bindt : forall {A B : Type} (m : M A) (f : A -> M B),
        liftt (m >>= f) = bindt (liftt m) (liftt ∘ f).
    Proof.
      intros; unfold bindt,liftt,"∘".
      extensionality st.
      do 2 rewrite <- bind_assoc.
      f_equal.
      extensionality a.
      rewrite pure_left. reflexivity.
    Qed.
  End Transformers.
End StateTransformer.

Instance StateMonadTransformer (ST : Type) : MonadTrans (StateT ST) :=
  { lift := @StateTransformer.liftt ST
  ; lift_pure := @StateTransformer.liftt_pure ST
  ; lift_bind := @StateTransformer.liftt_bindt ST }.
