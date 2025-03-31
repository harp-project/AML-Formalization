From Kore Require Export Signature
                         Basics.
From MatchingLogic Require Export extralibrary
                                  Lattice.
From Coq Require Export FunctionalExtensionality.

Set Default Proof Mode "Classic".

Section Syntax.

  Context {Σ : Signature}.

  Inductive Pattern : list sort -> list sort -> sort -> Type :=
  | kore_bevar {ex mu : list sort} {s : sort}
               (idx : InTy s ex) : Pattern ex mu s
  | kore_bsvar {ex mu : list sort} {s : sort}
               (idx : InTy s mu) : Pattern ex mu s
  | kore_fevar {ex mu : list sort} {s : sort}
               (x : evar s) : Pattern ex mu s
  | kore_fsvar {ex mu : list sort} {s : sort}
               (X : svar s) : Pattern ex mu s

  | kore_app   {ex mu : list sort} (* (ss : list sort) (explicit app arg sort)? *)
               (σ : symbol)
               (args : hlist (Pattern ex mu) (arg_sorts σ)) : Pattern ex mu (ret_sort σ)

  | kore_bot   {ex mu : list sort}
               (s : sort) : Pattern ex mu s
  | kore_top   {ex mu : list sort}
               (s : sort) : Pattern ex mu s
  | kore_not   {ex mu : list sort} {s : sort}
               (φ : Pattern ex mu s) : Pattern ex mu s
  | kore_and   {ex mu : list sort} {s : sort}
               (φ1 φ2 : Pattern ex mu s) : Pattern ex mu s
  | kore_or    {ex mu : list sort} {s : sort}
               (φ1 φ2 : Pattern ex mu s) : Pattern ex mu s
  | kore_imp   {ex mu : list sort} {s : sort}
               (φ1 φ2 : Pattern ex mu s) : Pattern ex mu s
  | kore_iff   {ex mu : list sort} {s : sort}
               (φ1 φ2 : Pattern ex mu s) : Pattern ex mu s

  | kore_exists {ex mu : list sort} {s : sort}
                (s_var : sort)
                (φ : Pattern (s_var :: ex) mu s) : Pattern ex mu s
  | kore_forall {ex mu : list sort} {s : sort}
                (s_var : sort)
                (φ : Pattern (s_var :: ex) mu s) : Pattern ex mu s

  | kore_mu     {ex mu : list sort} {s : sort}
                (φ : Pattern ex (s :: mu) s) : Pattern ex mu s
  | kore_nu     {ex mu : list sort} {s : sort}
                (φ : Pattern ex (s :: mu) s) : Pattern ex mu s

  | kore_ceil   {ex mu : list sort} {s1 : sort}
                (s2 : sort)
                (φ : Pattern ex mu s1) : Pattern ex mu s2
  | kore_floor  {ex mu : list sort} {s1 : sort}
                (s2 : sort)
                (φ : Pattern ex mu s1) : Pattern ex mu s2
  | kore_equals {ex mu : list sort} {s1 : sort}
                (s2 : sort)
                (φ1 φ2 : Pattern ex mu s1) : Pattern ex mu s2
  | kore_in     {ex mu : list sort} {s1 : sort}
                (s2 : sort)
                (φ1 φ2 : Pattern ex mu s1) : Pattern ex mu s2

(*   | kore_next     (* (s : sort) ? *) (φ : Pattern)
  | kore_rewrites (* (s : sort) ? *) (φ1 φ2 : Pattern)
  | kore_dv       (s : sort) (s : string) *).

  Section pat_rect.
    Variables
      (P : forall {ex mu s}, Pattern ex mu s -> Type).
    Hypotheses
      (P_bevar : forall {ex mu s} idx, @P ex mu s (kore_bevar idx))
      (P_fevar : forall {ex mu s} x, @P ex mu s (kore_fevar x))
      (P_bsvar : forall {ex mu s} idx, @P ex mu s (kore_bsvar idx))
      (P_fsvar : forall {ex mu s} x, @P ex mu s (kore_fsvar x))

      (P_app : forall {ex mu} σ (args : hlist (Pattern ex mu) (arg_sorts σ)), hlist_rect True (fun s ss x xs pf => prod (P x) pf) args -> P (kore_app σ args))

      (P_bot : forall {ex mu s}, @P ex mu s (kore_bot s))
      (P_top : forall {ex mu s}, @P ex mu s (kore_top s))
      (P_not : forall {ex mu s} (φ : Pattern ex mu s), P φ -> P (kore_not φ))
      (P_and : forall {ex mu s} (φ : Pattern ex mu s), P φ -> forall ψ, P ψ -> P (kore_and φ ψ))
      (P_or : forall {ex mu s} (φ : Pattern ex mu s), P φ -> forall ψ, P ψ -> P (kore_or φ ψ))
      (P_imp : forall {ex mu s} (φ : Pattern ex mu s), P φ -> forall ψ, P ψ -> P (kore_imp φ ψ))
      (P_iff : forall {ex mu s} (φ : Pattern ex mu s), P φ -> forall ψ, P ψ -> P (kore_iff φ ψ))

      (P_exists : forall {ex mu s} s_var φ, @P (s_var :: ex) mu s φ -> @P ex mu s (kore_exists s_var φ))
      (P_forall : forall {ex mu s} s_var φ, @P (s_var :: ex) mu s φ -> @P ex mu s (kore_forall s_var φ))
      (P_mu : forall {ex mu s} φ, @P ex (s :: mu) s φ -> @P ex mu s (kore_mu φ))
      (P_nu : forall {ex mu s} φ, @P ex (s :: mu) s φ -> @P ex mu s (kore_nu φ))

      (P_ceil : forall {ex mu s1} s2 φ, @P ex mu s1 φ -> P (kore_ceil s2 φ))
      (P_floor : forall {ex mu s1} s2 φ, @P ex mu s1 φ -> P (kore_floor s2 φ))
      (P_equal : forall {ex mu s1} s2 φ, @P ex mu s1 φ -> forall ψ, @P ex mu s1 ψ -> P (kore_equals s2 φ ψ))
      (P_in : forall {ex mu s1} s2 φ, @P ex mu s1 φ -> forall ψ, @P ex mu s1 ψ -> P (kore_in s2 φ ψ)).

    Definition Pat_rect {ex mu s} (φ : Pattern ex mu s) : P φ.
    Proof.
      revert ex mu s φ.

      refine (fix Pat_rect {ex mu s} (φ : Pattern ex mu s) :=
      match φ with
       | kore_bevar dbi => P_bevar dbi
       | kore_fevar x => P_fevar x
       | kore_bsvar dbi => P_bsvar dbi
       | kore_fsvar x => P_fsvar x

       | kore_app σ args => _

       | kore_bot s => P_bot
       | kore_top s => P_top
       | kore_not φ => P_not _ (Pat_rect φ)
       | kore_and φ1 φ2 => P_and _ (Pat_rect φ1) _ (Pat_rect φ2)
       | kore_or  φ1 φ2 => P_or _ (Pat_rect φ1) _ (Pat_rect φ2)
       | kore_imp φ1 φ2 => P_imp _ (Pat_rect φ1) _ (Pat_rect φ2)
       | kore_iff φ1 φ2 => P_iff _ (Pat_rect φ1) _ (Pat_rect φ2)

       | kore_exists s φ => P_exists s _ (Pat_rect φ)
       | kore_forall s φ => P_forall s _ (Pat_rect φ)

       | kore_mu φ => P_mu _ (Pat_rect φ)
       | kore_nu φ => P_nu _ (Pat_rect φ)

       | kore_ceil s2 φ => P_ceil s2 _ (Pat_rect φ)
       | kore_floor s2 φ => P_floor s2 _ (Pat_rect φ)
       | kore_equals s2 φ1 φ2 => P_equal s2 _ (Pat_rect φ1) _ (Pat_rect φ2)
       | kore_in    s2 φ1 φ2 => P_in s2 _ (Pat_rect φ1) _ (Pat_rect φ2)
      end).
      apply P_app.
      induction args; simpl. 1: exact I.
        split. 2: exact IHargs.
        apply Pat_rect.
    Defined.
  End pat_rect.

  Section pat_ind.
    Variables
      (P : forall {ex mu s}, Pattern ex mu s -> Prop).
    Hypotheses
      (P_bevar : forall {ex mu s} idx, @P ex mu s (kore_bevar idx))
      (P_fevar : forall {ex mu s} x, @P ex mu s (kore_fevar x))
      (P_bsvar : forall {ex mu s} idx, @P ex mu s (kore_bsvar idx))
      (P_fsvar : forall {ex mu s} x, @P ex mu s (kore_fsvar x))

      (P_app : forall {ex mu} σ (args : hlist (Pattern ex mu) (arg_sorts σ)), hlist_rect True (fun s ss x xs pf => (P x) /\ pf) args -> P (kore_app σ args))

      (P_bot : forall {ex mu s}, @P ex mu s (kore_bot s))
      (P_top : forall {ex mu s}, @P ex mu s (kore_top s))
      (P_not : forall {ex mu s} (φ : Pattern ex mu s), P φ -> P (kore_not φ))
      (P_and : forall {ex mu s} (φ : Pattern ex mu s), P φ -> forall ψ, P ψ -> P (kore_and φ ψ))
      (P_or : forall {ex mu s} (φ : Pattern ex mu s), P φ -> forall ψ, P ψ -> P (kore_or φ ψ))
      (P_imp : forall {ex mu s} (φ : Pattern ex mu s), P φ -> forall ψ, P ψ -> P (kore_imp φ ψ))
      (P_iff : forall {ex mu s} (φ : Pattern ex mu s), P φ -> forall ψ, P ψ -> P (kore_iff φ ψ))

      (P_exists : forall {ex mu s} s_var φ, @P (s_var :: ex) mu s φ -> @P ex mu s (kore_exists s_var φ))
      (P_forall : forall {ex mu s} s_var φ, @P (s_var :: ex) mu s φ -> @P ex mu s (kore_forall s_var φ))
      (P_mu : forall {ex mu s} φ, @P ex (s :: mu) s φ -> @P ex mu s (kore_mu φ))
      (P_nu : forall {ex mu s} φ, @P ex (s :: mu) s φ -> @P ex mu s (kore_nu φ))

      (P_ceil : forall {ex mu s1} s2 φ, @P ex mu s1 φ -> P (kore_ceil s2 φ))
      (P_floor : forall {ex mu s1} s2 φ, @P ex mu s1 φ -> P (kore_floor s2 φ))
      (P_equal : forall {ex mu s1} s2 φ, @P ex mu s1 φ -> forall ψ, @P ex mu s1 ψ -> P (kore_equals s2 φ ψ))
      (P_in : forall {ex mu s1} s2 φ, @P ex mu s1 φ -> forall ψ, @P ex mu s1 ψ -> P (kore_in s2 φ ψ)).
    Definition Pat_ind {ex mu s} (φ : Pattern ex mu s) : P φ.
    Proof.
      revert ex mu s φ.

      refine (fix Pat_ind {ex mu s} (φ : Pattern ex mu s) :=
      match φ with
       | kore_bevar dbi => P_bevar dbi
       | kore_fevar x => P_fevar x
       | kore_bsvar dbi => P_bsvar dbi
       | kore_fsvar x => P_fsvar x

       | kore_app σ args => _

       | kore_bot s => P_bot
       | kore_top s => P_top
       | kore_not φ => P_not _ (Pat_ind φ)
       | kore_and φ1 φ2 => P_and _ (Pat_ind φ1) _ (Pat_ind φ2)
       | kore_or  φ1 φ2 => P_or _ (Pat_ind φ1) _ (Pat_ind φ2)
       | kore_imp φ1 φ2 => P_imp _ (Pat_ind φ1) _ (Pat_ind φ2)
       | kore_iff φ1 φ2 => P_iff _ (Pat_ind φ1) _ (Pat_ind φ2)

       | kore_exists s φ => P_exists s _ (Pat_ind φ)
       | kore_forall s φ => P_forall s _ (Pat_ind φ)

       | kore_mu φ => P_mu _ (Pat_ind φ)
       | kore_nu φ => P_nu _ (Pat_ind φ)

       | kore_ceil s2 φ => P_ceil s2 _ (Pat_ind φ)
       | kore_floor s2 φ => P_floor s2 _ (Pat_ind φ)
       | kore_equals s2 φ1 φ2 => P_equal s2 _ (Pat_ind φ1) _ (Pat_ind φ2)
       | kore_in    s2 φ1 φ2 => P_in s2 _ (Pat_ind φ1) _ (Pat_ind φ2)
      end).
      apply P_app.
      induction args; simpl. 1: exact I.
        split. 2: exact IHargs.
        apply Pat_ind.
    Defined.

  End pat_ind.

  Fixpoint pat_size {ex mu s} (p : Pattern ex mu s) : nat :=
  match p with
   | kore_imp φ1 φ2 | kore_iff φ1 φ2
   | kore_and φ1 φ2 | kore_or φ1 φ2
   | kore_equals _ φ1 φ2 | kore_in _ φ1 φ2
      => 1 + pat_size φ1 + pat_size φ2
   | kore_app σ args
      => 1 + hlist_rect 0 (λ _ _ a _ b, pat_size a + b) args
   | kore_exists _ φ | kore_forall _ φ
   | kore_nu φ | kore_mu φ 
   | kore_not φ | kore_ceil _ φ
   | kore_floor _ φ
       => 1 + pat_size φ
   | kore_bevar _ | kore_fevar _
   | kore_bsvar _ | kore_fsvar _
   | kore_bot _ | kore_top _
       => 1
  end.

  Definition Theory := propset (sigT (Pattern [] [])).

End Syntax.

Module Notations.

  Declare Scope kore_scope.
  Delimit Scope kore_scope with kore.

  Notation "'⊥{' s '}'" := (kore_bot s) (format "'⊥{' s '}'") : kore_scope.
  Check ⊥{ _ }%kore.
  Notation "'Top{' s '}'" := (kore_top s) (format "'Top{' s '}'") : kore_scope.
  Check Top{ _ }%kore.
  Notation "'!' p" := (kore_not p) (at level 71, format "'!'  p") : kore_scope.
  Check (! ⊥{_})%kore.
  Notation "p1 'and' p2" := (kore_and p1 p2) (at level 72, format "p1  'and'  p2", left associativity) : kore_scope.
  Check (⊥{_} and Top{_})%kore.
  Notation "p1 'or' p2" := (kore_or p1 p2) (at level 73, format "p1  'or'  p2", left associativity) : kore_scope.
  Check (⊥{_} or Top{_})%kore.
  Notation "p1 '--->' p2" := (kore_imp p1 p2) (at level 75, format "p1  '--->'  p2", right associativity) : kore_scope.
  Check (⊥{_} ---> Top{_})%kore.
  Notation "p1 '<--->' p2" := (kore_iff p1 p2) (at level 74, format "p1  '<--->'  p2") : kore_scope.
  Check (⊥{_} <---> Top{_})%kore.

  Notation "s ⋅ pars" := (kore_app s pars) (at level 50, format "s  '⋅'  pars") : kore_scope.
  Fail Check (_ ⋅ [Top{_}; Top{_}]%hlist)%kore.


  Notation "∃ s1 ',' p" := (kore_exists s1 p) (at level 80, format "∃  s1 ','  p") : kore_scope.
  Check (∃ _ , ⊥{_})%kore.
  Notation "∀ s1 ',' p" := (kore_forall s1 p) (at level 80, format "∀  s1 ','  p") : kore_scope.
  Check (∀ _ , ⊥{_})%kore.

  Notation "μ ',' p" := (kore_mu p) (at level 80, format "μ ','  p") : kore_scope.
  Check (μ , ⊥{_})%kore.
  Notation "ν ',' p" := (kore_nu p) (at level 80, format "ν ','  p") : kore_scope.
  Check (ν , ⊥{_})%kore.

  Notation "'⌈{' s2 '}' p ⌉" := (kore_ceil s2 p) (format "'⌈{' s2 '}'  p ⌉") : kore_scope.
  Check (⌈{_} ⊥{_}⌉)%kore.
  Notation "'⌊{' s2 '}' p ⌋" := (kore_floor s2 p) (format "'⌊{' s2 '}'  p ⌋") : kore_scope.
  Check ⌊{_} ⊥{_}⌋%kore.
  Notation "p1 '=k{' s2 '}' p2" := (kore_equals s2 p1 p2) (at level 68, format "p1  '=k{' s2 '}'  p2", left associativity) : kore_scope.
  Check (⊥{_} =k{_} Top{_})%kore.
  Notation "p1 '⊆k{' s2 '}' p2" := (kore_in s2 p1 p2) (at level 68, format "p1  '⊆k{' s2 '}'  p2", left associativity) : kore_scope.
  Check (⊥{_} ⊆k{_} Top{_})%kore.




(*   Notation "''" := (kore_is_sort s).
  Notation := (kore_is_predicate s p).
  Notation := (kore_is_nonempty_sort s). *)

  (* Notation "'mu' s , p" := (kore_mu s p) (at level 80).
  Check mu Nat, ⊥.
  Notation "'nu' s , p" := (kore_nu s p) (at level 80).
  Check nu Nat, ⊥. *)

  (* Notation "'•(' s ')' p"    := (kore_next s p) (at level 30, format "'•(' s ')'  p") : kore_scope.
  Check •(Nat) ⊥.
  Notation "'○(' s ')' p"    := (kore_all_path_next s p) (at level 71, format "'○(' s ')'  p") : kore_scope.
  Check ○(Nat) ⊥.
  Notation "'⋄(' s ')' p"    := (kore_eventually s p) (at level 71, format "'⋄(' s ')'  p") : kore_scope.
  Check ⋄(Nat) ⊥.
  Notation "'⋄ʷ(' s ')' p"   := (kore_weak_eventually s p) (at level 71, format "'⋄ʷ(' s ')'  p") : kore_scope.
  Check ⋄ʷ(Nat) ⊥.
(*   Notation "s"       := (kore_well_founded s) (at level 71) : kore_scope. *)
(*   Notation ""       := (kore_well_founded_alt s) (at level 71) : kore_scope. *)
  Notation "'⊞(' s ')' p"    := (kore_always s p) (at level 71, format "'⊞(' s ')'  p") : kore_scope. (* □ is taken by application contexts *)
  Check ⊞(Nat) ⊥.
  Notation "p '=(' s ')=>' q"  := (kore_rewrites s p q) (at level 81, format "p  '=(' s ')=>'  q") : kore_scope.
  Check ⊥ =(Nat)=> Top.
  Notation "p '=(' s ')=>*' q" := (kore_rewrites_star s p q) (at level 81, format "p  '=(' s ')=>*'  q") : kore_scope.
  Check ⊥ =(Nat)=>* Top.
  Notation "p '=(' s ')=>⁺' q" := (kore_rewrites_plus s p q) (at level 81, format "p  '=(' s ')=>⁺'  q") : kore_scope.
  Check ⊥ =(Nat)=>⁺ Top.

(* These probably don't need notations:
  Notation "" := (kore_one_path_reaches_star s p1 p2).
  Notation := (kore_one_path_reaches_plus s p1 p2). *)
  Notation "'↺(' s ')' p" := (kore_circularity s p) (at level 71, format "'↺(' s ')'  p").
  Check ↺(Nat) ⊥.
  Notation "s ⇑" := (kore_non_terminating s) (at level 90).
  Check ⊥ ⋅ ⊥ ⇑. *)

End Notations.

(*
Section Sortedness.
  Import Notations.
  Context {Σ : Signature}.
  Open Scope kore_scope.

  Definition shift {T : Set} (f : nat -> T) (d : T)
    : nat -> T :=
    fun n => match n with
              | O => d
              | S n' => f n'
             end.

  Definition update {T : Set} (n : nat) (d : T) (f : nat -> T)
    : nat -> T :=
    fun m => if decide (n = m) then d else f m.

  Fixpoint app_ws (well_sorted : sort -> Pattern -> bool)
                  (φs : list Pattern)
                  (ss : list sort) {struct φs} :=
    match φs, ss with
    | [], [] => true
    | φ::φs, s::ss => well_sorted s φ &&
                      app_ws well_sorted φs ss
    | _, _ => false
    end.

  Fixpoint well_sorted
    (esorts : nat -> option sort)
    (ssorts : nat -> option sort)
    (s : sort)
    (p : Pattern) {struct p} : bool :=
    match p with
     | kore_bot s => true
     | kore_top s => true
     | kore_bevar dbi => decide (esorts dbi = Some s)
     | kore_bsvar dbi => decide (ssorts dbi = Some s)
     | kore_fevar x => decide (evar_sort x = s)
     | kore_fsvar X => decide (svar_sort X = s)
     | kore_imp φ1 φ2 | kore_iff φ1 φ2
     | kore_and φ1 φ2 | kore_or φ1 φ2
       => well_sorted esorts ssorts s φ1 &&
          well_sorted esorts ssorts s φ2
     | kore_not φ => well_sorted esorts ssorts s φ
     | kore_app σ args =>
        decide (s = ret_sort σ) &&
        app_ws (well_sorted esorts ssorts) args (arg_sorts σ)
     | kore_exists s0 φ | kore_forall s0 φ =>
        well_sorted (shift esorts (Some s0)) ssorts s φ
     | kore_mu s0 φ | kore_nu s0 φ =>
        well_sorted esorts (shift ssorts (Some s0)) s φ
     | kore_ceil s1 s2 φ | kore_floor s1 s2 φ
        => well_sorted esorts ssorts s1 φ &&
           decide (s2 = s)
     | kore_equals s1 s2 φ1 φ2 | kore_in s1 s2 φ1 φ2
        => well_sorted esorts ssorts s1 φ1 &&
           well_sorted esorts ssorts s1 φ2 &&
           decide (s2 = s)
    end.

  Definition default : nat -> option sort := fun _ : nat => None.

  Definition is_weaker (f1 f2 : nat -> option sort) : Prop :=
    forall n s, f2 n = Some s -> f1 n = Some s.

  Notation "f '≤ₛ' g" := (is_weaker f g) (at level 50).

  Lemma default_is_strongest :
    forall f, f ≤ₛ default.
  Proof.
    intros f n σ H.
    unfold default in H.
    inversion H.
  Defined.

  Lemma is_weaker_refl :
    forall f, f ≤ₛ f.
  Proof.
    intros. intro. intros.
    assumption.
  Defined.

  Lemma is_weaker_shift :
    forall f1 f2,
      f1 ≤ₛ f2 ->
      forall d,
        (shift f1 d) ≤ₛ (shift f2 d).
  Proof.
    intros.
    unfold is_weaker.
    intros.
    destruct n; simpl in *. assumption.
    by apply H.
  Defined.


  Lemma shift_update :
    forall {T: Set} (f : nat -> T) n d1 d2,
      shift (update n d1 f) d2 =
      update (S n) d1 (shift f d2).
  Proof.
    intros. unfold shift, update.
    extensionality x.
    destruct x; simpl. reflexivity.
    destruct decide; simpl;
    destruct decide; simpl; try lia; reflexivity.
  Defined.

  Lemma well_sorted_weaken :
    forall φ s fe fe' fs fs',
      fe' ≤ₛ fe ->
      fs' ≤ₛ fs ->
      well_sorted fe fs s φ ->
      well_sorted fe' fs' s φ.
  Proof.
    induction φ using Pat_rect; intros * Hw1 Hw2 Hwf; try by constructor.
    * simpl in *. destruct decide. 2: simpl in Hwf; congruence.
      clear Hwf. apply Hw1 in e.
      cbn. rewrite e. destruct decide; auto.
    * simpl in *. assumption.
    * simpl in *. destruct decide. 2: simpl in Hwf; congruence.
      clear Hwf. apply Hw2 in e.
      cbn. rewrite e. destruct decide; auto.
    * simpl in *. assumption.
    * simpl in *.
      apply andb_split_1 in Hwf as H1. rewrite H1. simpl.
      apply andb_split_2 in Hwf.
      {
        clear - H Hwf Hw1 Hw2.
        remember (arg_sorts σ) as sorts.
        clear Heqsorts. revert sorts Hwf.
        induction args; simpl in *; intros.
        + case_match; by auto.
        + case_match. by auto.
          subst.
          inversion H. subst. erewrite H2. 2-3: eassumption.
          2: by apply andb_split_1 in Hwf.
          eapply IHargs. assumption.
          by apply andb_split_2 in Hwf.
      }
    * simpl in *. eapply IHφ in Hwf; eassumption.
    * simpl in *. apply andb_true_iff in Hwf as [Hwf1 Hwf2].
      erewrite IHφ1; try eassumption.
      erewrite IHφ2; try eassumption.
      reflexivity.
    * simpl in *. apply andb_true_iff in Hwf as [Hwf1 Hwf2].
      erewrite IHφ1; try eassumption.
      erewrite IHφ2; try eassumption.
      reflexivity.
    * simpl in *. apply andb_true_iff in Hwf as [Hwf1 Hwf2].
      erewrite IHφ1; try eassumption.
      erewrite IHφ2; try eassumption.
      reflexivity.
    * simpl in *. apply andb_true_iff in Hwf as [Hwf1 Hwf2].
      erewrite IHφ1; try eassumption.
      erewrite IHφ2; try eassumption.
      reflexivity.
    * simpl in *. eapply IHφ in Hwf. exact Hwf.
      by apply is_weaker_shift.
      assumption.
    * simpl in *. eapply IHφ in Hwf. exact Hwf.
      by apply is_weaker_shift.
      assumption.
    * simpl in *. eapply IHφ in Hwf. exact Hwf.
      2: by apply is_weaker_shift.
      assumption.
    * simpl in *. eapply IHφ in Hwf. exact Hwf.
      2: by apply is_weaker_shift.
      assumption.
    * simpl in *.
      erewrite IHφ; try eassumption.
      simpl. apply andb_split_2 in Hwf. assumption.
      simpl. apply andb_split_1 in Hwf. assumption.
    * simpl in *.
      erewrite IHφ; try eassumption.
      simpl. apply andb_split_2 in Hwf. assumption.
      simpl. apply andb_split_1 in Hwf. assumption.
    * simpl in *.
      erewrite IHφ1; try eassumption.
      erewrite IHφ2; try eassumption.
      simpl. apply andb_split_2 in Hwf. assumption.
      simpl. apply andb_split_1, andb_split_2 in Hwf. assumption.
      simpl. apply andb_split_1, andb_split_1 in Hwf. assumption.
    * simpl in *.
      erewrite IHφ1; try eassumption.
      erewrite IHφ2; try eassumption.
      simpl. apply andb_split_2 in Hwf. assumption.
      simpl. apply andb_split_1, andb_split_2 in Hwf. assumption.
      simpl. apply andb_split_1, andb_split_1 in Hwf. assumption.
  Defined.

End Sortedness. *)

