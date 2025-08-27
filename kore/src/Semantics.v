From Equations Require Import Equations.
From Kore Require Export Substitution
                         Freshness
                         Basics.
Require Import Coq.Program.Equality.


Lemma propset_rewrite :
  forall {T C : Type} (P Q : C -> Prop),
    (forall x, P x = Q x) ->
    {[x | P x]} =
    {[x | Q x]}.
Proof.
  intros.
  unfold propset_fa_union.
  apply set_eq; intros.
  do 2 rewrite elem_of_PropSet.
  split; intros.
  * by rewrite -H.
  * by rewrite H.
Qed.

Lemma propset_fa_union_rewrite :
  forall {T C : Type} (P Q : C -> propset T),
    (forall x, P x = Q x) ->
    propset_fa_union (fun x => P x) =
    propset_fa_union (fun x => Q x).
Proof.
  intros.
  unfold propset_fa_union.
  apply set_eq; intros.
  do 2 rewrite elem_of_PropSet.
  split; intros.
  * set_solver.
  * set_solver.
Qed.

Lemma propset_fa_union_empty_2 :
  forall {C T : Type} (P : C -> Prop),
    (forall c, ~P c) ->
    @propset_fa_union T C (fun c => {[ _ | P c]}) = ∅.
Proof.
  intros.
  set_solver.
Qed.

Lemma propset_fa_union_full_2 :
  forall {C T : Type} (P : C -> Prop),
    (exists c, P c) ->
    @propset_fa_union T C (fun c => {[ _ | P c]}) = ⊤.
Proof.
  intros.
  set_solver.
Qed.

Lemma propset_double :
  forall {C1 C2 : Type} (P : C1 -> C2 -> Prop),
    {[ x | ∃ c : C1, x ∈ {[ x0 | P c x0 ]} ]} =
    {[x | ∃ c : C1, P c x]}.
Proof.
  set_solver.
Qed.

Lemma propset_fa_union_double :
  forall {T C1 C2 : Type} (P : C1 -> C2 -> propset T),
    {[ x | ∃ c : C1, x ∈ {[ x0 | ∃ c0 : C2, x0 ∈ P c c0 ]} ]} =
    {[x | ∃ c1 c2, x ∈ P c1 c2]}.
Proof.
  intros.
  unfold propset_fa_union.
  apply set_eq; intros; split.
  - intros. destruct H, H.
    by exists x0, x1.
  - intros.
    destruct H, H.
    apply elem_of_PropSet.
    by exists x0, x1.
Qed.

Section Semantics.
  Context {Σ : Signature}.

  Record Model := {
    carrier :> sort -> Set;
    app (σ : symbol) :
       @hlist _ carrier (arg_sorts σ) -> propset (carrier (ret_sort σ));
    inhabited (s : sort) : Inhabited (carrier s) ;
    sort_inj (s1 s2 : sort) (P : subsort s1 s2) :
     carrier s1 -> carrier s2;
    sort_parse (s : sort) : string -> option (carrier s)
  }.

  Section with_model.

    Context {M : Model}.
    Record Valuation : Type := {
      evar_valuation {s : sort} (x : evar s) : carrier M s;
      svar_valuation {s : sort} (X : svar s) : propset (carrier M s) ;
    }.

    Definition app_ext
      (σ : symbol)
      (args : @hlist _ (fun s => propset (carrier M s)) (arg_sorts σ))
      : propset (carrier M (ret_sort σ)) :=
    PropSet (
      fun e => exists (l : @hlist _ (carrier M) (arg_sorts σ)),
        pointwise_elem_of _ l args /\ e ∈ app M σ l
    ).


    Definition update_evar_val {s} (ev : evar s) (x : carrier M s) (val : Valuation) : Valuation.
    Proof.
      unshelve esplit.
      intros s' ev'.
      destruct (decide (s = s')).
      destruct (decide (eq_rect s evar ev _ e = ev')).
      exact (eq_rect s M x _ e).
      1,2:exact (evar_valuation val ev').
      exact (@svar_valuation val).
    Defined.

    Definition update_svar_val {s} (sv : svar s) (X : propset (carrier M s)) (val : Valuation) : Valuation.
    Proof.
      unshelve esplit.
      exact (@evar_valuation val).
      intros s' sv'.
      destruct (decide (s = s')).
      * destruct (decide (eq_rect s svar sv _ e = sv')).
        - rewrite e in X. exact X.
        - exact (svar_valuation val sv').
      * exact (svar_valuation val sv').
    Defined.

    Lemma update_evar_val_same :
      forall s (ρ : Valuation) (ev : evar s) c,
        evar_valuation (update_evar_val ev c ρ) ev = c.
    Proof.
      intros. unfold update_evar_val. simpl.
      rewrite decide_eq_same. simpl.
      by rewrite decide_eq_same.
    Qed.

    Lemma update_evar_val_same_sort_neq :
      forall s (ρ : Valuation) (ev1 ev2 : evar s) c,
        ev1 <> ev2 ->
        evar_valuation (update_evar_val ev1 c ρ) ev2 = evar_valuation ρ ev2.
    Proof.
      intros. simpl.
      rewrite decide_eq_same. simpl.
      case_match. congruence.
      reflexivity.
    Qed.

    Lemma update_evar_val_diff_sort :
      forall s1 s2 (ρ : Valuation) (ev1 : evar s1) (ev2 : evar s2) c,
        s1 <> s2 ->
        evar_valuation (update_evar_val ev1 c ρ) ev2 = evar_valuation ρ ev2.
    Proof.
      intros. simpl.
      case_match. congruence.
      reflexivity.
    Qed.

    Lemma update_svar_val_same :
      forall s (ρ : Valuation) (sv : svar s) C,
        svar_valuation (update_svar_val sv C ρ) sv = C.
    Proof.
      intros. unfold update_evar_val. simpl.
      rewrite decide_eq_same. simpl.
      by rewrite decide_eq_same.
    Qed.

    Lemma update_svar_val_same_sort_neq :
      forall s (ρ : Valuation) (sv1 sv2 : svar s) C,
        sv1 <> sv2 ->
        svar_valuation (update_svar_val sv1 C ρ) sv2 = svar_valuation ρ sv2.
    Proof.
      intros. simpl.
      rewrite decide_eq_same. simpl.
      case_match. congruence.
      reflexivity.
    Qed.

    Lemma update_svar_val_diff_sort :
      forall s1 s2 (ρ : Valuation) (sv1 : svar s1) (sv2 : svar s2) C,
        s1 <> s2 ->
        svar_valuation (update_svar_val sv1 C ρ) sv2 = svar_valuation ρ sv2.
    Proof.
      intros. simpl.
      case_match. congruence.
      reflexivity.
    Qed.



    Let OS s := PropsetOrderedSet (carrier M s).
    Let  L s := PowersetLattice (carrier M s).

    Equations? eval {ex mu} {s} (ρ : Valuation)
                    (φ : Pattern ex mu s)
                    : propset (carrier M s)
                      by wf (pat_size φ) :=
      eval ρ (kore_bevar _) := empty ;
      eval ρ (kore_fevar x) := {[evar_valuation ρ x]} ;
      eval ρ (kore_bsvar _) := empty ;
      eval ρ (kore_fsvar X) := svar_valuation ρ X ;

      eval ρ (kore_app σ l) := app_ext σ _ 
      (* Map alternative, if wf ∘ pat_size would not be a requirement in the def.: *)
      (* (hmap (fun j (p : Pattern ex mu j) => eval ρ p) l) *) ;

      eval ρ kore_bot         := empty ;
      eval ρ kore_top         := ⊤ ;
      eval ρ (kore_not φ)     := ⊤ ∖ (eval ρ φ) ;
      eval ρ (kore_and φ1 φ2) := (eval ρ φ1) ∩ (eval ρ φ2) ;
      eval ρ (kore_or φ1 φ2)  := (eval ρ φ1) ∪ (eval ρ φ2) ;
      eval ρ (kore_imp φ1 φ2) := (⊤ ∖ (eval ρ φ1)) ∪ (eval ρ φ2) ;
      eval ρ (kore_iff φ1 φ2) := (⊤ ∖ eval ρ φ1 ∪ eval ρ φ2) ∩
                                 (⊤ ∖ eval ρ φ2 ∪ eval ρ φ1) ;

      eval ρ (kore_exists s' φ) :=
      (* Monadic alternative: 
         ⊤ ≫= λ X, let o := fresh_evar s' φ in
            eval (update_evar_val o X ρ) (bevar_subst [] φ (kore_fevar o)) *)
        let x := fresh_evar s' φ in
          propset_fa_union (λ c,
             eval (update_evar_val x c ρ)
                  (bevar_subst [] (kore_fevar x) φ)) ;
      eval ρ (kore_forall s' φ) :=
        let x := fresh_evar s' φ in
          propset_fa_intersection (λ c,
             eval (update_evar_val x c ρ)
                  (bevar_subst [] (kore_fevar x) φ)) ;

      eval ρ (kore_mu φ)     :=
        let X := fresh_svar s φ in
          @LeastFixpointOf _ (OS s) (L s) (fun S =>
            eval (update_svar_val X S ρ)
                 (bsvar_subst [] (kore_fsvar X) φ)
          )
       ;
      eval ρ (kore_nu φ)     :=
        let X := fresh_svar s φ in
          @GreatestFixpointOf _ (OS s) (L s) (fun S =>
            eval (update_svar_val X S ρ)
                 (bsvar_subst [] (kore_fsvar X) φ)
          );

      eval ρ (kore_ceil φ)       := PropSet (λ _, ∃ c, c ∈ eval ρ φ) ;
      eval ρ (kore_floor φ)      := PropSet (λ _, ∀ c, c ∈ eval ρ φ) ;
      eval ρ (kore_equals φ1 φ2) := PropSet (λ _, (eval ρ φ1) = (eval ρ φ2)) ;
      eval ρ (kore_in φ1 φ2)     := PropSet (λ _, (eval ρ φ1) ⊆ (eval ρ φ2)) ;
      eval ρ (kore_inj s2 pf φ)  := sort_inj M _ _ pf <$> eval ρ φ ;
      eval ρ (kore_dv s str)     := if sort_parse M s str is Some x then {[x]} else ∅
    .
    Proof.
      1: { (* def. of eval ρ (σ ⋅ l) *)
        simpl in *.
        induction l.
        * exact hnil.
        * apply hcons.
          - apply (eval _ _ _ ρ f). lia.
          - apply IHl. intros.
            apply (eval x0 x1 x2 x3 x4). lia.
      }
      (* wf ∘ pat_size constraints *)
      all: try by simpl; lia.
      1-2: rewrite (bevar_subst_size [] ex mu s s' φ x); constructor.
      1-2: rewrite (bsvar_subst_size ex [] mu s s φ X); constructor.
    Defined.



    Definition eval_bevar_simpl := eval_equation_1.
    Definition eval_bsvar_simpl := eval_equation_2.
    Definition eval_fevar_simpl := eval_equation_3.
    Definition eval_fsvar_simpl := eval_equation_4.
    Definition eval_bot_simpl := eval_equation_6.
    Definition eval_top_simpl := eval_equation_7.
    Definition eval_not_simpl := eval_equation_8.
    Definition eval_and_simpl := eval_equation_9.
    Definition eval_or_simpl := eval_equation_10.
    Definition eval_imp_simpl := eval_equation_11.
    Definition eval_iff_simpl := eval_equation_12.
    Definition eval_exists_simpl := eval_equation_13.
    Definition eval_forall_simpl := eval_equation_14.
    Definition eval_mu_simpl := eval_equation_15.
    Definition eval_nu_simpl := eval_equation_16.
    Definition eval_ceil_simpl := eval_equation_17.
    Definition eval_floor_simpl := eval_equation_18.
    Definition eval_equals_simpl := eval_equation_19.
    Definition eval_in_simpl := eval_equation_20.
    Definition eval_inj_simpl := eval_equation_21.
    Definition eval_dv_simpl := eval_equation_22.
    Definition eval_simpl :=
      (eval_bevar_simpl,
       eval_bsvar_simpl,
       eval_fevar_simpl,
       eval_fsvar_simpl,
       eval_bot_simpl,
       eval_top_simpl,
       eval_not_simpl,
       eval_and_simpl,
       eval_or_simpl,
       eval_imp_simpl,
       eval_iff_simpl,
       eval_exists_simpl,
       eval_forall_simpl,
       eval_mu_simpl,
       eval_nu_simpl,
       eval_ceil_simpl,
       eval_floor_simpl,
       eval_equals_simpl,
       eval_in_simpl,
       eval_inj_simpl,
       eval_dv_simpl).

    (* simpler evaluation rule for σ ⋅ l *)
    Lemma eval_app_simpl :
      forall {ex mu} (σ : symbol) (l : hlist (Pattern ex mu) (arg_sorts σ)) (ρ : Valuation),
        eval ρ (kore_app σ l) = app_ext σ (hmap (fun _ => eval ρ) l).
    Proof.
      intros.
      simp eval. f_equal.
      simpl in *. unfold eval_obligation_1. simpl. cbn.
      induction l.
      * reflexivity.
      * rewrite IHl. reflexivity.
    Defined.

    Lemma app_ext_singleton
      {σ}
      {args : hlist (propset ∘ M) (arg_sorts σ)}
      (H : all_singleton args) :
        app_ext σ args = app M σ (all_singleton_extract H).
    Proof.
      apply set_eq. split; intros.
      unfold app_ext in H0.
      destruct H0 as [? []].
      replace (all_singleton_extract H) with x0. auto.
      clear x H1. induction args.
      simpl in *.
      apply destruct_hnil.
      simpl in H. destruct H. destruct s.
      simpl in c. simpl.
      epose proof destruct_hcons x0 as [[] ?]. rewrite y in H0.
      simpl in H0. destruct H0. rewrite c in H. inversion H.
      rewrite y. f_equal. apply IHargs. apply H0.
      apply elem_of_PropSet. exists (all_singleton_extract H).
      split. 2: auto. clear. induction args. simpl. split.
      simpl in H. destruct H. destruct s. simpl in c. subst.
      simpl. split. congruence.
      apply IHargs.
    Defined.

    Lemma all_singleton_var_list {l} (vars : hlist evar l) ρ:
      all_singleton (hmap (fun s (x : evar s) => {[evar_valuation ρ x]}) vars).
    Proof.
      induction vars; simpl.
      * exact tt.
      * apply pair. 2: exact IHvars.
        eapply existT. reflexivity.
    Defined.

    Corollary eval_app_var_list :
      forall ex mu (σ : symbol) (vars : hlist evar (arg_sorts σ)) (ρ : Valuation),
        eval ρ (kore_app σ (var_list ex mu vars)) =
          app M σ (all_singleton_extract (all_singleton_var_list vars ρ)).
    Proof.
      intros. rewrite eval_app_simpl.
      rewrite <- app_ext_singleton.
      (* there is a slight difference in the arguments *)
      f_equal.
      induction vars; simpl.
      * reflexivity.
      * rewrite IHvars. reflexivity.
    Defined.

(*   Lemma app_ext_singleton_empty
    {σ}
    (n : nat)
    (args1 : hlist (propset ∘ M) (take n (arg_sorts σ)))
    (args2 : hlist (propset ∘ M) (drop (n + 1) (arg_sorts σ))) :
      app_ext σ (hlist_app args1 (hcons ∅ args2)) = ∅. *)
Definition contains_empty
  {σ}
  (args : hlist (propset ∘ M) (arg_sorts σ)) : Prop.
Proof.
  induction args.
  - exact False.
  - exact (f = ∅ \/ IHargs).
Defined.

Lemma app_ext_singleton_empty
    {σ}
    (args : hlist (propset ∘ M) (arg_sorts σ))
    (H : contains_empty args) :
      app_ext σ args = ∅.
Proof.
  clear -H.
  apply set_eq. split; intros. 2: set_solver.
  unfold app_ext in H0. destruct H0 as [? []].
  exfalso. clear dependent x.
  unfold contains_empty in H.
  induction args; simpl in H.
  - exact H.
  - pose proof destruct_hcons x0 as [[] ->].
    simpl in H0. destruct H0. destruct H.
    * set_solver.
    * by eapply IHargs.
Defined.

End with_model.

  (** Satisfaction *)
  Definition satM {ex mu s} (φ : Pattern ex mu s) (M : Model) :=
    forall ρ, @eval M _ _ _ ρ φ = ⊤.
  Definition satT (Γ : Theory) (M : Model) :=
    forall p, p ∈ Γ -> @satM _ _ (projT1 p) (projT2 p) M.

  (** Model construction based on curried application *)
  Program Definition mkModel
    (custom_carrier : sort → Set)
    (custom_app : forall (σ : symbol),
      foldr (λ c a, custom_carrier c -> a)
            (propset (custom_carrier (ret_sort σ)))
            (arg_sorts σ))
    (custom_inh : ∀ s : sort, Inhabited (custom_carrier s))
    (custom_sort_inj : ∀ s1 s2, subsort s1 s2 -> custom_carrier s1 -> custom_carrier s2)
    (custom_parser : ∀ s, string -> option (custom_carrier s)) :
    Model :=
  {|
    carrier := custom_carrier;
    inhabited := custom_inh;
    app := fun σ => uncurry_n (custom_app σ);
    sort_inj := custom_sort_inj;
    sort_parse := custom_parser;
  |}.

  (** Model construction based on curried application of singleton-result
      functions *)
  Definition mkModel_singleton
    (custom_carrier : sort → Set)
    (custom_app : forall (σ : symbol), foldr (λ c a, custom_carrier c -> a) (custom_carrier (ret_sort σ)) (arg_sorts σ))
    (custom_inh : ∀ s : sort, Inhabited (custom_carrier s))
    (custom_sort_inj : ∀ s1 s2, subsort s1 s2 -> custom_carrier s1 -> custom_carrier s2)
    (custom_parser : ∀ s, string -> option (custom_carrier s)) :
    Model :=
  {|
    carrier := custom_carrier;
    inhabited := custom_inh;
    app := fun σ => singleton ∘ uncurry_n (custom_app σ);
    sort_inj := custom_sort_inj;
    sort_parse := custom_parser;
  |}.

  Program Definition mkModel_partial
    (custom_carrier : sort → Set)
    (custom_app : forall (σ : symbol), foldr (λ c a, custom_carrier c -> a) (option (custom_carrier (ret_sort σ))) (arg_sorts σ))
    (custom_inh : ∀ s : sort, Inhabited (custom_carrier s))
    (custom_sort_inj : ∀ s1 s2, subsort s1 s2 -> custom_carrier s1 -> custom_carrier s2)
    (custom_parser : ∀ s, string -> option (custom_carrier s)) :
    Model :=
  {|
    carrier := custom_carrier;
    inhabited := custom_inh;
    app := fun σ => oapp singleton empty ∘ (uncurry_n (custom_app σ));
    sort_inj := custom_sort_inj;
    sort_parse := custom_parser;
  |}.

  (** If a symbol is modeled by a function, it is consistent: *)
  Lemma functional_symbol_is_functional :
    forall (σ : symbol) (R : sort) (vars : hlist evar (arg_sorts σ)),
      forall (M : Model),
        (exists (f : hlist M (arg_sorts σ) -> M (ret_sort σ)), app M σ = singleton ∘ f) ->
        satM (functional_symbol σ R vars) M.
  Proof.
    intros.
    unfold satM, functional_symbol. intros.
    simp eval. simpl.
    apply propset_fa_union_full. intro.
    cbn.
    setoid_rewrite eval_equation_19.
    remember (fresh_evar _ _) as x.
    assert (X : 
      ((fix F
                    (l : list sort)
                    (h : hlist (Pattern [ret_sort σ] []) l) {struct
                     h} : hlist (Pattern [] []) l :=
                    match
                      h in (hlist _ l0)
                      return (hlist (Pattern [] []) l0)
                    with
                    | ⟨ ⟩%hlist => ⟨ ⟩%hlist
                    | @hcons _ _ x0 xs y h0 =>
                        hcons (bevar_subst [] (kore_fevar x) y)
                          (F xs h0)
                    end) (arg_sorts σ)
                   (var_list [ret_sort σ] [] vars)) =
                     var_list [] [] vars
    ). {
      clear ρ t H M Heqx.
      induction vars; simpl.
      * reflexivity.
      * rewrite IHvars. reflexivity.
    }
    rewrite X.
    clear X.
    setoid_rewrite elem_of_PropSet.
    setoid_rewrite eval_app_var_list.
    simp eval.
    destruct H as [f H].
    rewrite H. cbn.
    setoid_rewrite eval_equation_3.
    unfold evar_valuation, update_evar_val at 2.
    rewrite decide_eq_same. simpl.
    rewrite decide_eq_same.
    (* c still appears on the lhs *)
    assert (x ∉ free_evars (ret_sort σ) (kore_app σ (var_list [ret_sort σ] [] vars))). {
      pose proof (fresh_evar_is_fresh (ret_sort σ) (kore_equals R (kore_app σ (var_list [ret_sort σ] [] vars))
       (kore_bevar In_nil))).
       subst x.
       simpl in *. set_solver.
    }
    clear -H0.
    cbn in H0.
    exists (f
      (all_singleton_extract
         (all_singleton_var_list vars ρ))).
    f_equal. f_equal.
    remember (f _) as c. clear f Heqc.
    revert ρ c.
    induction vars; intros; simpl in *.
    * reflexivity.
    * destruct decide; subst; simpl in *.
      - destruct decide.
        + subst. clear-H0. exfalso.
          set_solver.
        + f_equal.
          specialize (IHvars ltac:(set_solver)).
          by rewrite IHvars.
      - f_equal.
        specialize (IHvars ltac:(set_solver)).
        by rewrite IHvars.
  Qed.

  Lemma functional_symbol_is_functional_sym :
    forall (σ : symbol) (R : sort) (vars : hlist evar (arg_sorts σ)),
      forall (M : Model),
        (exists (f : hlist M (arg_sorts σ) -> M (ret_sort σ)), app M σ = singleton ∘ f) ->
        satM (functional_symbol_sym σ R vars) M.
  Proof.
    intros.
    unfold satM, functional_symbol_sym. intros.
    simp eval. simpl.
    apply propset_fa_union_full. intro.
    cbn.
    setoid_rewrite eval_equation_19.
    remember (fresh_evar _ _) as x.
    assert (X : 
      ((fix F
                    (l : list sort)
                    (h : hlist (Pattern [ret_sort σ] []) l) {struct
                     h} : hlist (Pattern [] []) l :=
                    match
                      h in (hlist _ l0)
                      return (hlist (Pattern [] []) l0)
                    with
                    | ⟨ ⟩%hlist => ⟨ ⟩%hlist
                    | @hcons _ _ x0 xs y h0 =>
                        hcons (bevar_subst [] (kore_fevar x) y)
                          (F xs h0)
                    end) (arg_sorts σ)
                   (var_list [ret_sort σ] [] vars)) =
                     var_list [] [] vars
    ). {
      clear ρ t H M Heqx.
      induction vars; simpl.
      * reflexivity.
      * rewrite IHvars. reflexivity.
    }
    rewrite X.
    clear X.
    setoid_rewrite elem_of_PropSet.
    setoid_rewrite eval_app_var_list.
    simp eval.
    destruct H as [f H].
    rewrite H. cbn.
    setoid_rewrite eval_equation_3.
    unfold evar_valuation, update_evar_val at 2.
    simpl.
    rewrite decide_eq_same. simpl.
    rewrite decide_eq_same.
    (* c still appears on the lhs *)
    assert (x ∉ free_evars (ret_sort σ) (kore_app σ (var_list [ret_sort σ] [] vars))). {
      pose proof (fresh_evar_is_fresh (ret_sort σ) (kore_equals R (kore_bevar In_nil) (kore_app σ (var_list [ret_sort σ] [] vars))
       )).
       subst x.
       simpl in *. set_solver.
    }
    clear -H0.
    cbn in H0.
    exists (f
      (all_singleton_extract
         (all_singleton_var_list vars ρ))).
    f_equal. f_equal.
    remember (f _) as c. clear f Heqc.
    revert ρ c.
    induction vars; intros; simpl in *.
    * reflexivity.
    * destruct decide; subst; simpl in *.
      - destruct decide.
        + subst. clear-H0. exfalso.
          set_solver.
        + f_equal.
          specialize (IHvars ltac:(set_solver)).
          by erewrite IHvars.
      - f_equal.
        specialize (IHvars ltac:(set_solver)).
        by erewrite IHvars.
  Qed.

  Lemma functional_symbol_is_functional_option :
    forall (σ : symbol) (R : sort) (vars : hlist evar (arg_sorts σ)),
      forall (M : Model),
        (exists (f : hlist M (arg_sorts σ) -> option (M (ret_sort σ))),
(*                 foldr (fun s acc => M s -> acc) (option (M (ret_sort σ))) (arg_sorts σ)), *)
          app M σ = oapp singleton empty ∘ f /\
          forall l, f l <> None) ->
        satM (functional_symbol σ R vars) M.
  Proof.
    intros * [f [H1 H2]].
    apply functional_symbol_is_functional.
    rewrite H1.
    clear -H2.
    epose (
      _ : hlist M (arg_sorts σ) → M (ret_sort σ)
    ) as newf. Unshelve. 2: {
      clear -f. intro l. destruct (f l) eqn:P.
      * exact c.
      * apply inhabited. (* Trick: non-empty carrier is exploited here *)
    } simpl in newf.
    exists newf.
    extensionality l. simpl.
    destruct (f l) eqn:P.
    * simpl. subst newf. simpl. rewrite P. reflexivity.
    * by apply H2 in P.
  Qed.

  Lemma functional_symbol_is_functional_option_sym :
    forall (σ : symbol) (R : sort) (vars : hlist evar (arg_sorts σ)),
      forall (M : Model),
        (exists (f : hlist M (arg_sorts σ) -> option (M (ret_sort σ))),
(*                 foldr (fun s acc => M s -> acc) (option (M (ret_sort σ))) (arg_sorts σ)), *)
          app M σ = oapp singleton empty ∘ f /\
          forall l, f l <> None) ->
        satM (functional_symbol_sym σ R vars) M.
  Proof.
    intros * [f [H1 H2]].
    apply functional_symbol_is_functional_sym.
    rewrite H1.
    clear -H2.
    epose (
      _ : hlist M (arg_sorts σ) → M (ret_sort σ)
    ) as newf. Unshelve. 2: {
      clear -f. intro l. destruct (f l) eqn:P.
      * exact c.
      * apply inhabited. (* Trick: non-empty carrier is exploited here *)
    } simpl in newf.
    exists newf.
    extensionality l. simpl.
    destruct (f l) eqn:P.
    * simpl. subst newf. simpl. rewrite P. reflexivity.
    * by apply H2 in P.
  Qed.

End Semantics.

    Lemma eval_propset_fa_union {Σ : Signature} {M : Model} ex mu s s' (x : evar s) (φ : Pattern ex mu s') ρ Q:
        (forall (c : M s), eval (update_evar_val x c ρ) φ = Q c) ->
        propset_fa_union (fun c => @eval _ _ ex _ _ (update_evar_val x c ρ) φ) =
        propset_fa_union (fun c => Q c).
    Proof.
      intros.
      apply set_eq; intros; split.
      set_solver.
      set_solver.
    Qed.


(** A tactic for deconstructing a concrete set. *)
Ltac unfold_elem_of :=
match goal with
| [H : _ ∈ _ |- _]  => destruct H
end.

(** Case separation based on the value of variables. *)
(* Ltac destruct_evar_val :=
match goal with
| [ |- context [evar_valuation ?ρ ?x] ] =>
  let H := fresh "Val" in
    destruct (evar_valuation ρ x) eqn:H
end. *)

Ltac destruct_evar_val :=
match goal with
| [ |- context [evar_valuation ?ρ ?x] ] =>
  let H := fresh "Val" in
    destruct (evar_valuation ρ x) eqn:H;
    try rewrite H in *
end.

Ltac destruct_evar_val_hyp :=
match goal with
| [H : context [evar_valuation ?ρ ?x] |- _] =>
  let H := fresh "Val" in
    destruct (evar_valuation ρ x) eqn:H;
    try rewrite H in *;
    clear H
end.

(** This tactic is used to construct a proof for `all_singleton`. *)
Ltac solve_dep_prods :=
  match goal with
  | [ |- ()] => exact tt
  | [ |- prod (sigT _) _] =>
    apply pair; [
      eapply existT; reflexivity
    |
      solve_dep_prods
    ]
  end.

Ltac solve_all_singleton :=
match goal with
| [ |- all_singleton _] => cbn; solve_dep_prods
end.

(* NOTE: This would be much more simple, if rewrite_stat innermost worked... *)
(** This tactic rewrites `app_ext` (extension of application), if all
    the arguments are singletons. The tactic rewrites the leftmost-innermost
    occurrence of such `app_ext`. *)
Ltac rewrite_app_ext_innnermost G :=
multimatch G with
(* | context [@app_ext _ ?M ?σ ?args] =>
  rewrite_app_ext_innnermost args (* This step is just to reach
                                      the innermost app_ext *)
  (* idtac "match" σ args *) *)
| context [@app_ext _ ?M ?σ ?args] => (* This branch fails, if there is no
                                   more app_exts, therefore
                                   it succeeds for the last (innermost)
                                   app_ext *)
  (* idtac "last1" σ args; *)
  (* let H := fresh "H" in
  (* we explicitly rewrite: *)
  unshelve (epose proof (@app_ext_singleton _ ImpModel σ args ltac:(solve_all_singleton)) as H);
  (* idtac "last2" σ args; *)
  rewrite H; (* erewrite does not work here, for some reason *)
  clear H *)
  rewrite (@app_ext_singleton _ M σ args ltac:(solve_all_singleton))
end.

Ltac rewrite_app_ext :=
match goal with
| |- ?G => rewrite_app_ext_innnermost G; simpl app
end.

(* Ltac rewrite_app_ext_innnermost_in H G :=
match G with
| context [@app_ext _ ?M ?σ ?args] =>
  rewrite_app_ext_innnermost_in H args
| context [@app_ext _ ?M ?σ ?args] => 
  rewrite (@app_ext_singleton _ M σ args ltac:(solve_all_singleton)) in H
end.

Ltac rewrite_app_ext_in H :=
match type of H with
| ?T => rewrite_app_ext_innnermost_in H T; simpl Semantics.app in H
end.
Ltac rewrite_app_ext_in_single :=
match goal with
| [H : context [app_ext _ _] |- _] => rewrite_app_ext_in H
end. *)
Ltac rewrite_app_ext_in H0 :=
multimatch type of H0 with
| context [@app_ext _ ?M ?σ ?args] => 
  try rewrite (@app_ext_singleton _ M σ args ltac:(solve_all_singleton)) in H0
end.
Ltac rewrite_app_ext_in_single :=
lazymatch goal with
| [H : context [@app_ext _ ?M ?σ ?args] |- _] =>
  rewrite_app_ext_in H
end.

Tactic Notation "deconstruct_elem_of_Theory" :=
  repeat match goal with
  | [ H : _ ∈ _ |- _ ] => inversion H; subst; clear H
  end; clear; simpl.

(* Tactic Notation "eval_helper" :=
  repeat
    match goal with
    | [ |- context [eval ?ρ (@kore_app ?Σ ?ex ?mu ?σ ?l) ] ] =>
       let H := fresh "H" in
       pose proof (eval_app_simpl σ l ρ) as H;
       rewrite H;
       clear H;
       cbn
    | _ => simp eval
    end.

Tactic Notation "eval_helper2" :=
  repeat
    match goal with
    | [ |- context [eval ?ρ (@kore_app ?Σ ?ex ?mu ?σ ?l) ] ] =>
       let H := fresh "H" in
       pose proof (eval_app_simpl σ l ρ) as H;
       rewrite H;
       clear H;
       simpl hmap
    | _ => rewrite eval_simpl
    end. *)

Tactic Notation "rewrite_singleton_all" :=
  unshelve (rewrite_strat bottomup app_ext_singleton); [repeat esplit.. |].

(** This tactic proves the consistency of a functional axiom (based on the
    `functional_symbol_is_functional` property). For this, it automatically
    constructs a parameter list containing variables. *)
Ltac solve_functional_axiom :=
match goal with
| [ |- @eval _ ?M _ _ _ ?ρ (kore_exists _
                (kore_equals ?s (kore_app ?σ ?l)
                             (kore_bevar In_nil))) = ⊤]
                             (* ^- NOTE: this is a restriction on db index 0!!! This pattern checks whether the axiom is a functional axiom *) =>
  let H := fresh "H" in
  epose proof (functional_symbol_is_functional σ s (hmap (fun s p =>
    match p with
    | kore_fevar x => x
    | _ => "_"%string
    end) l) M);
  apply H;
  eexists;
  reflexivity
end.

Ltac solve_functional_axiom_option :=
match goal with
| [ |- @eval _ ?M _ _ _ ?ρ (kore_exists _
                (kore_equals ?s (kore_app ?σ ?l)
                             (kore_bevar In_nil))) = ⊤]
                             (* ^- NOTE: this is a restriction on db index 0!!! This pattern checks whether the axiom is a functional axiom *) =>
  let H := fresh "H" in
  epose proof (H := functional_symbol_is_functional_option σ s (hmap (fun s p =>
    match p with
    | kore_fevar x => x
    | _ => "_"%string
    end) l) M);
  apply H;
  eexists; split; [reflexivity|]
end.

Ltac solve_functional_axiom_option_sym :=
match goal with
| [ |- @eval _ ?M _ _ _ ?ρ (kore_exists _
                (kore_equals ?s (kore_bevar In_nil) (kore_app ?σ ?l))) = ⊤]
                             (* ^- NOTE: this is a restriction on db index 0!!! This pattern checks whether the axiom is a functional axiom *) =>
  let H := fresh "H" in
  epose proof (H := functional_symbol_is_functional_option_sym σ s (hmap (fun s p =>
    match p with
    | kore_fevar x => x
    | _ => "_"%string
    end) l) M);
      apply H;
  eexists; split; [reflexivity|]
end.



Ltac solve_ineqs_smart :=
  lazymatch goal with
  | |- context [decide (?X = ?X)] =>
    rewrite decide_eq_same
  | |- context [decide ((@fresh ?A ?C ?I ?X) = (@fresh ?A ?C ?I ?Y))] =>
       let P := fresh "P" in
       let e := fresh "e" in
       destruct (decide ((@fresh A C I X) = (@fresh A C I Y))) as [e | e] eqn:P;
         [
          try rewrite P;
          exfalso;
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          pose proof (infinite_is_fresh X) as H1;
          pose proof (infinite_is_fresh Y) as H2;
          rewrite -> e in *;
          clear -H1 H2;
          rewrite elem_of_elements in H1;
          rewrite elem_of_elements in H2;
          set_solver|
          try rewrite P;
          try rewrite e; clear P e]
  | |- context [decide ((@fresh ?A ?C ?I ?X) = ?Y)] =>
    let P := fresh "P" in
    let e := fresh "e" in
    destruct (decide ((@fresh A C I X) = Y)) as [e | e] eqn:P;
         [
          try rewrite P;
          exfalso;
          let H1 := fresh "H" in
          pose proof (infinite_is_fresh X) as H1;
          rewrite -> e in *;
          clear -H1;
          rewrite elem_of_elements in H1;
          set_solver|
          try rewrite P;
          try rewrite e; clear P e]
  | |- context [decide (?X = (@fresh ?A ?C ?I ?Y))] =>
    let P := fresh "P" in
    let e := fresh "e" in
    destruct (decide (X = (@fresh A C I Y))) as [e | e] eqn:P;
         [
          try rewrite P;
          exfalso;
          let H1 := fresh "H" in
          pose proof (infinite_is_fresh Y) as H1;
          rewrite -> e in *;
          clear -H1;
          rewrite elem_of_elements in H1;
          set_solver|
          try rewrite P;
          try rewrite e; clear P e]
  end.





(** This tactic automatically simplifies the semantics of patterns with the
    usual simplification tactic of `Equations`. However, in case of application
    it uses a derived theorem. *)
Ltac simplify_fresh :=
match goal with
| |- context [@fresh_evar ?Σ ?pat_s ?ex ?mu ?s ?φ] =>
  let H := fresh "Hass" in
  eassert (Hass :
    @fresh_evar Σ pat_s ex mu s φ = _
  ); [
    clear;
    unfold fresh_evar;
    cbn;
    repeat rewrite decide_eq_same;
    repeat (destruct decide; [congruence|]);
    cbn;
    repeat rewrite union_empty_l_L;
    repeat rewrite union_empty_r_L;
    reflexivity
  |
    rewrite Hass;
    clear Hass
  ]
end.
Ltac eval_simplifier :=
  lazymatch goal with
  | |- context [propset_fa_union (fun c => eval (update_evar_val _ c _) _)] =>
      (* idtac "propset"; *)
      erewrite eval_propset_fa_union;
      [
      |
        intro; cbn;
        repeat eval_simplifier;
        cbn;
        reflexivity
      ] (* recursion, first the second goal should be solved *)

  | [ |- context [eval ?ρ (@kore_app ?Σ ?ex ?mu ?σ ?l) ] ] =>
     let H := fresh "H" in
     pose proof (eval_app_simpl σ l ρ) as H;
     rewrite H;
     clear H;
     simpl hmap
  | [ |- context [eval ?ρ (kore_exists _ _) ]] =>
    (* idtac "ex"; *)
    rewrite eval_simpl;
    simplify_fresh
    (* remember_fresh - can't be done here, due to existential variables *)
  | [ |- context [eval ?ρ (@kore_fevar ?Σ ?ex ?mu ?s ?x) ] ]
     => (* idtac "var"; *)
        rewrite eval_simpl;
        simpl;
        try solve_ineqs_smart
  | _ =>
    (* idtac "other"; *)
    rewrite eval_simpl
  end.

Ltac destruct_oapp_hyp :=
  match goal with
  | [H : context [oapp singleton ∅ ?x] |- _] =>
    let P := fresh "P" in
    destruct x eqn:P; simpl in *
  end.

  Ltac app_ext_empty_smart :=
    match goal with
    | |- context [app_ext _ ?args] =>
      match args with
      | context [∅] =>
    rewrite app_ext_singleton_empty;
      [app_ext_empty_smart + (cbn; set_solver)
      |
      (cbn; set_solver)
      ]
      end
    end.

  Ltac app_ext_empty_hyp :=
    match goal with
    | [H : context [app_ext ?σ ?args] |- _] =>
      match args with
      | context [∅] =>
        rewrite app_ext_singleton_empty in H;
        [
          app_ext_empty_smart
        |
          set_solver
        ]
      end
    end.

Ltac app_ext_empty :=
    rewrite app_ext_singleton_empty;
    [app_ext_empty || idtac (* for some reason, this idtac is needed here *);cbn; set_solver
      |
    ].
Ltac destruct_oapps :=
  repeat (match goal with
  | [H : context [oapp singleton ∅ ?x] |- _] =>
    let P := fresh "P" in
    destruct x eqn:P; simpl in *
  | |- context [oapp singleton ∅ ?x] =>
    let P := fresh "P" in
    destruct x eqn:P; simpl in *
  end;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
  repeat app_ext_empty;
  repeat rewrite_app_ext_in_single).
Ltac rewrite_evar_val :=
  repeat match goal with
    | [H : _ = evar_valuation ?ρ ?x |- _] => rewrite <- H in *; clear H
    | [H : evar_valuation ?ρ ?x = _ |- _] => rewrite -> H in *; clear H
    end.

Add Search Blacklist "_elim".
Add Search Blacklist "FunctionalElimination_".
Add Search Blacklist "_graph_mut".
Add Search Blacklist "_graph_rect".
Add Search Blacklist "eval_equation_".

