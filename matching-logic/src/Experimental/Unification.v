From Coq Require Import ssreflect ssrfun ssrbool.

(* From Ltac2 Require Import Ltac2. *)

Require Import Equations.Prop.Equations.

From Coq Require Import String Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.MLPM Substitution.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem FOEquality_ProofSystem DeductionTheorem.
From MatchingLogic.Utils Require Import stdpp_ext.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Section unification.
  Context {Σ : Signature} {syntax : Syntax}.

  Section helpers.

    Lemma extract_common_from_equality_r a b p Γ :
      theory ⊆ Γ ->
      well_formed a -> well_formed b -> well_formed p ->
      Γ ⊢ is_predicate_pattern p --->
          p ---> a =ml b <---> (a and p) =ml (b and p).
    Proof.
      intros HΓ wfa wfb wfx.
      mlIntro "H".
      mlIntro "H0".
      mlSplitAnd; mlIntro "H1".
      mlRewriteBy "H1" at 1.
      mlReflexivity.
      epose proof (predicate_equiv _ _ _ _).
      mlApplyMeta H in "H".
      mlDestructAnd "H" as "H2" "_".
      mlApply "H2" in "H0".
      epose proof (patt_total_and _ _ _ _ _ _).
      apply pf_iff_proj2 in H0.
      use AnyReasoning in H0.
      mlConj "H1" "H0" as "H".
      mlApplyMeta H0 in "H".
      clear H H0. mlClear "H0". mlClear "H2". mlClear "_". mlClear "H1".
      mlDeduct "H".
      remember (_ : ProofInfo) as i. clear Heqi.
      evar Pattern.
      epose proof (hypothesis (Γ ∪ {[p0]}) p0 _ ltac:(set_solver)). use i in H.
      epose proof (extract_common_from_equivalence_r _ _ _ _ _ _ _ _).
      apply (pf_iff_proj1) in H0.
      apply lhs_from_and in H0.
      apply (MP H) in H0.
      mlAdd H.
      mlRewrite H0 at 1.
      mlReflexivity.
      Unshelve. all: wf_auto2.
    Defined.

    Definition get_fresh_evar (φ : Pattern) : sig (.∉ free_evars φ).
    Proof.
      exists (fresh_evar φ); auto.
    Defined.

  End helpers.

  (** The naming of the following lemmas matches this article:
        Unification in Matching Logic - Extended Version
        Andrei Arusoaie, Dorel Lucanu
        https://arxiv.org/abs/1811.02835v3
   *)

  Lemma Prop₃_left: forall Γ φ φ',
    theory ⊆ Γ ->
    well_formed φ -> well_formed φ' ->
    Γ ⊢ (φ and (φ' =ml φ)) ---> (φ and φ').
  Proof.
    intros Γ φ φ' SubTheory Wf1 Wf2.
    toMLGoal. wf_auto2.
    mlIntro "H0". mlDestructAnd "H0" as "H1" "H2".
    mlRewriteBy "H2" at 1.
    mlSplitAnd; mlExact "H1".
  Defined.

  Lemma Prop₃_right : forall Γ φ φ',
      theory ⊆ Γ ->
      well_formed φ -> well_formed φ' -> mu_free φ' ->
      Γ ⊢ (ex , (φ =ml b0))  ->
      Γ ⊢ (ex , (φ' =ml b0))  ->
      Γ ⊢ (φ and φ') ---> (φ and (φ =ml φ')) .
  Proof.
    intros Γ φ φ' HΓ Wf1 Wf2 MF Func1 Func2.
    toMLGoal. wf_auto2.
    mlIntro "H0".
    mlAssert ("H1" : ⌈ φ and φ' ⌉).
    { wf_auto2. }
    {
      pose proof (phi_impl_defined_phi Γ (φ and φ') (fresh_evar (φ and φ')) HΓ
                    ltac:(solve_fresh) ltac:(wf_auto2)) as H.
      use AnyReasoning in H.
      mlApplyMeta H.
      mlExact "H0".
    }
    replace (⌈ φ and φ' ⌉) with (φ ∈ml φ') by auto.
    mlDestructAnd "H0" as "H2" "H3". mlSplitAnd.
    * mlExact "H2".
    * mlApplyMeta membership_imp_equal_meta; auto.
      mlExact "H1".
  Defined.

  Definition substitute_list (σ : list (evar * Pattern)) (t : Pattern) : Pattern := fold_left (fun φ '(x, φ') => φ^[[evar: x ↦ φ']]) σ t.

  Lemma wf_substitute_list : forall σ t, wf (map snd σ) -> well_formed t -> well_formed (substitute_list σ t).
  Proof.
    intros.
    apply wf_fold_left with (t := snd); try assumption.
    intros ? [] **; wf_auto2.
  Qed.

  Definition predicate_list (σ : list (evar * Pattern)) : Pattern := fold_right (fun '(x, φ') φ => patt_free_evar x =ml φ' and φ) patt_top σ.

  Lemma wf_predicate_list : forall σ, wf (map snd σ) -> well_formed (predicate_list σ).
  Proof.
    intros.
    apply wf_foldr with (t := snd);
    only 3: intros ? [] **; wf_auto2.
  Qed.
  
  Lemma Lemma₁ : forall Γ φ t x, theory ⊆ Γ ->
    well_formed φ ->
    mu_free φ ->
    well_formed t ->
    Γ ⊢ (patt_free_evar x) =ml t ---> φ^[[evar:x↦t]] =ml φ.
  Proof.
    intros * HΓ wfφ mfφ wft.
    pose proof (get_fresh_evar φ) as [y Hy].
    pose proof (equality_elimination_basic Γ (patt_free_evar x) t {| pcEvar := y; pcPattern := φ^[[evar: x ↦ patt_free_evar y]] =ml φ |}).
    ospecialize* H; auto. wf_auto2.
    simpl. now erewrite mu_free_free_evar_subst, mfφ.
    cbn -["=ml"] in H. mlSimpl in H.
    erewrite ! free_evar_subst_chain, free_evar_subst_id, ! (free_evar_subst_no_occurrence y) in H by auto.
    mlIntro "H".
    mlApplyMeta H in "H".
    mlDestructAnd "H" as "H1" "H2".
    mlApply "H1". mlReflexivity.
  Defined.

  Lemma Lemma₂ : forall Γ φ σ (i : ProofInfo),
    theory ⊆ Γ -> mu_free φ -> well_formed φ ->
    forallb mu_free (map snd σ) -> wf (map snd σ) ->
    Γ ⊢i substitute_list σ φ and predicate_list σ <--->
      φ and predicate_list σ using i.
  Proof.
    intros * HΓ mfφ wfφ mfσ wfσ.
    pose proof (wf_predicate_list σ wfσ) as WF1.
    pose proof (wf_substitute_list σ φ wfσ wfφ) as WF2.
    epose proof (extract_common_from_equivalence_r _ _ _ _ _ _ _).
    eapply (pf_iff_proj2 _ _ _ _ _ _) in H.
    mlApplyMeta H.
    clear H.
    fromMLGoal.
    generalize dependent φ.
    induction σ; simpl; intros. mlIntro. mlReflexivity. destruct a.
    mlIntro "H". mlDestructAnd "H" as "H1" "H2".
    unshelve ospecialize* IHσ. exact φ^[[evar:e↦p]]. 1-6, 8: shelve.
    mlApplyMeta IHσ in "H2". clear IHσ.
    mlApplyMeta (pf_iff_equiv_trans_obj) in "H2".
    mlApply "H2". mlClear "H2".
    epose proof (Lemma₁ _ φ _ _ _ _ _ _).
    mlApplyMeta H in "H1". clear H. 2: admit.
    epose proof (get_fresh_evar (φ^[[evar:e↦p]] <---> φ)) as [y Hy].
    epose proof (total_phi_impl_phi _ _ _ _ Hy _).
    mlApplyMeta H in "H1". clear H.
    mlExact "H1". admit.
    Unshelve. all: try solve [auto | wf_auto2].
    simpl in mfσ. apply andb_true_iff in mfσ as [].
    apply mu_free_free_evar_subst; auto.
  Admitted.

  Definition is_unifier_of (σ : list (evar * Pattern)) t₁ t₂ := substitute_list σ t₁ =ml substitute_list σ t₂.

  Lemma wf_is_unifier_of : forall σ t₁ t₂, wf (map snd σ) -> well_formed t₁ -> well_formed t₂ -> well_formed (is_unifier_of σ t₁ t₂).
  Proof.
    intros.
    apply well_formed_equal; apply wf_substitute_list; assumption.
  Qed.

  Lemma predicate_list_predicate Γ σ : theory ⊆ Γ -> wf (map snd σ) -> Γ ⊢ is_predicate_pattern (predicate_list σ).
  Proof with wf_auto2.
    intros HΓ wfσ.
    epose proof (foldr_ind_set (λ φ, well_formed φ -> Γ ⊢ is_predicate_pattern φ) (λ '(x, φ), well_formed (patt_free_evar x =ml φ) -> Γ ⊢ is_predicate_pattern (patt_free_evar x =ml φ)) (λ '(x, φ') (φ : Pattern), patt_free_evar x =ml φ' and φ) patt_top σ).
    ospecialize* X. 1-4: clear X.
    * intro. toMLGoal... mlLeft. mlReflexivity.
    * induction σ; split.
      ** destruct a. intro. unfold "=ml".
         eapply useGenericReasoning.
         apply pile_any.
         mlFreshEvar as x.
         mlFreshEvar as y.
         mlFreshEvar as z.
         eapply (floor_is_predicate _ _ AnyReasoning x y z).
         3: fm_solve.
         3: fm_solve.
         3: fm_solve.
         3: try_solve_pile.
         assumption.
         wf_auto2.
      ** apply IHσ...
    * intros [] ? ? ? ?.
      (* destruct a. *)
      eenough (well_formed _).
      eenough (well_formed _).
      pose proof (predicate_and Γ _ _ HΓ H3 H2).
      apply (MP (H H3)) in H4.
      apply (MP (H0 H2)) in H4.
      exact H4.
      all: wf_auto2.
    * apply (wf_foldr) with (t := snd); only 3: intros ? [] ? ?...
    * exact X.
  Defined.

  Lemma Lemma₅ : forall (σ : list (evar * Pattern)) t₁ t₂ Γ,
    theory ⊆ Γ ->
    well_formed t₁ -> well_formed t₂ ->
    mu_free t₁ -> mu_free t₂ ->
    wf (map snd σ) -> forallb mu_free (map snd σ) ->
    Γ ⊢ is_unifier_of σ t₁ t₂ ---> predicate_list σ ---> (t₁ =ml t₂).
  Proof.
    intros * HΓ wft₁ wft₂ mft₁ mft₂ wfσ mfσ.
    unfold is_unifier_of.
    epose proof (wf_predicate_list σ wfσ) as wfpl.
    epose proof (wf_substitute_list σ t₁ wfσ wft₁) as wfsl1.
    epose proof (wf_substitute_list σ t₂ wfσ wft₂) as wfsl2.
    mlIntro "H".
    mlIntro "H0".
    epose proof (extract_common_from_equality_r _ _ _ _ _ _ _ _).
    epose proof (predicate_list_predicate _ _ _ _).
    apply (MP H0) in H.
    mlApplyMeta H in "H0".
    mlDestructAnd "H0" as "H1" "H2".
    mlApply "H2".
    epose proof (Lemma₂ Γ t₁ σ AnyReasoning _ _ _ _ _).
    mlRewrite <- H1 at 1.
    epose proof (Lemma₂ Γ t₂ σ AnyReasoning _ _ _ _ _).
    mlRewrite <- H2 at 1.
    mlRewriteBy "H" at 1.
    mlReflexivity.
    Unshelve. all: auto.
  Defined.

  Lemma R₅' : forall x Γ, theory ⊆ Γ -> Γ ⊢ (ex , patt_free_evar x =ml b0).
  Proof.
    intros.
    toMLGoal.
    wf_auto2.
    mlExists x.
    mlSimpl.
    rewrite evar_open_not_occur.
    wf_auto2.
    unfold evar_open. simpl.
    mlReflexivity.
  Defined.

  Definition WFPattern := sig well_formed.
  Definition mkWFWrapper (f : Pattern -> Pattern -> Pattern) (wfp : forall a b, well_formed a -> well_formed b -> well_formed (f a b)) : WFPattern -> WFPattern -> WFPattern.
  Proof.
    intros * [a wfa] [b wfb].
    exists (f a b). exact (wfp a b wfa wfb).
  Defined.
  Definition WFPatt_imp := mkWFWrapper patt_imp well_formed_imp.
  Notation "a wf---> b"  := (WFPatt_imp a b) (at level 75, right associativity) : ml_scope.
  Definition WFPatt_and := mkWFWrapper patt_and well_formed_and.
  Notation "a 'wfand' b" := (WFPatt_and   a b) (at level 72, left associativity) : ml_scope.
  Definition WFPatt_iff := mkWFWrapper patt_iff well_formed_iff.
  Notation "a wf<---> b" := (WFPatt_iff a b) (at level 74, no associativity) : ml_scope.
  Definition WFPatt_equal := mkWFWrapper patt_equal well_formed_equal.
  Notation "p wf=ml q" := (WFPatt_equal p q) (at level 67) : ml_scope.
  Definition WFFree_evar_subst (x : evar) := mkWFWrapper (flip free_evar_subst x) (fun a b => well_formed_free_evar_subst x b a).
  Notation "e ^wf[[ 'evar:' x ↦ e' ]]" := (WFFree_evar_subst x e' e) (at level 2, e' at level 200, left associativity, format "e ^wf[[ 'evar:' x ↦ e' ]]" ) : ml_scope.
  Definition WFDerives (Γ : Theory) (p : WFPattern) : Set := derives Γ (proj1_sig p).
  Notation "Γ ⊢wf ϕ" := (WFDerives Γ ϕ) (at level 95, no associativity).
  Definition WFPatt_app := mkWFWrapper patt_app well_formed_app.
  Notation "a wf⋅ b" := (WFPatt_app a b) (at level 66, left associativity) : ml_scope.
  Lemma well_formed_free_evar : forall e, well_formed (patt_free_evar e).
  Proof.
    exact (const eq_refl).
  Defined.

  (**
    This typeclass represents (in an abstract way) the unification problems of

      Unification in Matching Logic - Extended Version
      Andrei Arusoaie, Dorel Lucanu
      https://arxiv.org/abs/1811.02835v3

      In the following description, we highlight the connection to this paper.
  *)
  Class UP (T : Type) := {
    (** Insertion operation:

          insertUP P (t, u) ~ P ∪ {t ≐ u}
      *)
    insertUP : T -> (WFPattern * WFPattern) -> T;
    (** Failed unification problem

          bottomUP ~ ⊥
      *)

    bottomUP : T;
    (** Conversion to predicate. Expected to be conjunction of equalities.

          toPredicateUP P ~ ϕᴾ
      *)

    toPredicateUP : T -> WFPattern;
    (** Substitution of a variable to a pattern in every pattern of
        a unification problem

          substituteAllUP x t P ~ P{x ↦ t}
      *)

    substituteAllUP : evar -> WFPattern -> T -> T;
    (** Creation of a singleton problem

          singletonUP t u ~ {t ≐ u}
      *)

    singletonUP : WFPattern -> WFPattern -> T;

    (**
      Converting a unification problem maps insertion to conjunction.
     *)
    toPredicateInsertUP : forall Γ t x y, Γ ⊢wf toPredicateUP (insertUP t (x, y)) wf<---> ((x wf=ml y) wfand (toPredicateUP t));

    (**
      Converting a unification problem maps substitution of unification problems
      to substitution of patterns.
     *)
    toPredicateSubstituteAllUP : forall Γ t e p, Γ ⊢wf toPredicateUP (substituteAllUP e p t) wf<---> (toPredicateUP t)^wf[[evar:e↦p]];

    (**
      Inserting into a non-⊥ unification problem cannot result ⊥.
     *)
    insertNotBottomUP : forall t x, t ≠ bottomUP -> insertUP t x ≠ bottomUP;

    (**
      Converting a singleton problem to a predicate pattern gives us an equality.
     *)
    toPredicateSingletonUP : forall Γ t1 t2, Γ ⊢wf toPredicateUP (singletonUP t1 t2) wf<---> (t1 wf=ml t2)
  }.

  Lemma lift_derives : forall Γ p, derives Γ (proj1_sig p) -> WFDerives Γ p.
  Proof.
    intros. auto.
  Defined.

  Lemma unwrap_wfwrapper : forall f wff a b, proj1_sig (mkWFWrapper f wff a b) = f (`a) (`b).
  Proof.
    now intros ? ? [a wfa] [b wfb].
  Defined.

  Lemma wfWFPattern : forall (p : WFPattern), well_formed (proj1_sig p).
  Proof.
    intros [p wfp]. exact wfp.
  Defined.

  Tactic Notation "mlDestructBotDocVer" := match goal with [ |- context [mkNH _ ?x patt_bott] ] => mlDestructBot x end.

  Tactic Notation "refine_wf" := repeat first [
      apply well_formed_imp |
      apply well_formed_and |
      apply well_formed_equal |
      apply well_formed_free_evar_subst |
      apply well_formed_top |
      apply well_formed_free_evar
    ].

  Tactic Notation "mlDecomposeAll" := do !
    match goal with
    | [ |- context[(mkMLGoal _ _ _ (patt_imp _ _) _)] ] => mlIntro
    | [ |- context[mkNH _ ?x (patt_and _ _)] ] => mlDestructAnd x
    end.

  Lemma set_fold_disj_union_strong_equiv `{FinSet A C} Γ (f : A → WFPattern → WFPattern) (b : WFPattern) (X Y : C) :
  (∀ x1 x2 b',
  x1 ∈ X ∪ Y → x2 ∈ X ∪ Y → x1 ≠ x2 →
  Γ ⊢wf (f x1 (f x2 b')) wf<---> (f x2 (f x1 b'))) →
  X ## Y →
  Γ ⊢wf (set_fold f b (X ∪ Y)) wf<---> (set_fold f (set_fold f b X) Y).
  Admitted.
  (* Proof. *)
  (*   intros Hf Hdisj. unfold set_fold; simpl. *)
  (*   rewrite <- foldr_app. *)
  (*   epose proof foldr_permutation. *)
  (*   apply (foldr_permutation R f b). *)
  (*   - intros j1 x1 j2 x2 b' Hj Hj1 Hj2. apply Hf. *)
  (*     + apply elem_of_list_lookup_2 in Hj1. set_solver. *)
  (*     + apply elem_of_list_lookup_2 in Hj2. set_solver. *)
  (*     + intros →. pose proof (NoDup_elements (X ∪ Y)). *)
  (*       by eapply Hj, NoDup_lookup. *)
  (*   - by rewrite elements_disj_union, (comm (++)). *)
  (* Qed. *)

  Lemma in_set_implies_in_predicate `{FinSet A C} `{!LeibnizEquiv C} : forall Γ f b x (X : C), x ∈ X -> Γ ⊢wf set_fold (WFPatt_and ∘ f) b X wf---> f x.
  Proof.
    intros.
    opose proof* (set_ind' (fun X' => Γ ⊢wf set_fold (WFPatt_and ∘ f) b ({[x]} ∪ X') wf---> f x) _ _ X).
    rewrite -> union_empty_r_L, set_fold_singleton. simpl.
    unfold WFDerives. toMLGoal. apply wfWFPattern. rewrite ! unwrap_wfwrapper. mlDecomposeAll; mlAssumption.
    intros.
    rewrite union_assoc_L.
    destruct (EqDecision0 x x0) as [-> | ].
    rewrite union_idemp_L. exact H9.
    rewrite -> (union_comm_L {[x]}), <- union_assoc_L, union_comm_L.
    opose proof* (set_fold_disj_union_strong_equiv Γ (WFPatt_and ∘ f) b ({[x]} ∪ X0) {[x0]} _ _).
    intros. simpl.
    unfold WFDerives. toMLGoal. apply wfWFPattern. rewrite ! unwrap_wfwrapper.
    mlSplitAnd; mlDecomposeAll; repeat mlSplitAnd; mlAssumption.
    set_solver.
    rewrite set_fold_singleton in H10. simpl in H10.
    unfold WFDerives in H10, H9 |- *.
    toMLGoal. apply wfWFPattern.
    rewrite ! unwrap_wfwrapper in H10, H9 |- *.
    mlIntro. apply pf_iff_proj1 in H10. mlApplyMeta H10 in "0".
    mlDestructAnd "0". mlApplyMeta H9 in "2". mlAssumption.
    1-2: refine_wf; apply wfWFPattern.
    simpl in H8.
    apply elem_of_subseteq_singleton in H7.
    apply subseteq_union_1_L in H7.
    rewrite H7 in H8. exact H8.
  Defined.

  Lemma WFPattern_eq_dec : EqDecision (WFPattern * WFPattern).
  Proof.
    apply @prod_eq_dec.
    all: apply sig_eq_dec.
    1, 3: intros; apply eq_pi; apply decide_rel; apply bool_eq_dec.
    1, 2: apply Pattern_eqdec.
  Defined.

  #[refine] Instance optionSetUP `{H : ElemOf (WFPattern * WFPattern) T, H0 : Empty T, H1 : Singleton (WFPattern * WFPattern) T, H2 : Union T, H3 : Intersection T, H4 : Difference T, H5 : Elements (WFPattern * WFPattern) T, @FinSet (WFPattern * WFPattern) T H H0 H1 H2 H3 H4 H5 WFPattern_eq_dec, !LeibnizEquiv T} : UP (option T) := {
    insertUP t x := option_map ({[x]} ∪.) t;
    bottomUP := None;
    toPredicateUP := from_option (set_fold (WFPatt_and ∘ (fun '(x, y) => x wf=ml y)) (Top ↾ well_formed_top)) (patt_bott ↾ well_formed_bott);
    substituteAllUP e p := option_map (set_map (fun '(x, y) => (x^wf[[evar:e↦p]], y^wf[[evar:e↦p]])));
    singletonUP t1 t2 := Some {[(t1, t2)]}
  }.
  Proof.
    * intros. destruct_with_eqn t; simpl.
      ** match goal with [ |- context[set_fold (WFPatt_and ∘ ?f') ?b' _] ] => remember f' as f; remember b' as b end.
         epose proof (elem_of_dec_slow (x, y) t0) as [].
         pose proof (in_set_implies_in_predicate Γ f b _ _ e).
         rewrite subseteq_union_1_L. set_solver.
         unfold WFDerives in H7 |- *. toMLGoal. apply wfWFPattern.
         rewrite ! unwrap_wfwrapper in H7 |- *.
         mlSplitAnd; mlDecomposeAll.
         mlSplitAnd. subst f. rewrite unwrap_wfwrapper in H7.
         mlApplyMeta H7. 1-3: mlAssumption.
         rewrite union_comm_L.
         opose proof* (set_fold_disj_union_strong_equiv Γ (WFPatt_and ∘ f) b t0 {[(x, y)]} _ _).
         intros. subst f. simpl. do ! case_match.
         unfold WFDerives. toMLGoal. apply wfWFPattern. rewrite ! unwrap_wfwrapper.
         mlSplitAnd; mlDecomposeAll; repeat mlSplitAnd; mlAssumption.
         set_solver.
         rewrite set_fold_singleton in H7. simpl in H7. subst f.
         exact H7.
      ** unfold WFDerives. case_match. simpl.
         apply (f_equal proj1_sig) in H7. rewrite ! unwrap_wfwrapper in H7. simpl in H7.
         rewrite <- H7. toMLGoal. refine_wf; apply wfWFPattern.
         mlSplitAnd; mlDecomposeAll; mlDestructBotDocVer.
    * intros. destruct_with_eqn t; simpl.
      ** match goal with [ |- context[set_fold (WFPatt_and ∘ ?f') ?b' (set_map ?g' _)] ] => remember f' as f; remember b' as b; remember g' as g end.
         apply (set_fold_ind' (fun r X => Γ ⊢wf set_fold (WFPatt_and ∘ f) b (set_map g X) wf<---> r^wf[[evar:e↦p]]) (WFPatt_and ∘ f) b).
         rewrite -> set_map_empty, set_fold_empty. subst b.
         unfold WFDerives. rewrite ! unwrap_wfwrapper. simpl.
         toMLGoal. wf_auto2. mlSplitAnd; mlDecomposeAll.
         mlAssumption. pose proof (top_holds Γ). use AnyReasoning in H7. mlExactMeta H7.
         intros. simpl. rewrite -> set_map_union_L, set_map_singleton_L.
         unshelve epose proof (elem_of_dec_slow (g x) (set_map g X)) as [].
         1: exact T. 4: exact H6. 1-3: auto.
         rewrite subseteq_union_1_L. apply elem_of_subseteq_singleton. exact e0.
         epose proof (in_set_implies_in_predicate Γ f b _ _ e0).
         unfold WFDerives in H8, H9 |- *. toMLGoal. apply wfWFPattern.
         rewrite ! unwrap_wfwrapper in H8, H9 |- *.
         cbn [flip] in H8 |- *. mlSimpl.
         mlSplitAnd; mlDecomposeAll. mlSplitAnd.
         mlApplyMeta H9 in "0". subst f g. case_match.
         rewrite ! unwrap_wfwrapper. cbn [flip]. mlSimpl.
         mlAssumption.
         apply pf_iff_proj1 in H8. mlApplyMeta H8. mlAssumption.
         1-2: refine_wf; apply wfWFPattern.
         apply pf_iff_proj2 in H8. mlApplyMeta H8. mlAssumption.
         1-2: refine_wf; apply wfWFPattern.
         rewrite union_comm_L.
         unshelve opose proof* (set_fold_disj_union_strong_equiv Γ (WFPatt_and ∘ f) b (set_map g X) {[g x]}).
         5: exact H6. all: auto.
         intros.
         subst f g. simpl. repeat case_match.
         unfold WFDerives. toMLGoal. apply wfWFPattern.
         rewrite ! unwrap_wfwrapper. mlSplitAnd; mlDecomposeAll;
         repeat mlSplitAnd; mlAssumption.
         set_solver.
         unfold WFDerives in H9, H8 |- *.
         rewrite ! unwrap_wfwrapper in H9, H8 |- *.
         cbn [flip] in H8 |- *.
         eapply pf_iff_equiv_trans. 4: exact H9.
         1-3: refine_wf; apply wfWFPattern.
         rewrite set_fold_singleton. cbn [compose].
         mlSimpl. rewrite unwrap_wfwrapper.
         toMLGoal. refine_wf; apply wfWFPattern.
         mlSplitAnd; mlDecomposeAll; mlSplitAnd.
         subst f g. case_match. rewrite ! unwrap_wfwrapper.
         cbn [flip]. mlSimpl. mlAssumption.
         apply pf_iff_proj1 in H8. mlApplyMeta H8. mlAssumption.
         1-2: refine_wf; apply wfWFPattern.
         subst f g. case_match. rewrite ! unwrap_wfwrapper.
         cbn [flip]. mlSimpl. mlAssumption.
         apply pf_iff_proj2 in H8. mlApplyMeta H8. mlAssumption.
         1-2: refine_wf; apply wfWFPattern.
      ** case_match. apply (f_equal proj1_sig) in H7. rewrite unwrap_wfwrapper in H7. simpl in H7. unfold WFDerives. simpl. rewrite H7. now aapply pf_iff_equiv_refl.
    * intros. destruct_with_eqn t. simpl. discriminate. now destruct H7.
    * intros. simpl. rewrite set_fold_singleton. simpl.
      unfold WFDerives. rewrite ! unwrap_wfwrapper. simpl.
      toMLGoal. refine_wf; apply wfWFPattern.
      mlSplitAnd; mlDecomposeAll; only 2: mlSplitAnd; try mlAssumption.
      pose proof (top_holds Γ). use AnyReasoning in H7.
      mlExactMeta H7.
  Defined.

  Reserved Notation "P ===> P'" (at level 80).
  Inductive unification_step {T : Set} {UPT : UP T} : T -> T -> Set :=
    | deleteUS : forall P t,
        P ≠ bottomUP ->
        insertUP P (t, t) ===> P
    | decompositionUS : forall P f t g u,
        P ≠ bottomUP ->
        insertUP P (f wf⋅ t, g wf⋅ u) ===> insertUP (insertUP P (f, g)) (t, u)
    | symbol_clash_lUS : forall P f t,
        P ≠ bottomUP ->
        patt_sym f ≠ `t ->
        (forall x, `t ≠ patt_free_evar x) ->
        insertUP P (patt_sym f ↾ well_formed_sym f, t) ===> bottomUP
    | symbol_clash_rUS : forall P f t,
        P ≠ bottomUP ->
        patt_sym f ≠ `t ->
        (forall x, `t ≠ patt_free_evar x) ->
        insertUP P (t, patt_sym f ↾ well_formed_sym f) ===> bottomUP
    | orientUS : forall P x y,
        P ≠ bottomUP ->
        insertUP P (x, patt_free_evar y ↾ well_formed_free_evar y) ===> insertUP P (patt_free_evar y ↾ well_formed_free_evar y, x)
    | occours_checkUS : forall P x t,
        P ≠ bottomUP ->
        x ∈ free_evars (`t) ->
        insertUP P (patt_free_evar x ↾ well_formed_free_evar x, t) ===> bottomUP
    | eliminationUS : forall P x t,
        P ≠ bottomUP ->
        x ∉ free_evars (`t) ->
        mu_free (`t) ->
        insertUP P (patt_free_evar x ↾ well_formed_free_evar x, t) ===> insertUP (substituteAllUP x t P) (patt_free_evar x ↾ well_formed_free_evar x, t)
  where "P ===> P'" := (unification_step P P').

  (**
    TODO: this axiom should be placed into Γ later, and we have to use `hypothesis`
          to obtain it. For this, we have to create a spec. for unification/term
          algebras.
  *)
  Axiom injectivity : forall Γ f t g u, Γ ⊢ (f ⋅ t) =ml (g ⋅ u) ---> (f =ml g) and (t =ml u).

  Tactic Notation "inside" tactic(inside) "outside" tactic(outside) :=
    match goal with
    | [ |- of_MLGoal _ ] => inside
    | _ => outside
    end.

  Lemma Lemma₃ {T : Set} {UPT : UP T} Γ P P' : theory ⊆ Γ -> P ===> P' -> P' <> bottomUP -> Γ ⊢wf toPredicateUP P wf---> toPredicateUP P'.
  Proof with inside mlClear "_" outside try apply wfWFPattern.
    intros HΓ [] NB; pose proof (toPredicateInsertUP Γ).
    * specialize (H P0 t t).
      unfold WFDerives in H |- *.
      rewrite unwrap_wfwrapper in H.
      apply pf_iff_proj1 in H...
      toMLGoal...
      rewrite ! unwrap_wfwrapper in H |- *.
      mlIntro "H". mlApplyMeta H in "H".
      mlDestructAnd "H" as "_" "H0"...
      mlAssumption.
    * unfold WFDerives in H |- *.
      pose proof (H P0 (f wf⋅ t) (g wf⋅ u)) as H0.
      rewrite unwrap_wfwrapper in H0.
      pose proof (H (insertUP P0 (f, g)) t u) as H1.
      rewrite unwrap_wfwrapper in H1.
      specialize (H P0 f g).
      rewrite unwrap_wfwrapper in H.
      apply pf_iff_proj1 in H0...
      apply pf_iff_proj2 in H1, H...
      toMLGoal...
      rewrite ! unwrap_wfwrapper in H0, H1, H |- *.
      mlIntro "H".
      mlApplyMeta H0 in "H".
      mlDestructAnd "H" as "H0" "H3".
      mlApplyMeta injectivity in "H0".
      mlDestructAnd "H0" as "H1" "H2".
      mlApplyMeta H1.
      mlSplitAnd. mlAssumption.
      mlApplyMeta H. mlSplitAnd; mlAssumption.
    * now destruct NB.
    * now destruct NB.
    * unfold WFDerives in H |- *.
      pose proof (H P0 x (patt_free_evar y ↾ well_formed_free_evar y)) as H0.
      rewrite unwrap_wfwrapper in H0.
      apply pf_iff_proj1 in H0...
      specialize (H P0 (patt_free_evar y ↾ well_formed_free_evar y) x).
      rewrite unwrap_wfwrapper in H.
      apply pf_iff_proj2 in H...
      toMLGoal...
      rewrite ! unwrap_wfwrapper in H0, H |- *.
      mlIntro "H".
      mlApplyMeta H0 in "H". mlDestructAnd "H" as "H0" "H1".
      mlApplyMeta H. mlSplitAnd. mlSymmetry. 1-2: mlAssumption.
    * now destruct NB.
    * unfold WFDerives in H |- *.
      pose proof (H P0 (patt_free_evar x ↾ well_formed_free_evar x) t).
      rewrite unwrap_wfwrapper in H0.
      apply pf_iff_proj1 in H0...
      specialize (H (substituteAllUP x t P0) (patt_free_evar x ↾ well_formed_free_evar x) t).
      rewrite unwrap_wfwrapper in H.
      apply pf_iff_proj2 in H...
      toMLGoal...
      rewrite ! unwrap_wfwrapper in H0, H |- *.
      mlIntro "H".
      mlApplyMeta H0 in "H".
      mlApplyMeta H. simpl.
      pose proof (toPredicateSubstituteAllUP Γ P0 x t).
      unfold WFDerives in H1.
      rewrite ! unwrap_wfwrapper in H1. simpl in H1.
      pose proof (projT2 t). simpl in H2.
      mlRewrite H1 at 1. clear H2.
      opose proof* (Lemma₂ Γ (proj1_sig (toPredicateUP P0)) [(x, projT1 t)] AnyReasoning); cbn; rewrite ? andb_true_r; auto...
      admit.
      simpl in H2. apply pf_iff_proj2 in H2.
      2-3: refine_wf...

      match goal with [H2 : derives_using _ (?x ---> _) _ |- _] => mlAssert ("H0" : x) end. refine_wf...

      mlDestructAnd "H" as "H1" "H2".
      repeat mlSplitAnd; try mlAssumption.
      pose proof (top_holds Γ). use AnyReasoning in H3. mlExactMeta H3.
      mlApplyMeta H2 in "H0".
      mlDestructAnd "H0" as "H1" "H2". mlDestructAnd "H2" as "H3" "_"...
      mlSplitAnd; mlAssumption.
  Admitted.

  Definition compose_substitution (σ η : list (evar * Pattern)) : list (evar * Pattern) := map (fun '(e, p) => (e, substitute_list η p)) σ.

  Definition more_general_substitution (σ η : list (evar * Pattern)) : Prop := exists (θ : list (evar * Pattern)), compose_substitution σ θ = η.

  Definition is_most_general_unifier_of (σ : list (evar * Pattern)) (t₁ t₂ : Pattern) : Type := (forall Γ, Γ ⊢ is_unifier_of σ t₁ t₂) * (forall η, more_general_substitution σ η).

  (* NOTE Could I make US a Prop and use stdpp's rtc for this? *)
  Inductive USrtc {T : Set} {UPT : UP T} : T -> T -> Set :=
    | USrtc_last : forall a, USrtc a a
    | USrtc_step : forall a b c, a ===> b -> USrtc b c -> USrtc a c
  .

  (**
    The formalized unification algorithm gives us an MGU.
  *)
  Axiom convenient : forall {T : Set} {UPT : UP T} σ t1 t2, is_most_general_unifier_of σ (`t1) (`t2) -> {P : T & (USrtc (singletonUP t1 t2) P * (P ≠ bottomUP) * forall Γ, Γ ⊢ projT1 (toPredicateUP P) <---> predicate_list σ)%type}.

  Lemma Lemma₄_helper : forall {T : Set} {UPT : UP T} Γ P P',
    theory ⊆ Γ ->
    USrtc P P' ->
    P' ≠ bottomUP ->
    Γ ⊢wf toPredicateUP P wf---> toPredicateUP P'.
  Proof with apply wfWFPattern.
    intros * HΓ R NB.
    unfold WFDerives.
    rewrite unwrap_wfwrapper.
    induction R.
    aapply A_impl_A...
    toMLGoal. apply well_formed_imp...
    mlIntro "H".
    mlApplyMeta IHR; auto.
    opose proof* (Lemma₃ Γ); eauto.
    {
      inversion R; subst.
      auto.
      pose proof insertNotBottomUP.
      inversion H; subst; apply H1; auto.
    }
    unfold WFDerives in H. rewrite unwrap_wfwrapper in H.
    mlApplyMeta H. mlAssumption.
  Defined.

  From stdpp Require Import gmap.
  Definition wf := Pattern.wf.

  Lemma Lemma₄ : forall Γ (σ : list (evar * Pattern)) (t1 t2 : WFPattern),
    theory ⊆ Γ -> wf (map snd σ) ->
    is_most_general_unifier_of σ (`t1) (`t2) -> Γ ⊢ `t1 =ml `t2 ---> predicate_list σ.
  Proof with try apply wfWFPattern.
    intros * HΓ WFσ HMGU.
    opose proof* (@optionSetUP (gset (WFPattern * WFPattern))).
    1-2: typeclasses eauto.
    pose proof (convenient σ t1 t2 HMGU) as [P [[R NB] EQ] ].
    toMLGoal. simpl. refine_wf...
    now apply wf_predicate_list.
    pose proof (proj2_sig t1). pose proof (proj2_sig t2).
    mlRewrite <- (EQ Γ) at 1.
    clear H H0.
    pose proof (toPredicateSingletonUP Γ t1 t2).
    unfold WFDerives in H. rewrite ! unwrap_wfwrapper in H.
    pose proof (proj2_sig (toPredicateUP P)).
    mlRewrite <- H at 1.
    clear H0.
    opose proof* (Lemma₄_helper Γ); eauto.
    unfold WFDerives in H0. rewrite ! unwrap_wfwrapper in H0.
    mlExactMeta H0.
  Defined.

  Lemma Lemma₆ : forall Γ (σ : list (evar * Pattern)) (t1 t2 : WFPattern),
    theory ⊆ Γ ->
    wf (map snd σ) ->
    mu_free (`t1) -> mu_free (`t2) ->
    forallb mu_free (map snd σ) ->
    is_most_general_unifier_of σ (`t1) (`t2) ->
    Γ ⊢ (`t1 =ml `t2) <---> predicate_list σ.
  Proof with try by refine_wf.
    intros ? ? [t1 wft1] [t2 wft2] HΓ WFσ MFt1 MFt2 MFσ HMGU.
    opose proof* (wf_predicate_list σ) as WFpl...
    toMLGoal... mlSplitAnd; mlIntro "H".
    unshelve opose proof* (Lemma₄ Γ σ (t1 ↾ _) (t2 ↾ _))...
    all: simpl in *. mlApplyMeta H. mlAssumption.
    opose proof* (Lemma₅ σ t1 t2 Γ)...
    destruct HMGU as [IUO _]. specialize (IUO Γ).
    pose proof (MP IUO H). mlApplyMeta H0. mlAssumption.
  Defined.

  Lemma Prop3_full : forall Γ t1 t2,
    theory ⊆ Γ -> well_formed t1 -> well_formed t2 -> mu_free t2 ->
    Γ ⊢ is_functional t1 -> Γ ⊢ is_functional t2 ->
    Γ ⊢ t1 and t2 <---> t1 and t1 =ml t2.
  Proof with try solve [auto | wf_auto2].
    intros * HΓ WFt1 WFt2 MFt2 IFt1 IFt2.
    toMLGoal... mlSplitAnd; mlIntro "H".
    opose proof* (Prop₃_right Γ t1 t2)...
    mlApplyMeta H. mlAssumption.
    opose proof* (Prop₃_left Γ t1 t2)...
    mlApplyMeta H. mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd; only 2: mlSymmetry; mlAssumption.
  Defined.

  Lemma Theorem₁ : forall Γ σ t1 t2,
    theory ⊆ Γ ->
    well_formed t1 -> well_formed t2 ->
    wf (map snd σ) ->
    mu_free t1 -> mu_free t2 ->
    forallb mu_free (map snd σ) ->
    Γ ⊢ is_functional t1 -> Γ ⊢ is_functional t2 ->
    is_most_general_unifier_of σ t1 t2 ->
    (Γ ⊢ (t1 and t2) =ml (t1 and predicate_list σ)) * (Γ ⊢ (t1 and t2) =ml (t2 and predicate_list σ)).
  Proof with try solve [auto | wf_auto2 | refine_wf; auto].
    intros * HΓ WFt1 WFt2 WFσ MFt1 MFt2 MFσ IFt1 IFt2 HMGU.
    opose proof* (Prop3_full Γ t1 t2)...
    assert (Γ ⊢ t1 and t2 <---> t2 and t1 =ml t2). {
      opose proof* (Prop3_full Γ t2 t1)...
      opose proof* (patt_and_comm Γ t1 t2)...
      use AnyReasoning in H1.
      mlRewrite H1 at 1.
      opose proof* (patt_equal_comm t1 t2 Γ).
      1: assumption.
      1-2: wf_auto2.
      use AnyReasoning in H2.
      mlRewrite H2 at 1.
      mlExactMeta H0.
    }
    opose proof* (Lemma₆ Γ σ (t1 ↾ WFt1) (t2 ↾ WFt2))...
    opose proof* (wf_predicate_list σ)...
    split. toMLGoal... 2: toMLGoal...
    all: simpl in H1.
    mlRewrite H at 1. 2: mlRewrite H0 at 1.
    all: mlRewrite H1 at 1; mlReflexivity.
  Defined.

  Tactic Notation "mlConjFast" constr(a) constr(b) "as" constr(c) "wfby" tactic(d) := match goal with | [ |- context[mkNH _ a ?x] ] => match goal with | [ |- context[mkNH _ b ?y] ] => mlAssert (c : (x and y)); [d | mlSplitAnd; [mlExact a | mlExact b] |] end end.

  Tactic Notation "mlConjFast" constr(a) constr(b) "as" constr(c) := mlConjFast a b as c wfby idtac.

  Goal forall Γ (f' g' one' : symbols) (x' y' z' : evar) (*one : WFPattern*),
    x' ≠ z' -> y' ≠ z' ->
    theory ⊆ Γ ->
    let f := (patt_sym f' ↾ well_formed_sym f') in
    let g := (patt_sym g' ↾ well_formed_sym g') in
    let one := (patt_sym one' ↾ well_formed_sym one') in
    let x := (patt_free_evar x' ↾ well_formed_free_evar x') in
    let y := (patt_free_evar y' ↾ well_formed_free_evar y') in
    let z := (patt_free_evar z' ↾ well_formed_free_evar z') in
    let t1 := f wf⋅ x wf⋅ (g wf⋅ one) wf⋅ (g wf⋅ z) in
    let t2 := f wf⋅ (g wf⋅ y) wf⋅ (g wf⋅ y) wf⋅ (g wf⋅ (g wf⋅ x)) in
    (** f is a functional symbol *)
    (all, all, all, ex, (patt_sym f') ⋅ b3 ⋅ b2 ⋅ b1 =ml b0) ∈ Γ ->
    (** g is a functional symbol *)
    (all, ex, (patt_sym g') ⋅ b1 =ml b0) ∈ Γ ->
    (** one is a functional symbol *)
    (ex, patt_sym one' =ml b0) ∈ Γ ->
    (*
      TODO: after defining term algebra spec. these functional axioms should be
      in the theory of the spec.
    *)
    {σ & Γ ⊢ `t1 and `t2 <---> `t1 and predicate_list σ}.
  Proof with try solve [auto | refine_wf; auto; apply wfWFPattern].
    intros * NE1 NE2 HΓ **.
    rename H into Hfunctional_f.
    rename H0 into Hfunctional_g.
    rename H1 into Hfunctional_one.
    evar (σ : list (evar * Pattern)).
    assert (wf (map snd σ)) as WFσ by shelve.
    pose proof (wf_predicate_list σ WFσ) as WFplσ.
    exists σ.
    toMLGoal... mlSplitAnd; mlIntro.
    opose proof* (Prop₃_right Γ (`t1) (`t2))...
    (* functional patterns: *)
    1: {
      subst t1 t2. cbn.
      toMLGoal. { wf_auto2. }
      solve_functional.
    }
    1: {
      subst t1 t2. cbn.
      toMLGoal. { wf_auto2. }
      solve_functional.
    }
    {
      mlApplyMeta H in "0".
      pose proof (@gset_fin_set _ WFPattern_eq_dec ltac:(typeclasses eauto)).
      pose (@optionSetUP _ _ _ _ _ _ _ _ H0 ltac:(typeclasses eauto)).
      opose proof* (Lemma₄_helper Γ (Some (singleton (t1, t2)))). auto.
      eright. pose proof (decompositionUS (Some empty)). simpl in H1. rewrite <- union_empty_r_L. apply H1... rewrite union_empty_r_L.
      eright. epose proof (decompositionUS (Some _)). simpl in H1. apply H1...
      rewrite union_comm_L. rewrite <- union_assoc_L.
      eright. epose proof (deleteUS (Some _)). simpl in H1. apply H1...
      eright. epose proof (decompositionUS (Some _)). simpl in H1. apply H1...
      eright. epose proof (decompositionUS (Some _)). simpl in H1. apply H1...
      rewrite union_comm_L. rewrite <- union_assoc_L.
      eright. epose proof (deleteUS (Some _)). simpl in H1. apply H1...
      rewrite <- union_assoc_L.
      eright. epose proof (decompositionUS (Some _)). simpl in H1. apply H1...
      rewrite union_comm_L. rewrite <- union_assoc_L.
      eright. epose proof (deleteUS (Some _)). simpl in H1. apply H1...
      rewrite (union_comm_L {[(z, g wf⋅ x)]}). rewrite <- union_assoc_L.
      eright. epose proof (orientUS (Some _)). simpl in H1. apply H1... fold y.
      rewrite union_assoc_L. rewrite (union_comm_L {[(y, one)]}).
      left. discriminate. cbn -[f g one x y z] in H1.
      rewrite set_fold_singleton in H1. cbn -[f g one x y z] in H1.
      unfold WFDerives in H1. do 3 rewrite unwrap_wfwrapper in H1. cbn [proj1_sig] in H1.
      mlDestructAnd "0". mlSplitAnd. mlAssumption.
      pose proof (top_holds Γ). use AnyReasoning in H2.
      mlAdd H2.
      Time mlConjFast "2" "0" as "3"... (*wfby (refine_wf; apply wfWFPattern).*)
      (* Record: 0.19s *)
      (* Time mlConj "2" "0" as "3". *)
      (* Record: 38.576s *)
      mlApplyMeta H1 in "3".
      mlClear "0". mlClear "1". mlClear "2". clear H H1 H2.
      opose proof* (set_fold_disj_union_strong_equiv Γ (WFPatt_and ∘ uncurry WFPatt_equal) (Top ↾ well_formed_top)).
      3: unfold WFDerives in H; rewrite unwrap_wfwrapper in H; apply pf_iff_proj1 in H; [mlApplyMeta H in "3" | |]...
      intros. simpl. unfold WFDerives. rewrite ! unwrap_wfwrapper.
      toMLGoal. refine_wf; apply wfWFPattern. mlSplitAnd; mlDecomposeAll; do 2? mlSplitAnd; mlAssumption.
      apply disjoint_singleton_r. set_solver.
      rewrite set_fold_singleton. simpl. case_match. simpl.
      instantiate (σ := [(_, _); (_, _); (_, _)]). simpl.
      mlDestructAnd "3". mlSplitAnd. mlExact "0". mlClear "0". clear H.
      apply (f_equal proj1_sig) in H1. simpl in H1. subst x0.
      opose proof* (set_fold_disj_union_strong_equiv Γ (WFPatt_and ∘ uncurry WFPatt_equal) (Top ↾ well_formed_top)).
      3: unfold WFDerives in H; rewrite unwrap_wfwrapper in H; apply pf_iff_proj1 in H; [mlApplyMeta H in "1" | |]...
      intros. simpl. unfold WFDerives. rewrite ! unwrap_wfwrapper.
      toMLGoal. refine_wf; apply wfWFPattern. mlSplitAnd; mlDecomposeAll; do 2? mlSplitAnd; mlAssumption.
      apply disjoint_singleton_r. set_solver.
      rewrite 2! set_fold_singleton. simpl.
      mlExact "1".
    }
    {
      opose proof* (Lemma₂ Γ (`t1) σ AnyReasoning)...
      opose proof* (wf_substitute_list σ (`t1))...
      apply pf_iff_proj2 in H... mlSplitAnd. mlDestructAnd "0"; mlAssumption.
      mlApplyMeta H in "0". unfold t1. simpl.
      case_match. 2: now destruct n.
      case_match. now destruct NE1.
      mlSimpl. simpl.
      case_match. 2: now destruct n0.
      case_match. now destruct NE2.
      simpl. case_match. 2: now destruct n1.
      mlDecomposeAll.
      do ! mlRewriteBy "2" at 1.
      mlExact "1".
    }
      Unshelve.
      wf_auto2.
      all: typeclasses eauto.
  Defined.

End unification.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.

