From MatchingLogic.Theories Require Export FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

From MatchingLogic Require Export Unification.Helpers.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Section Definitions.
  Context {Σ : Signature} {syntax : Syntax}.

  Definition is_unifier_of (σ : list (evar * Pattern)) t₁ t₂ :=
    substitute_list σ t₁ =ml substitute_list σ t₂.

  Lemma wf_is_unifier_of : forall σ t₁ t₂,
    wf (map snd σ) ->
    well_formed t₁ ->
    well_formed t₂ ->
    well_formed (is_unifier_of σ t₁ t₂).
  Proof.
    intros.
    apply well_formed_equal; apply wf_substitute_list; assumption.
  Qed.

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

  Definition compose_substitution (σ η : list (evar * Pattern)) : list (evar * Pattern) := map (fun '(e, p) => (e, substitute_list η p)) σ.

  Definition more_general_substitution (σ η : list (evar * Pattern)) : Prop := exists (θ : list (evar * Pattern)), compose_substitution σ θ = η.

  Definition is_most_general_unifier_of (σ : list (evar * Pattern)) (t₁ t₂ : Pattern) : Type := (forall Γ, Γ ⊢ is_unifier_of σ t₁ t₂) * (forall η, more_general_substitution σ η).

End Definitions.

Reserved Notation "P ===> P'" (at level 80).
Inductive unification_step {Σ : Signature} {syntax : Syntax} {T : Set} {UPT : UP T} : T -> T -> Set :=
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

Inductive USrtc {Σ : Signature} {syntax : Syntax} {T : Set} {UPT : UP T} : T -> T -> Set :=
  | USrtc_last : forall a, USrtc a a
  | USrtc_step : forall a b c, a ===> b -> USrtc b c -> USrtc a c
.

