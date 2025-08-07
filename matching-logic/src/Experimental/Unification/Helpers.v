From MatchingLogic.Theories Require Export FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

From MatchingLogic Require Export Unification.TacticsNotations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Section Helpers.
  Context {Σ : Signature} {syntax : Syntax}.

  Definition get_fresh_evar (φ : Pattern) : sig (.∉ free_evars φ).
  Proof.
    exists (fresh_evar φ); auto.
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

  (* Similar proof as in Definedness_ProofSystem but object level. *)
  Lemma def_of_pred_impl_pred_obj Γ ψ :
    theory ⊆ Γ ->
    well_formed ψ ->
    Γ ⊢ is_predicate_pattern ψ ---> ⌈ ψ ⌉ ---> ψ.
  Proof.
    intros HΓ wfψ.
    toMLGoal. wf_auto2. 
    mlIntro "H0".
    mlDestructOr "H0" as "H1" "H1".
    - mlRewriteBy "H1" at 2.
      mlClear "H1".
      unfold patt_top. mlIntro. mlIntro. mlExactn 1.
    - mlRewriteBy "H1" at 2.
      mlRewriteBy "H1" at 1.
  mlClear "H1".
  fromMLGoal.
  aapply bott_not_defined.
  Defined.

  Lemma extend_total_to_imp Γ p f :
    theory ⊆ Γ ->
    well_formed p ->
    well_formed f ->
    Γ ⊢ is_predicate_pattern p ---> (p ---> ⌊ f ⌋) ---> ⌊ p ---> f ⌋.
  Proof.
    intros HΓ Hwfp Hwff.
    do 2 mlIntro.
    epose proof (def_of_pred_impl_pred_obj Γ p HΓ Hwfp).
    mlApplyMeta H in "0".
    opose proof (syllogism Γ ⌈ p ⌉ p ⌊ f ⌋ _ Hwfp _).
    1-2: wf_auto2. use AnyReasoning in H0.
    mlApplyMeta H0 in "0". mlApply "0" in "1".
    opose proof (impl_eq_or Γ ⌈ p ⌉ ⌊ f ⌋ _ _).
    1-2: wf_auto2. use AnyReasoning in H1.
    apply pf_iff_proj1 in H1. 2-3: wf_auto2.
    mlApplyMeta H1 in "1".
    epose proof (def_propagate_not Γ p HΓ Hwfp).
    use AnyReasoning in H2.
    mlAssert ("2" : (⌊ ! p ⌋ or ⌊ f ⌋)).
    wf_auto2. mlRewrite <- H2 at 1. mlAssumption.
    opose proof (patt_or_total Γ (! p) f AnyReasoning HΓ _ Hwff).
    wf_auto2. mlApplyMeta H3 in "2".
    epose proof (impl_eq_or Γ p f Hwfp Hwff).
    use AnyReasoning in H4.
    mlRewrite H4 at 1. mlAssumption.
  Defined.

  Lemma extract_common_from_equality_r_2 Γ a b p :
    theory ⊆ Γ ->
    well_formed a ->
    well_formed b ->
    well_formed p ->
    Γ ⊢ is_predicate_pattern p --->
    (p ---> a =ml b) <---> (a and p) =ml (b and p).
  Proof.
    intros HΓ Hwfa Hwfb Hwfp.
    mlIntro.
    mlSplitAnd; mlIntro.
    -
      opose proof (extend_total_to_imp Γ p (a <---> b) HΓ Hwfp _). wf_auto2.
      mlApplyMeta H in "0". mlApply "0" in "1".
      mlClear "0". mlDeductHypo "1". 2: wf_auto2.
      remember (Γ ∪ _) as Γ'.
      epose proof (extract_common_from_equivalence_r Γ' p a b i Hwfp Hwfa Hwfb).
      apply pf_iff_proj2 in H1. 2-3: wf_auto2.
      apply (MP H0) in H1. mlRewrite H1 at 1. mlReflexivity.
    -
      mlIntro.
      mlApplyMeta predicate_equiv in "0". 2: auto.
      mlDestructAnd "0". mlApply "3" in "2".
      mlClear "3". mlClear "4".
      mlConj "1" "2" as "0".
      mlClear "1". mlClear "2".
      epose proof patt_total_and _ _ _ HΓ _ _.
      use AnyReasoning in H.
      apply pf_iff_proj2 in H.
      mlApplyMeta H in "0". 2-3: wf_auto2. clear H.
      mlDeductHypo "0".
      2: wf_auto2.
      remember (Γ ∪ _) as Γ'.
      pose proof extract_common_from_equivalence_r Γ' p a b i Hwfp Hwfa Hwfb.
      apply pf_iff_proj1 in H0.
      apply lhs_from_and in H0.
      apply (MP H) in H0.
      mlRewrite H0 at 1. mlReflexivity.
      Unshelve.
      all: wf_auto2.
  Defined.

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

End Helpers.

