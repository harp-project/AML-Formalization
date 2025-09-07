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
    insertUP : T -> (TermPattern * TermPattern) -> T;
    (** Failed unification problem

       bottomUP ~ ⊥
     *)

    bottomUP : T;
    (** Conversion to predicate. Expected to be conjunction of equalities.

       toPredicateUP P ~ ϕᴾ
     *)

    toPredicateUP : T -> WFMFPattern;
    (** Substitution of a variable to a pattern in every pattern of
       a unification problem

       substituteAllUP x t P ~ P{x ↦ t}
     *)

    substituteAllUP : evar -> TermPattern -> T -> T;
    (** Creation of a singleton problem

       singletonUP t u ~ {t ≐ u}
     *)

    singletonUP : TermPattern -> TermPattern -> T;

    (**
       Converting a unification problem maps insertion to conjunction.
     *)
    toPredicateInsertUP : forall Γ t x y, Γ ⊢ toPredicateUP (insertUP t (x, y)) wf<---> ((x wf=ml y) wfand (toPredicateUP t));

    (**
       Converting a unification problem maps substitution of unification problems
       to substitution of patterns.
     *)
    toPredicateSubstituteAllUP : forall Γ t e p, Γ ⊢ toPredicateUP (substituteAllUP e p t) wf<---> (toPredicateUP t)^wf[[evar:e↦p]];

    (**
       Inserting into a non-⊥ unification problem cannot result ⊥.
     *)
    insertNotBottomUP : forall t x, t ≠ bottomUP -> insertUP t x ≠ bottomUP;

    (**
       Converting a singleton problem to a predicate pattern gives us an equality.
     *)
    toPredicateSingletonUP : forall Γ t1 t2, Γ ⊢ toPredicateUP (singletonUP t1 t2) wf<---> (t1 wf=ml t2)
  }.

  Local Definition wfmfTop := mkWFMF Top well_formed_top eq_refl.

  Goal forall φ a b c, (a ≠ c) -> (patt_free_evar c)^[[evar:a↦patt_free_evar b]]^[[evar:c↦φ]] = φ.
  Proof.
    intros.
    simpl.
    rewrite decide_False. assumption.
    simpl. rewrite decide_eq_same.
    reflexivity.
  Qed.

  (* Lemma equality_elimination_functional_subst (Γ : Theory) p q p1 p2 x : *)
  (*   theory ⊆ Γ -> *)
  (*   well_formed p -> *)
  (*   well_formed q -> *)
  (*   well_formed p1 -> *)
  (*   well_formed p2 -> *)
  (*   mu_free p -> *)
  (*   mu_free q -> *)
  (*   pattern_kt_well_formed p1 -> *)
  (*   pattern_kt_well_formed p2 -> *)
  (*   Γ ⊢ p =ml q -> *)
  (*   Γ ⊢ p1 =ml p2 -> *)
  (*   Γ ⊢ is_functional p1 -> *)
  (*   Γ ⊢ p^[[evar: x ↦ p1]] =ml q^[[evar: x ↦ p2]]. *)
  (* Proof. *)
  (*   intros HΓ Hwfp Hwfq Hwfp1 Hwfp2 Hmfp Hmfq Hktwfp1 Hktwfp2 Hpeqq Hp1eqp2 Hfuncp1. *)
  (*   pose proof mf_imp_ktwf _ Hmfp as Hktwfp. *)
  (*   pose proof mf_imp_ktwf _ Hmfq as Hktwfq. *)

    (* apply universal_generalization with (x := x) in Hpeqq; *)
    (* [| try_solve_pile | wf_auto2]. *)
    (* eapply forall_functional_subst_meta with (φ' := p1) in Hpeqq; *)
    (* auto; [|rewrite <- mu_free_evar_quantify | ..]; *)
    (* [| wf_auto2 ..]. *)
    (* rewrite bevar_subst_evar_quantify in Hpeqq; [wf_auto2 |]. *)
    (* mlSimpl in Hpeqq. *)
    (* mlFreshEvar as y. *)
    (* unshelve epose proof MP Hp1eqp2 (equality_elimination Γ p1 p2 {|pcPattern := p^[[evar: x ↦ p1]] =ml q^[[evar: x ↦ patt_free_evar y]]; pcEvar := y|} HΓ _ _ _ _); try solve [wf_auto2]. *)
    (* simpl. rewrite ! pattern_kt_well_formed_free_evar_subst; auto. *)
    (* unfold emplace in H. mlSimpl in H. cbn in H. *)
    (* rewrite -> 2 free_evar_subst_chain in H; [| fm_solve ..]. *)
    (* rewrite -> 2 (free_evar_subst_no_occurrence y) in H; [| fm_solve ..]. *)
    (* exact (MP Hpeqq H). *)
  (* Defined. *)

  (*Goal forall Γ p q p1 p2 x, *)
  (*  theory ⊆ Γ -> *)
  (*  well_formed p -> *)
  (*  well_formed q -> *)
  (*  well_formed p1 -> *)
  (*  well_formed p2 -> *)
  (*  mu_free p -> *)
  (*  mu_free q -> *)
  (*  pattern_kt_well_formed p1 -> *)
  (*  pattern_kt_well_formed p2 -> *)
  (*  Γ ⊢ p =ml q ---> *)
  (*  p1 =ml p2 ---> *)
  (*  is_functional p1 ---> *)
  (*  p^[[evar: x ↦ p1]] =ml q^[[evar: x ↦ p2]]. *)
  (*Proof. *)
  (*  intros * HΓ Hwfp Hwfq Hwfp1 Hwfp2 Hmfp Hmfq Hktwfp1 Hktwfp2. *)
  (*  pose proof mf_imp_ktwf _ Hmfp as Hktwfp. *)
  (*  pose proof mf_imp_ktwf _ Hmfq as Hktwfq. *)
  (*  toMLGoal. wf_auto2. do 3 mlIntro. *)
  (*  mlFreshEvar as y. *)
  (*  unshelve epose proof equality_elimination Γ p1 p2 {| pcEvar := y; pcPattern := p^[[evar:x↦p1]] =ml q^[[evar:x↦patt_free_evar y]] |} HΓ Hwfp1 Hwfp2 _ _. *)
  (*  wf_auto2. *)
  (*  simpl. rewrite ! pattern_kt_well_formed_free_evar_subst; auto. *)
  (*  unfold emplace in H. cbn [pcPattern pcEvar] in H. *)
  (*  mlSimpl in H. rewrite ! free_evar_subst_chain in H. *)
  (*  ltac2:(fm_solve()). *)
  (*  ltac2:(fm_solve()). *)
  (*  rewrite ! (free_evar_subst_no_occurrence y) in H. *)
  (*  ltac2:(fm_solve()). *)
  (*  ltac2:(fm_solve()). *)
  (*  mlApplyMeta H in "1". mlApply "1". clear H. mlClear "1". *)

  (*  Search free_evar_subst. *)

  (*  rewrite <- 2 bevar_subst_evar_quantify with (dbi := 0). *)
  (*  2,3: wf_auto2. *)
  (*  unshelve epose proof forall_functional_subst (p^{{evar:x↦0}} =ml q^{{evar:x↦0}}) p1 Γ HΓ _ Hwfp1 _ _. *)
  (*  1-3: wf_auto2; rewrite <- mu_free_evar_quantify; auto. *)
  (*  mlSimpl in H. mlApplyMeta H. clear H. *)
  (*  mlSplitAnd. 2: mlExact "2". mlClear "2". *) 
  (*  mlIntroAllManual y. *)
  (*  fm_solve. *)
  (*  simpl; rewrite ! free_evars_evar_quantify; fm_solve. *)
  (*  try_solve_pile. *)
    

  (*  Search patt_forall. *)

  (*  mlDeduct "0". *)
  (*  remember (Γ ∪ _) as Γ'. *)
  (*  remember (_ : ProofInfo) as i. *)
  (*  unshelve epose proof universal_generalization Γ' (p =ml q) x i _ _. *)
  (*  subst i. try_solve_pile. *)
  (*  unfold pi_generalized_evars. rewrite ! union_empty_r_L. *)

  (*  mlRevertAll x. *)
  (*  epose proof universal_generalization Γ (p =ml q) x AnyReasoning (pile_any _) (well_formed_equal _ _ Hwfp Hwfq). *)
  (*  mlApplyMeta H in "0". *)
  (*  eapply forall_functional_subst_meta with (φ' := p1) in Hpeqq; *)
  (*  auto; [|rewrite <- mu_free_evar_quantify | ..]; *)
  (*  [| wf_auto2 ..]. *)
  (*  rewrite bevar_subst_evar_quantify in Hpeqq; [wf_auto2 |]. *)
  (*  mlSimpl in Hpeqq. *)
  (*  mlFreshEvar as y. *)
  (*  unshelve epose proof MP Hp1eqp2 (equality_elimination Γ p1 p2 {|pcPattern := p^[[evar: x ↦ p1]] =ml q^[[evar: x ↦ patt_free_evar y]]; pcEvar := y|} HΓ _ _ _ _); try solve [wf_auto2]. *)
  (*  simpl. rewrite ! pattern_kt_well_formed_free_evar_subst; auto. *)
  (*  unfold emplace in H. mlSimpl in H. cbn in H. *)
  (*  rewrite -> 2 free_evar_subst_chain in H; [| fm_solve ..]. *)
  (*  rewrite -> 2 (free_evar_subst_no_occurrence y) in H; [| fm_solve ..]. *)
  (*  exact (MP Hpeqq H). *)
  (*  Defined. *)

    Goal forall Γ e a, theory ⊆ Γ -> e ≠ a -> {x & ((e ∈ free_evars x) * (Γ ⊢ x =ml patt_free_evar a))%type}.
    Proof.
      intros.
      exists (patt_free_evar e and patt_bott or patt_free_evar a).
      split.
      set_solver.
      toMLGoal. wf_auto2.
      mlApplyMeta disj_equals_greater_1. 2: auto.
      fromMLGoal.
      apply phi_impl_total_phi_meta. wf_auto2. try_solve_pile.
      mlIntro. mlDestructAnd "0". mlDestructBot "2".
    Defined.

    (* NOT TRUE *)
    (* Goal forall x Γ e a, theory ⊆ Γ -> well_formed x -> e ∈ free_evars x -> e ≠ a -> Γ ⊢ ! x =ml patt_free_evar a. *)
    (* Proof. *)
    (*   induction x; intros. *)
    (*   - simpl in H1. apply elem_of_singleton_1 in H1. *)
    (*     rewrite <- H1. clear H1. *)
    (*     mlIntro. *)
    (*     (1* Search patt_equal. *1) *)
    (*     unfold patt_equal, patt_total. *)
    (*     mlApply "0". mlClear "0". *)
    (*     unfold patt_iff. *)
    (*     Search patt_not patt_and patt_or. *)
    (*     unshelve epose proof deMorgan_nand Γ (patt_free_evar e ---> patt_free_evar a) (patt_free_evar a ---> patt_free_evar e) _ _. *)
    (*     1-2: wf_auto2. use AnyReasoning in H1. *)
    (*     mlRewrite H1 at 1. clear H1. *)
    (*     mlApplyMeta patt_defined_or_2. *)
    (*     2: assumption. *)
    (*     unshelve epose proof and_impl_2 Γ (patt_free_evar e) (patt_free_evar a) _ _. 1-2: wf_auto2. *)
    (*     use AnyReasoning in H1. mlRewrite H1 at 1. clear H1. *)
    (*     unshelve epose proof and_impl_2 Γ (patt_free_evar a) (patt_free_evar e) _ _. 1-2: wf_auto2. *)
    (*     use AnyReasoning in H1. mlRewrite H1 at 1. clear H1. *)
    (*     Search patt_in. *)
    (*     Search patt_defined. *)
    (* Abort. *)

    Goal forall (Γ : Theory) (φ ψ : Pattern) (e : evar), theory ⊆ Γ -> well_formed φ -> mu_free φ -> well_formed ψ -> e ∉ free_evars φ -> Γ ⊢ is_functional ψ ---> φ ---> φ^[[evar:e↦ψ]].
    Proof.
      intros.
      epose proof universal_generalization_iter Γ [φ] φ e AnyReasoning ltac:(wf_auto2) H0 ltac:(unfold free_evars_of_list; set_solver) ltac:(try_solve_pile) (useBasicReasoning AnyReasoning (A_impl_A Γ φ H0)). simpl in H4.
      unshelve epose proof forall_functional_subst (φ^{{evar:e↦0}}) ψ Γ H ltac:(rewrite <- mu_free_evar_quantify; exact H1) H2 ltac:(wf_auto2) ltac:(wf_auto2).
      rewrite bevar_subst_evar_quantify in H5. wf_auto2.
      do 2 mlIntro. mlApplyMeta H5. mlSplitAnd.
      mlApplyMeta H4. all: mlAssumption.
    Defined.

    Goal forall (x y : TermPattern) (e : evar), TermPattern.
    Proof.
      intros [[x wfx mfx] fpx] [[y wfy mfy] fpy] e.
      unshelve esplit.
      unshelve esplit.
      exact (x^[[evar:e↦y]]).
      apply well_formed_free_evar_subst; assumption.
      apply mu_free_free_evar_subst; assumption.
      simpl in *.
      intros. specialize (fpx Γ). specialize (fpy Γ).
      assert (theory ⊆ Γ) by admit.
      unfold is_functional in *.

      Search patt_exists.
      Print instantiate.
      (* exists_functional_subst_meta *)
      (* Ex_quan *)
      (* congruence_ex *)

      toMLGoal. wf_auto2.
      mlAdd fpx. mlDestructEx "0" as a.
      mlAdd fpy. mlDestructEx "1" as b.
      mlSimpl. unfold evar_open. simpl.
      rewrite ! bevar_subst_not_occur; only 1,2: wf_auto2.

      clear fpx fpy.
      induction x.
      - destruct (decide (e = x)) as [-> |].
        mlExists b. unfold evar_open. mlSimpl. simpl.
        rewrite decide_eq_same bevar_subst_not_occur. wf_auto2.
        mlAssumption.
        mlExists a. unfold evar_open. mlSimpl. simpl.
        rewrite decide_False. assumption.
        rewrite bevar_subst_not_occur. wf_auto2.
        mlAssumption.
      - mlExists a. unfold evar_open. mlSimpl. simpl.
        mlAssumption.
      - cbn in wfx. wf_auto2.
      - cbn in wfx. wf_auto2.
      - mlExists a. unfold evar_open. mlSimpl. simpl.
        mlAssumption.
      -

      destruct (decide (a = e)) as [-> |].
      mlExists b.
      mlSimpl. unfold evar_open. simpl.
      rewrite ! bevar_subst_not_occur. wf_auto2.
      mlSymmetry in "1".
      mlRewriteBy "1" at 1.
      replace y with ((patt_free_evar e)^[[evar:e↦y]]) at 3.
      2: simpl; rewrite decide_eq_same; reflexivity.
      (* Search free_evar_subst. *)

      replace (x^[[evar:e↦y]] =ml (patt_free_evar e)^[[evar:e↦y]]) with ((x =ml (patt_free_evar e))^[[evar:e↦y]]) by reflexivity.
      rewrite <- bevar_subst_evar_quantify with (dbi := 0).
      mlApplyMeta forall_functional_subst.
      mlSplitAnd. 2: mlExists b; mlSimpl; cbn; unfold evar_open; rewrite bevar_subst_not_occur; [wf_auto2 | mlSymmetry; mlAssumption].
      mlClear "1". mlRevert "0". fromMLGoal.
      epose proof universal_generalization_iter Γ [x =ml patt_free_evar e] (x =ml patt_free_evar e) e AnyReasoning ltac:(wf_auto2) ltac:(wf_auto2) ltac2:(fm_solve()) (pile_any _). cbn [foldr] in H0.
      apply H0. aapply A_impl_A.
      1-6: auto; try solve [wf_auto2].
      1-3: mlSimpl; cbn; rewrite ? decide_eq_same; mlSimpl; wf_auto2; rewrite <- mu_free_evar_quantify; assumption.

      Search [is_functional | patt_exists patt_equal b0].

      mlExists a. mlSimpl. unfold evar_open. simpl.
      rewrite bevar_subst_not_occur. wf_auto2.
      replace (patt_free_evar a) with ((patt_free_evar a)^[[evar:e↦y]]) at 2.
      2: simpl; rewrite decide_False; auto.
      replace (x^[[evar:e↦y]] =ml (patt_free_evar a)^[[evar:e↦y]]) with ((x =ml (patt_free_evar a))^[[evar:e↦y]]) by reflexivity.
      rewrite <- bevar_subst_evar_quantify with (dbi := 0). 2: wf_auto2.
      mlApplyMeta forall_functional_subst.
      mlSplitAnd.
      2: mlExists b; mlSimpl; cbn; unfold evar_open; rewrite bevar_subst_not_occur; [wf_auto2 | mlAssumption].
      epose proof universal_generalization_iter Γ [x =ml patt_free_evar a] (x =ml patt_free_evar a) e AnyReasoning ltac:(wf_auto2) ltac:(wf_auto2).

      (**)




      mlExists a. mlSimpl. unfold evar_open. simpl.
      rewrite bevar_subst_not_occur. wf_auto2.
      mlFreshEvar as q.
      assert (e ≠ q) by ltac2:(fm_solve()).
      unshelve epose proof equality_elimination_basic _ x (patt_free_evar a) {| pcEvar := q; pcPattern := (patt_free_evar q)^[[evar:e↦y]] =ml patt_free_evar a |} H _ _ _ _.
      3,4: simpl; rewrite ! (decide_False _ _ H0).
      1-4: wf_auto2.
      simpl in H1. rewrite ! (decide_False _ _ H0) in H1.
      unfold emplace in H1. cbn [pcPattern pcEvar] in H1.


    mlRewriteBy "0" at 1.
    mlSymmetry in "0".
    mlRewriteBy "0" at 1.
    rewrite free_evar_subst_no_occurrence.
    ltac2:(fm_solve()).

  #[refine] Instance optionSetUP `{H : ElemOf (TermPattern * TermPattern) T, H0 : Empty T, H1 : Singleton (TermPattern * TermPattern) T, H2 : Union T, H3 : Intersection T, H4 : Difference T, H5 : Elements (TermPattern * TermPattern) T, @FinSet (TermPattern * TermPattern) T H H0 H1 H2 H3 H4 H5 (@prod_eq_dec _ TermPattern_eq_dec _ TermPattern_eq_dec), !LeibnizEquiv T} : UP (option T) := {
    insertUP t x := option_map ({[x]} ∪.) t;
    bottomUP := None;
    toPredicateUP := from_option (set_fold (WFMF_and ∘ (fun '(x, y) => tpPattern x wf=ml tpPattern y)) wfmfTop) (mkWFMF patt_bott well_formed_bott eq_refl);
    substituteAllUP e p := option_map (set_map (fun '(x, y) => ((tpPattern x)^wf[[evar:e↦p]], (tpPattern y)^wf[[evar:e↦p]])));
    singletonUP t1 t2 := Some {[(t1, t2)]}
  }.
  Proof.
    * intros. destruct_with_eqn t; simpl.
      ** remember (λ '(x0, y0), x0 wf=ml y0) as f.
         epose proof (elem_of_dec_slow (x, y) t0) as [].
         pose proof (in_set_implies_in_predicate Γ f wfmfTop _ _ e).
         rewrite subseteq_union_1_L. set_solver.
         toMLGoal. apply wfmfWF.
         rewrite ! unwrap_wfmfbWrapper in H7 |- *. simpl in H7 |- *.
         mlSplitAnd; mlDecomposeAll.
         mlSplitAnd. subst f.
         rewrite unwrap_wfmfbWrapper in H7. simpl in H7.
         mlApplyMeta H7. 1-3: mlAssumption.
         rewrite union_comm_L.
         opose proof* (set_fold_disj_union_strong_equiv Γ (WFMF_and ∘ f) wfmfTop t0 {[(x, y)]} _ _).
         intros. subst f. simpl. do ! case_match.
         toMLGoal. apply wfmfWF. rewrite ! unwrap_wfmfbWrapper. simpl.
         mlSplitAnd; mlDecomposeAll; repeat mlSplitAnd; mlAssumption.
         set_solver.
         rewrite set_fold_singleton in H7. simpl in H7. subst f.
         exact H7.
      ** case_match. simpl.
         apply (f_equal TacticsNotations.wfmfPattern) in H7. rewrite ! unwrap_wfmfbWrapper in H7. simpl in H7.
         rewrite <- H7. toMLGoal. refine_wf; apply TacticsNotations.wfmfWF.
         mlSplitAnd; mlDecomposeAll; mlDestructBotDocVer.
    * intros. destruct_with_eqn t; simpl.
      ** remember (λ '(x, y), x wf=ml y) as f.
         remember (λ '(x, y), (x^wf[[evar:e↦p]], y^wf[[evar:e↦p]])) as g.
         apply (set_fold_ind' (fun r X => Γ ⊢ set_fold (WFMF_and ∘ f) wfmfTop (set_map g X) wf<---> r^wf[[evar:e↦p]]) (WFMF_and ∘ f) wfmfTop).
         rewrite -> set_map_empty, set_fold_empty.
         toMLGoal. apply wfmfWF.
         rewrite ! unwrap_wfmfbWrapper. simpl.
         mlSplitAnd; mlDecomposeAll.
         mlAssumption. pose proof (top_holds Γ). use AnyReasoning in H7. mlExactMeta H7.
         intros. simpl. rewrite -> set_map_union_L, set_map_singleton_L.
         unshelve epose proof (elem_of_dec_slow (g x) (set_map g X)) as [].
         1: exact T.
         exact (@prod_eq_dec _ WFMFPattern_eq_dec _ WFMFPattern_eq_dec).
         4: exact H6. 1-3: auto.
         rewrite subseteq_union_1_L. apply elem_of_subseteq_singleton. exact e0.
         epose proof (in_set_implies_in_predicate Γ f wfmfTop _ _ e0).
         toMLGoal. apply wfmfWF.
         rewrite ! unwrap_wfmfbWrapper in H8, H9 |- *.
         cbn -[patt_and] in H8, H9 |- *. mlSimpl.
         mlSplitAnd; mlDecomposeAll. mlSplitAnd.
         mlApplyMeta H9 in "0". subst f g. case_match.
         rewrite ! unwrap_wfmfbWrapper. cbn -[patt_equal]. mlSimpl.
         mlAssumption.
         apply pf_iff_proj1 in H8. mlApplyMeta H8. mlAssumption.
         1-2: refine_wf; apply wfmfWF.
         apply pf_iff_proj2 in H8. mlApplyMeta H8. mlAssumption.
         1-2: refine_wf; apply wfmfWF.
         rewrite union_comm_L.
         unshelve opose proof* (set_fold_disj_union_strong_equiv Γ (WFMF_and ∘ f) wfmfTop (set_map g X) {[g x]}).
         5: exact H6. all: auto.
         intros.
         subst f g. simpl. repeat case_match.
         toMLGoal. apply wfmfWF.
         rewrite ! unwrap_wfmfbWrapper. simpl. mlSplitAnd; mlDecomposeAll;
         repeat mlSplitAnd; mlAssumption.
         set_solver.
         rewrite ! unwrap_wfmfbWrapper in H8, H9 |- *.
         cbn -[patt_and] in H8, H9 |- *.
         eapply pf_iff_equiv_trans. 4: exact H9.
         1-3: refine_wf; apply wfmfWF.
         rewrite set_fold_singleton. cbn [compose].
         mlSimpl. rewrite unwrap_wfmfbWrapper. simpl.
         toMLGoal. refine_wf; apply wfmfWF.
         mlSplitAnd; mlDecomposeAll; mlSplitAnd.
         subst f g. case_match. rewrite ! unwrap_wfmfbWrapper.
         cbn -[patt_equal]. mlSimpl. mlAssumption.
         apply pf_iff_proj1 in H8. mlApplyMeta H8. mlAssumption.
         1-2: refine_wf; apply wfmfWF.
         subst f g. case_match. rewrite ! unwrap_wfmfbWrapper.
         cbn -[patt_equal]. mlSimpl. mlAssumption.
         apply pf_iff_proj2 in H8. mlApplyMeta H8. mlAssumption.
         1-2: refine_wf; apply wfmfWF.
      ** case_match. apply (f_equal TacticsNotations.wfmfPattern) in H7. rewrite unwrap_wfmfbWrapper in H7. simpl in H7. simpl. rewrite H7. now aapply pf_iff_equiv_refl.
    * intros. destruct_with_eqn t. simpl. discriminate. now destruct H7.
    * intros. simpl. rewrite set_fold_singleton. simpl.
      rewrite ! unwrap_wfmfbWrapper. simpl.
      toMLGoal. refine_wf; apply wfmfWF.
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
      patt_sym f ≠ wfmfPattern t ->
      (forall x, wfmfPattern t ≠ patt_free_evar x) ->
      insertUP P (mkWFMF (patt_sym f) (well_formed_sym f) eq_refl, t) ===> bottomUP
  | symbol_clash_rUS : forall P f t,
      P ≠ bottomUP ->
      patt_sym f ≠ wfmfPattern t ->
      (forall x, wfmfPattern t ≠ patt_free_evar x) ->
      insertUP P (t, mkWFMF (patt_sym f) (well_formed_sym f) eq_refl) ===> bottomUP
  | orientUS : forall P x y,
      P ≠ bottomUP ->
      insertUP P (x, mkWFMF (patt_free_evar y) (well_formed_free_evar y) eq_refl) ===> insertUP P (mkWFMF (patt_free_evar y) (well_formed_free_evar y) eq_refl, x)
  | occours_checkUS : forall P x t,
      P ≠ bottomUP ->
      x ∈ free_evars (wfmfPattern t) ->
      insertUP P (mkWFMF (patt_free_evar x) (well_formed_free_evar x) eq_refl, t) ===> bottomUP
  | eliminationUS : forall P x t,
      P ≠ bottomUP ->
      x ∉ free_evars (wfmfPattern t) ->
      insertUP P (mkWFMF (patt_free_evar x) (well_formed_free_evar x) eq_refl, t) ===> insertUP (substituteAllUP x t P) (mkWFMF (patt_free_evar x) (well_formed_free_evar x) eq_refl, t)
      where "P ===> P'" := (unification_step P P').

Inductive USrtc {Σ : Signature} {syntax : Syntax} {T : Set} {UPT : UP T} : T -> T -> Set :=
  | USrtc_last : forall a, USrtc a a
  | USrtc_step : forall a b c, a ===> b -> USrtc b c -> USrtc a c
.

