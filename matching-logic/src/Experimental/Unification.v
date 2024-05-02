From Coq Require Import ssreflect ssrfun ssrbool.

(* From Ltac2 Require Import Ltac2. *)

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem FOEquality_ProofSystem DeductionTheorem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

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

  (* These [are from/should be part of] that branch. *)
  (* https://github.com/harp-project/AML-Formalization/blob/09f24d95119769ce578c8c15eceba5a3a00c45d4/matching-logic/src/Theories/Nat_ProofSystem.v#L392 *)
  Section predicate_stuff.

    Axiom predicate_equiv :
      forall Γ φ,
        theory ⊆ Γ ->
        well_formed φ ->
        Γ ⊢ is_predicate_pattern φ ---> φ <---> ⌊φ⌋.

    Axiom predicate_imp :
      forall Γ φ ψ,
        Definedness_Syntax.theory ⊆ Γ ->
        well_formed φ ->
        well_formed ψ ->
        Γ ⊢ is_predicate_pattern φ --->
            is_predicate_pattern ψ --->
            is_predicate_pattern (φ ---> ψ).

    Lemma predicate_bott : forall Γ,
      theory ⊆ Γ -> Γ ⊢ is_predicate_pattern ⊥.
    Proof with wf_auto2.
      intros * HΓ.
      unfold is_predicate_pattern.
      toMLGoal...
      mlRight. mlReflexivity.
    Defined.

    Lemma predicate_not : forall Γ φ,
      theory ⊆ Γ -> well_formed φ ->
      Γ ⊢ is_predicate_pattern φ ---> is_predicate_pattern (! φ).
    Proof.
      intros * HΓ wfφ.
      unfold patt_not.
      pose proof (predicate_imp Γ φ ⊥ HΓ wfφ well_formed_bott).
      mlIntro.
      mlAdd (predicate_bott Γ HΓ).
      mlRevert "1".
      (* mlRevert "0". *)
      fromMLGoal.
      exact H.
    Defined.

    Lemma predicate_or : forall Γ φ₁ φ₂,
      theory ⊆ Γ -> well_formed φ₁ -> well_formed φ₂ ->
      Γ ⊢ is_predicate_pattern φ₁ ---> is_predicate_pattern φ₂ --->
          is_predicate_pattern (φ₁ or φ₂).
    Proof.
      intros * HΓ wfφ₁ wfφ₂.
      unfold patt_or.
      pose proof (predicate_not Γ φ₁ HΓ wfφ₁).
      mlIntro.
      mlApplyMeta H in "0".
      fromMLGoal.
      apply predicate_imp; auto.
    Defined.

    Lemma predicate_and : forall Γ φ₁ φ₂,
      theory ⊆ Γ -> well_formed φ₁ -> well_formed φ₂ ->
      Γ ⊢ is_predicate_pattern φ₁ ---> is_predicate_pattern φ₂ --->
          is_predicate_pattern (φ₁ and φ₂).
    Proof.
      intros * HΓ wfφ₁ wfφ₂.
      unfold patt_and.
      mlIntro.
      mlIntro.
      mlApplyMeta predicate_not in "0".
      mlApplyMeta predicate_not in "1".
      mlApplyMeta predicate_or in "0".
      mlApplyMeta predicate_not.
      mlApply "0". mlExact "1".
      all: auto.
    Defined.

  End predicate_stuff.

  Section helpers.

    Lemma functional_pattern_defined :
      forall Γ φ, theory ⊆ Γ -> well_formed φ ->
         Γ ⊢ (ex , (φ =ml b0)) ---> ⌈ φ ⌉.
    Proof.
      intros Γ φ HΓ Wf.
      toMLGoal. wf_auto2.
      mlIntro "H0".
      mlApplyMeta (forall_functional_subst ⌈ b0 ⌉ φ _ HΓ ltac:(wf_auto2)
      ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
      mlSplitAnd.
      * mlClear "H0". fromMLGoal. wf_auto2.
        remember (fresh_evar patt_bott) as x.
        pose proof (universal_generalization Γ ⌈patt_free_evar x⌉ x AnyReasoning (pile_any _)) 
          as H1'.
        cbn in H1'. case_match. 2: congruence. apply H1'. reflexivity.
        gapply defined_evar.
        { apply pile_any. }
        { exact HΓ. }
      * mlExact "H0".
    Defined.

    Lemma membership_equal_equal :
      forall Γ φ φ',
        theory ⊆ Γ -> mu_free φ' ->
        well_formed φ -> well_formed φ' ->
        Γ ⊢ (ex , (φ =ml b0))  ->
        Γ ⊢ (ex , (φ' =ml b0))  ->
        Γ ⊢ (φ ∈ml φ') =ml (φ =ml φ') .
    Proof.
      intros Γ φ φ' HΓ Mufree Wf1 Wf2 Func1 Func2.
      unfold patt_equal at 1.

      toMLGoal. wf_auto2.
      mlIntro.
      pose proof (bott_not_defined Γ) as H.
      use AnyReasoning in H.
      mlApplyMeta H.
      fromMLGoal. wf_auto2.

      apply ceil_monotonic; auto.
      { wf_auto2. }

      toMLGoal. wf_auto2.
      pose proof (not_not_intro Γ ((φ ∈ml φ' <---> φ =ml φ' ))
      ltac:(wf_auto2)) as H0.
      use AnyReasoning in H0.
      mlApplyMeta H0.
      mlSplitAnd; mlIntro.
      * mlApplyMeta membership_imp_equal_meta; auto. mlExactn 0.
      * mlApplyMeta equal_imp_membership; auto. mlExactn 0.
        Unshelve.
        toMLGoal. wf_auto2.
        (* clear h. *)
        mlApplyMeta functional_pattern_defined; auto.
        mlExactMeta Func2.
    Defined.

    Lemma free_evar_subst_id :
      forall φ x, φ^[[evar: x ↦ patt_free_evar x]] = φ.
    Proof.
      induction φ; intros x'; simpl; auto.
      * case_match; subst; auto.
      * rewrite IHφ1. now rewrite IHφ2.
      * rewrite IHφ1. now rewrite IHφ2.
      * now rewrite IHφ.
      * now rewrite IHφ.
    Qed.

    Lemma foldr_ind {A B} (P : B -> Prop) (Q : A -> Prop) (f : A -> B -> B) (b : B) (l : list A) : P b -> Forall Q l -> (forall a b, Q a -> P b -> P (f a b)) -> P (foldr f b l).
    Proof.
      intros.
      induction l; simpl; inversion H0; auto.
    Defined.

    Lemma foldr_ind_set {A B} (P : B -> Set) (Q : A -> Set) (f : A -> B -> B) (b : B) (l : list A) : P b -> foldr (prod ∘ Q) True l -> (forall a b, Q a -> P b -> P (f a b)) -> P (foldr f b l).
    Proof.
      intros.
      induction l; simpl in X |- *;
      only 2: destruct X; auto.
    Defined.

    Lemma fold_left_ind {A B} (P : B -> Prop) (Q : A -> Prop) (f : B -> A -> B) (b : B) (l : list A) : P b -> Forall Q l -> (forall a b, Q a -> P b -> P (f b a)) -> P (fold_left f l b).
    Proof.
      intros.
      generalize dependent b.
      induction l; simpl; intros; inversion H0; auto.
    Defined.

    Lemma foldr_andb_equiv_foldr_conj {A : Type} (t : A -> bool) (xs : list A) : foldr (fun c a => t c && a) true xs <-> foldr (fun c a => (t c) = true /\ a) True xs.
    Proof.
      induction xs; simpl.
      split; split.
      destruct IHxs.
      split; intro.
      apply andb_true_iff in H1. destruct H1.
      split. exact H1.
      exact (H H2).
      destruct H1.
      apply andb_true_iff.
      split.
      exact H1.
      exact (H0 H2).
    Defined.

    Lemma foldr_map_thing {A B C : Type} (f : A -> B -> B) (g : C -> A) (x : B) (xs : list C) : foldr f x (map g xs) = foldr (fun c a => f (g c) a) x xs.
    Proof.
      induction xs.
      reflexivity.
      simpl. f_equal. exact IHxs.
    Defined.

    Lemma Forall_wf_thing {A} (t : A -> Pattern) l : Forall (well_formed ∘ t) l <-> wf (map t l).
    Proof.
      intros. etransitivity. apply Forall_fold_right. unfold wf.
      rewrite -> 2 foldr_map_thing, foldr_andb_equiv_foldr_conj.
      reflexivity.
    Defined.

    Lemma mu_free_free_evar_subst :
      forall φ ψ x,
      mu_free φ -> mu_free ψ ->
      mu_free (free_evar_subst ψ x φ).
    Proof.
      induction φ; intros; simpl; auto.
      * case_match; auto.
      * rewrite IHφ1. 3: rewrite IHφ2. all: simpl in H; destruct_and! H; auto.
      * rewrite IHφ1. 3: rewrite IHφ2. all: simpl in H; destruct_and! H; auto.
    Qed.

    Lemma extract_common_from_equivalence_r Γ a b c i :
      well_formed a -> well_formed b -> well_formed c ->
      Γ ⊢i (b and a <---> c and a) <---> (a ---> b <---> c) using i.
    Proof.
      intros wfa wfb wfc.
      pose proof (extract_common_from_equivalence Γ a b c wfa wfb wfc).
      use i in H.
      pose proof (patt_and_comm Γ b a wfb wfa).
      use i in H0.
      pose proof (patt_and_comm Γ c a wfc wfa).
      use i in H1.
      mlRewrite H0 at 1.
      mlRewrite H1 at 1.
      fromMLGoal.
      exact H.
    Defined.

    Lemma pf_iff_equiv_trans_obj : forall Γ A B C i,
      well_formed A -> well_formed B -> well_formed C ->
      Γ ⊢i (A <---> B) ---> (B <---> C) ---> (A <---> C) using i.
    Proof.
      intros * wfA wfB wfC.
      do 2 mlIntro.
      mlDestructAnd "0".
      mlDestructAnd "1".
      mlSplitAnd.
      pose proof (syllogism Γ _ _ _ wfA wfB wfC).
      use i in H.
      mlApplyMeta H in "2".
      mlApply "0" in "2".
      mlExact "0".
      pose proof (syllogism Γ _ _ _ wfC wfB wfA).
      use i in H.
      mlApplyMeta H in "4".
      mlApply "4" in "3".
      mlExact "3".
    Defined.

    Lemma pf_iff_equiv_sym_obj Γ A B i :
      well_formed A -> well_formed B -> Γ ⊢i (A <---> B) ---> (B <---> A) using i.
    Proof.
      intros wfa wfb.
      mlIntro.
      mlDestructAnd "0".
      mlSplitAnd; mlAssumption.
    Defined.

    Lemma free_evar_subst_chain :
      forall φ x y ψ,
      y ∉ free_evars φ ->
      φ^[[evar: x ↦ patt_free_evar y]]^[[evar:y ↦ ψ]] =
      φ^[[evar: x ↦ ψ]].
    Proof.
      induction φ; intros; simpl; auto.
      * simpl. case_match; simpl; case_match; try reflexivity.
        1: congruence.
        subst. set_solver.
      * rewrite IHφ1. set_solver. rewrite IHφ2. set_solver. reflexivity.
      * rewrite IHφ1. set_solver. rewrite IHφ2. set_solver. reflexivity.
      * rewrite IHφ; by set_solver.
      * rewrite IHφ; by set_solver.
    Qed.

    Definition get_fresh_evar (φ : Pattern) : sig (.∉ free_evars φ).
    Proof.
      exists (fresh_evar φ); auto.
    Defined.

    Lemma patt_free_evar_subst : forall x φ, (patt_free_evar x)^[[evar: x ↦ φ]] = φ.
    Proof.
      intros.
      simpl.
      case_match.
      reflexivity.
      contradiction.
    Defined.

    Lemma extract_common_from_equality_r a b x Γ :
      theory ⊆ Γ ->
      well_formed a -> well_formed b -> well_formed x ->
      Γ ⊢ is_predicate_pattern x --->
          x ---> a =ml b <---> (a and x) =ml (b and x).
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
      epose proof (hypothesis (Γ ∪ {[p]}) p _ ltac:(set_solver)). use i in H.
      epose proof (extract_common_from_equivalence_r _ _ _ _ _ _ _ _).
      apply (pf_iff_proj1) in H0.
      apply lhs_from_and in H0.
      apply (MP H) in H0.
      mlAdd H.
      mlRewrite H0 at 1.
      mlReflexivity.
      Unshelve. all: wf_auto2.
    Defined.

  End helpers.

  Section corollaries.

    Corollary wf_fold_left {A : Type} (f : Pattern -> A -> Pattern) (t : A -> Pattern) x xs :
      well_formed x ->
      wf (map t xs) ->
      (forall a b, well_formed a -> well_formed (t b) -> well_formed (f a b)) ->
      well_formed (fold_left f xs x).
    Proof.
      intros. apply fold_left_ind with (Q := well_formed ∘ t);
      only 2: apply Forall_wf_thing; auto.
    Defined.

    Corollary wf_foldr {A : Type} (f : A -> Pattern -> Pattern) (t : A -> Pattern) x xs :
      well_formed x ->
      wf (map t xs) ->
      (forall a b, well_formed a -> well_formed (t b) -> well_formed (f b a)) ->
      well_formed (foldr f x xs).
    Proof.
      intros.
      apply foldr_ind with (Q := well_formed ∘ t);
      only 2: apply Forall_wf_thing; auto.
    Defined.

    Corollary mf_fold_left {A : Type} (f : Pattern -> A -> Pattern) (t : A -> Pattern) x xs :
      mu_free x ->
      foldr (fun c a => mu_free c && a) true (map t xs) ->
      (forall a b, mu_free a -> mu_free (t b) -> mu_free (f a b)) ->
      mu_free (fold_left f xs x).
    Proof.
      intros.
      apply fold_left_ind with (Q := mu_free ∘ t);
      only 2: apply Forall_fold_right;
      only 2: rewrite -> foldr_map_thing, foldr_andb_equiv_foldr_conj in H0;
      auto.
    Defined.

  End corollaries.

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

  (* foldr_ind_set is more general *)
  Lemma foldr_preserves_function_set {A : Type} (t : A -> Pattern) (P : Pattern -> Set) (f : A -> Pattern -> Pattern) x xs :
    P x -> foldr (fun c a => (P (t c) * a)%type) True xs -> (forall a b, P a -> P (t b) -> P (f b a)) -> P (foldr f x xs).
  Proof.
    intros.
    apply foldr_ind_set with (Q := P ∘ t); auto.
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
    pose proof (foldr_preserves_function_set (λ '(x, φ), patt_free_evar x =ml φ) (λ φ, well_formed φ -> Γ ⊢ is_predicate_pattern φ) (λ '(x, φ') (φ : Pattern), patt_free_evar x =ml φ' and φ) patt_top σ).
    ospecialize* X. 1-4: clear X.
    * intro. toMLGoal... mlLeft. mlReflexivity.
    * induction σ; split.
      ** destruct a. intro. unfold "=ml".
         eapply useGenericReasoning.
         apply pile_any.
         apply floor_is_predicate; auto...
      ** apply IHσ...
    * intros ? [] ? ? ?.
      eenough (well_formed _).
      eenough (well_formed _).
      pose proof (predicate_and Γ _ _ HΓ H2 H3).
      apply (MP (H0 H2)) in H4.
      apply (MP (H H3)) in H4.
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
    unfold evar_open.
    rewrite bevar_subst_not_occur.
    wf_auto2.
    simpl.
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
  Notation "a wf$ b" := (WFPatt_app a b) (at level 65, right associativity) : ml_scope.
  Lemma well_formed_free_evar : forall e, well_formed (patt_free_evar e).
  Proof.
    exact (const eq_refl).
  Defined.

  Class UP (T : Type) := {
    insertUP : T -> (WFPattern * WFPattern) -> T;
    bottomUP : T;
    toPredicateUP : T -> WFPattern;
    substituteAllUP : evar -> WFPattern -> T -> T;
    singletonUP : WFPattern -> WFPattern -> T;
    toPredicateInsertUP : forall Γ t x y, Γ ⊢wf toPredicateUP (insertUP t (x, y)) wf<---> ((x wf=ml y) wfand (toPredicateUP t));
    toPredicateSubstituteAllUP : forall Γ t e p, (*e ∉ free_evars p ->*) Γ ⊢wf toPredicateUP (substituteAllUP e p t) wf<---> (toPredicateUP t)^wf[[evar:e↦p]];
    insertNotBottomUP : forall t x, t ≠ bottomUP -> insertUP t x ≠ bottomUP;
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

  Section stdpp_but_for_set.

    Lemma set_choose_or_empty' `{FinSet A C} (X : C) : (sig (.∈ X)) + (X ≡ ∅).
    Proof.
      destruct (elements X) as [|x l] eqn:HX; [right|left].
      * apply equiv_empty; intros x. by rewrite <-elem_of_elements, HX, elem_of_nil.
      * exists x. rewrite <-elem_of_elements, HX. by left.
    Qed.

    Lemma set_ind' `{FinSet A C, !LeibnizEquiv C} (P : C → Set) :
      P ∅ → (∀ x X, x ∉ X → P X → P ({[ x ]} ∪ X)) → ∀ X, P X.
    Proof.
      intros Hemp Hadd. apply well_founded_induction with (⊂).
      apply set_wf. 
      intros X IH.
      destruct (set_choose_or_empty' X) as [[x ?H]|HX].
      * pose proof (elem_of_subseteq_singleton x X) as [? _].
        specialize (H8 H7).
        unshelve epose proof (union_difference {[ x ]} X H8).
        apply elem_of_dec_slow. apply leibniz_equiv_iff in H9.
        rewrite H9. clear H8 H9.
        apply Hadd. 2: apply IH. all: set_solver.
      * apply leibniz_equiv_iff in HX. by rewrite HX.
    Qed.

    Lemma set_fold_ind' {B} `{FinSet A C, !LeibnizEquiv C} (P : B → C → Set) (f : A → B → B) (b : B) :
      P b ∅ → (∀ x X r, x ∉ X → P r X → P (f x r) ({[ x ]} ∪ X)) →
      ∀ X, P (set_fold f b X) X.
    Proof.
      intros Hemp Hadd.
      enough (∀ l, NoDup l → ∀ X, (∀ x, x ∈ X ↔ x ∈ l) → P (foldr f b l) X) as help.
      { intros ?. apply help; [apply NoDup_elements|].
        symmetry. apply elem_of_elements. }
      intros ? ?.  induction l; simpl. (* "probably" *)
      - intros X HX. setoid_rewrite elem_of_nil in HX.
        pose proof H6 as [[?H _ _] _ _].
        epose proof (@equiv_empty _ _ _ _ _ _ H8 X ltac:(set_solver)).
        now apply leibniz_equiv_iff in H9 as ->.
      - pose proof (NoDup_cons_1_1 _ _ H7). apply NoDup_cons_1_2 in H7.
        intros X HX. setoid_rewrite elem_of_cons in HX.
        epose proof (@elem_of_dec_slow _ _ _ _ _ _ _ _ _ _ H6).
        epose proof (@union_difference _ _ _ _ _ _ _ _ fin_set_set X0 {[a]} X ltac:(set_solver)).
        apply leibniz_equiv_iff in H9 as ->.
        apply Hadd; [set_solver|]. apply IHl; [auto | set_solver].
    Qed.

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

  End stdpp_but_for_set.

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
        insertUP P (f wf$ t, g wf$ u) ===> insertUP (insertUP P (f, g)) (t, u)
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

  Axiom injectivity : forall Γ f t g u, Γ ⊢ (f $ t) =ml (g $ u) ---> (f =ml g) and (t =ml u).

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
      pose proof (H P0 (f wf$ t) (g wf$ u)) as H0.
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

  (* Could I make US a Prop and use stdpp's rtc for this? *)
  Inductive USrtc {T : Set} {UPT : UP T} : T -> T -> Set :=
    | USrtc_last : forall a, USrtc a a
    | USrtc_step : forall a b c, a ===> b -> USrtc b c -> USrtc a c
  .

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
      opose proof* (patt_equal_comm t1 t2 Γ)...
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

  Section antiunification.
    Record AUP := mkAUP {
      patternAUP : Pattern;
      mappingsAUP : list (Pattern * Pattern);

      wfpPatternAUP : well_formed_positive patternAUP;
      wfcmaPatternAUP : well_formed_closed_mu_aux patternAUP 0;
      wfceaPatternAUP : well_formed_closed_ex_aux patternAUP (length mappingsAUP);
      (* wfMappingsAUP : wf (map (uncurry patt_and) mappingsAUP) *)
      wfFstMappingsAUP : wf (map fst mappingsAUP);
      wfSndMappingsAUP : wf (map snd mappingsAUP);
    }.

    (* Definition toPredicateAUP (aup : AUP) : Pattern := *)
    (*   match aup with *)
    (*   | {| patternAUP := p; mappingsAUP := m |} => (let '(_, exf, p1, p2) := foldr (fun '(u, v) '(n, exf, p1, p2) => (S n, exf ∘ patt_exists, (patt_bound_evar n =ml u) and p1, (patt_bound_evar n =ml v) and p2)) (0, id, Top, Top) m in exf (p and (p1 or p2))) *) 
    (*   end. *)

    Fixpoint existsN (n : nat) (p : Pattern) : Pattern :=
      match n with
      | 0 => p
      | S n => existsN n (ex, p)
      end.

    (* Definition toPredicateMappingAUP (f : (Pattern * Pattern) -> Pattern) (σ : list (Pattern * Pattern)) : Pattern := snd (foldr (fun p '(n, a) => (S n, patt_bound_evar n =ml (f p) and a)) (0, Top) σ). *)
    Definition toPredicateMappingAUP (f : (Pattern * Pattern) -> Pattern) (σ : list (Pattern * Pattern)) : Pattern := foldr (fun '(n, p) a => patt_bound_evar n =ml (f p) and a) Top (zip (seq 0 (length σ)) σ).

    Lemma wf_existsN n : forall φ, well_formed_positive φ -> well_formed_closed_mu_aux φ 0 -> well_formed_closed_ex_aux φ n -> well_formed (existsN n φ).
    Proof.
      induction n; intros; simpl.
      wf_auto2.
      apply IHn; wf_auto2.
    Defined.

    Lemma map_compose {A B C} (f : B -> C) (g : A -> B) (l : list A) : map (f ∘ g) l = map f (map g l).
    Proof.
      induction l; simpl; congruence.
    Defined.

    Lemma map_snd_zip {A B} (l : list A) : forall (l' : list B), length l' <= length l -> map snd (zip l l') = l'.
    Proof.
      induction l; intros; simpl.
      inversion H. now rewrite (nil_length_inv l').
      case_match; simpl.
      reflexivity.
      f_equal. apply IHl. simpl in H. now apply le_S_n in H.
    Defined.

    Goal forall σ, wf (map fst σ) -> wf (map snd σ) -> (let φ := toPredicateMappingAUP fst σ in well_formed_positive φ /\ well_formed_closed_mu_aux φ 0 /\ well_formed_closed_ex_aux φ (length σ)) /\ (let φ := toPredicateMappingAUP snd σ in well_formed_positive φ /\ well_formed_closed_mu_aux φ 0 /\ well_formed_closed_ex_aux φ (length σ)).
    Proof.
      (* intros. *)
      (* subst φ. unfold toPredicateMappingAUP. *)
      (* repeat split. *)
      (* apply foldr_ind with (Q := (fun '(a, b) => well_formed a /\ well_formed b) ∘ snd). *)
      (* wf_auto2. *)
      (* apply Forall_fold_right. rewrite <- foldr_map_thing, map_compose, map_snd_zip. *)
      (* induction σ. simpl. split. *)
      (* unfold wf, Pattern.wf in H, H0. simpl in H, H0 |- *. case_match. apply andb_prop in H as [], H0 as []. auto. *)
      (* rewrite seq_length. reflexivity. *)
      (* intros. case_match. simpl in H1. *)
      (* apply foldr_andb_equiv_foldr_conj in H, H0. *)
    Abort.

    (* Lemma foldr_ind' {A B} (P : B -> Prop) (t : A -> B) (f : B -> B -> B) (b : B) (l : list A) : P b -> Forall (P ∘ t) l -> (forall a b, P (t a) -> P b -> P (f (t a) b)) -> P (foldr (f ∘ t) b l). *)
    (* Proof. *)
    (*   intros. *)
    (*   induction l; simpl; inversion H0; auto. *)
    (* Defined. *)

    Definition toPredicateAUP : AUP -> WFPattern.
    Proof.
      intros [p m wfp wfcma wfcea wffm wfsm].
      exists (existsN (length m) (p and (toPredicateMappingAUP fst m or toPredicateMappingAUP snd m))).
      apply wf_existsN.
      opose proof* (foldr_ind well_formed_positive (well_formed ∘ fst ∘ snd) (fun '(n, p) a => patt_bound_evar n =ml (fst p) and a) Top (zip (seq 0 (length m)) m)).
      wf_auto2.
      unfold wf, Pattern.wf in wffm.
      apply Forall_fold_right. apply foldr_andb_equiv_foldr_conj.
      rewrite <- foldr_map_thing, map_compose, map_snd_zip, map_compose. auto.
      rewrite seq_length. reflexivity.
      (* opose proof* (wf_foldr (fun '(n, p) a => patt_bound_evar n =ml (fst p) and a) (fst ∘ snd) Top (zip (seq 0 (length m)) m)). *)
      (* wf_auto2. *)
      (* rewrite -> map_compose, map_snd_zip. auto. *)
      (* rewrite seq_length. reflexivity. *)
      intros. case_match. wf_auto2.
      match goal with [H : ?x |- _ ] => assert x end.
      generalize m. generalize (@fst Pattern Pattern).
      simpl in H. unfold toPredicateMappingAUP.


      (* induction m; unfold toPredicateMappingAUP; simpl. *)
      (* wf_auto2. *)
      (* do 2 case_match. *)
      (* Search well_formed_closed_ex_aux. *)
      (* simpl. apply well_formed_impl_well_formed_ex. *)


      (* unshelve epose proof (foldr _ (0, @id Pattern, Top, Top) m) as [[[_ exf] p1] p2]. *)
      (* intros [u v] [[[n exf] p1] p2]. *)
      (* exact (S n, exf ∘ patt_exists, (patt_bound_evar n =ml u) and p1, (patt_bound_evar n =ml v) and p2). *)
      (* (1* apply foldr with (A := (nat * (Pattern -> Pattern) * Pattern * Pattern)%type) in m as [[[_ exf] p1] p2]. *1) *)
      (* exists (exf (p and (p1 or p2))). *)
    (* Defined. *)
      Admitted.

    (* Inductive Plotkin : AUP -> AUP -> Prop := *)
    (*   | decompositionP t m1 m2 f x y : Plotkin (mkAUP t (m1 ++ (f $ x, f $ y) : m2) _ _ _) (mkAUP (t^{length m1↦f}) (m1 ++ (x, y) : m2) _ _ _). *)

    (* Lemma wfToPredicateAUP : forall aup, well_formed (toPredicateAUP aup). *)
    (* Proof. *)
    (*   intros []. simpl. *)
    (*   induction mappingsAUP0. *)
    (*   simpl. wf_auto2. *)
    (*   destruct a. simpl in IHmappingsAUP0 |- *. *)
    (* Abort. *)
  End antiunification.

  (*
  Section antiunification.
    Definition biWFP := (WFPattern * WFPattern)%type.
    Definition triWFP := (WFPattern * WFPattern * WFPattern)%type.

    Class AUP T `{ElemOf triWFP T, Empty T, Singleton triWFP T, Union T, Elements triWFP T} := {
      semiAUP :: SemiSet triWFP T;
      patternAUP : WFPattern;
      setAUP : T
    }.

    Definition triset_split `{Elements triWFP T, Singleton biWFP T', Empty T', Union T'} : T -> (T' * T')%type.
    Proof.
      intros.
      split; apply (@set_map _ _ H _ _ _ _ _); try assumption;
      intros [[a b] c].
      exact (a, b).
      exact (a, c).
    Defined.

    Definition predicate_biset `{Elements biWFP T} : T -> WFPattern.
    Proof.
      eintros X%set_fold.
      exact X.
      intros x%(uncurry WFPatt_equal).
      exact (WFPatt_and x).
      exists Top. exact well_formed_top.
    Defined.

    From stdpp Require Import listset.

    Definition predicateAUP `{AUP T} : T -> WFPattern.
    Proof.
      intros X.
      About listset_elements.
      assert (EqDecision biWFP) by (apply prod_eqdec; apply sigma_eqdec; try apply Pattern_eqdec; intros; apply eq_eqdec).
      pose proof (@triset_split _ _ (listset biWFP) _ _ _ X) as [Φσ₁%predicate_biset Φσ₂%predicate_biset].
    Abort.

  End antiunification.
   *)

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
    let t1 := ((f wf$ x) wf$ (g wf$ one)) wf$ (g wf$ z) in
    let t2 := ((f wf$ (g wf$ y)) wf$ (g wf$ y)) wf$ (g wf$ (g wf$ x)) in
    (* (all, all, all, ex, patt_app (patt_app (patt_app (patt_sym f') b3) b2) b1 =ml b0) ∈ Γ -> *)
    (* (all, all, ex, patt_app (patt_app (patt_sym g') b3) b2 =ml b0) ∈ Γ -> *)
    {σ & Γ ⊢ `t1 and `t2 <---> `t1 and predicate_list σ}.
  Proof with try solve [auto | refine_wf; auto; apply wfWFPattern].
    intros * NE1 NE2 HΓ **.
    evar (σ : list (evar * Pattern)).
    assert (wf (map snd σ)) as WFσ by shelve.
    pose proof (wf_predicate_list σ WFσ) as WFplσ.
    exists σ.
    toMLGoal... mlSplitAnd; mlIntro.
    opose proof* (Prop₃_right Γ (`t1) (`t2))...
    (* How do I solve these? *)
    (* toMLGoal. admit. apply hypothesis in FF. use AnyReasoning in FF. mlAdd FF. *)
    (* Print bevar_subst. *)
    (* About forall_functional_subst. *)
    1-2: admit.
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
    rewrite (union_comm_L {[(z, g wf$ x)]}). rewrite <- union_assoc_L.
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
    (* TODO: make issue *)
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
    Unshelve.
    wf_auto2.
    all: typeclasses eauto.
  Abort.

End unification.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.

