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

Section ProofSystemTheorems.
  Context
    {Σ : Signature}
    {syntax : Syntax}.

  Lemma Prop₃_left: forall Γ φ φ',
      theory ⊆ Γ ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (φ and (φ' =ml φ)) ---> (φ and φ').
  Proof.
    intros Γ φ φ' SubTheory Wf1 Wf2.
    toMLGoal. wf_auto2.
    mlIntro "H0". mlDestructAnd "H0" as "H1" "H2".
    mlRewriteBy "H2" at 1. (*assumption. wf_auto2.
    {
      unfold mu_in_evar_path. cbn. rewrite decide_eq_same. cbn.
      rewrite !Nat.max_0_r.
      case_match;[reflexivity|].
      rewrite maximal_mu_depth_to_0 in H.
      2: { inversion H. }
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh.
      { clear. set_solver. }
    }*)
    mlSplitAnd; mlExact "H1".
  Defined.

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
    (* Why can we only mlApplyMetaRaw here, and not after mlRevert? *)
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

  Corollary delete : forall φ φ' Γ,
    well_formed φ -> well_formed φ'
  ->
    Γ ⊢ φ and φ' =ml φ' ---> φ
    .
  Proof.
    intros φ φ' Γ WF1 WF2.
    toMLGoal. wf_auto2.
    mlIntro "H0". mlDestructAnd "H0" as "H1" "H2". mlExact "H1".
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

  Theorem elimination : forall φ φ' x Γ, x ∉ free_evars φ ->
    theory ⊆ Γ -> mu_free φ ->
    well_formed_closed_ex_aux φ 1 ->
    well_formed_closed_mu_aux φ 0 ->
    well_formed φ' ->
    Γ ⊢ φ^[evar: 0 ↦ patt_free_evar x] and φ' =ml patt_free_evar x ---> 
        φ^[evar: 0 ↦ φ'] and φ' =ml patt_free_evar x
    .
  Proof.
    intros φ φ' x Γ NotIn HΓ MF WFp1 WFp2 WF2.
    assert (well_formed (φ^[evar:0↦φ'])) as WFF.
    { wf_auto2. now apply mu_free_wfp. }
    assert (well_formed (φ^[evar:0↦patt_free_evar x])) as WFFF. {
      wf_auto2. now apply mu_free_wfp. }
    toMLGoal. wf_auto2.
    mlIntro "H0". mlDestructAnd "H0" as "H1" "H2".
    mlSplitAnd.
    2: { mlExact "H2". }
    epose proof (equality_elimination_basic Γ φ' (patt_free_evar x)
            {|pcEvar := x; pcPattern := φ^[evar: 0 ↦ patt_free_evar x]|} 
            HΓ WF2 ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    cbn in H.
    assert (Hwfeaψ': well_formed_closed_ex_aux φ' 0 = true).
    {
      (* TODO this clear should not be necessary *)
      clear - WF2.
      wf_auto2.
    }
    pose proof (bound_to_free_variable_subst φ x 1 0 φ' ltac:(lia) ltac:(wf_auto2) WFp1 NotIn) as H0.
    unfold evar_open in H0. rewrite <- H0 in H. (* TODO: cast_proof? *)
    rewrite free_evar_subst_id in H.
    assert (Γ ⊢ φ^[evar:0↦φ'] <---> φ^[evar:0↦patt_free_evar x] --->
                φ^[evar:0↦patt_free_evar x] ---> φ^[evar:0↦φ'] ) as Hiff. {
      toMLGoal.
      { clear H. wf_auto2. }
      mlIntro "H1". unfold patt_iff. mlDestructAnd "H1" as "H2" "H3". mlExact "H3".
    }
    
    use AnyReasoning in H.
    epose proof (syllogism_meta _ _ _ H Hiff).
    (* TODO: mlApplyMetaRaw buggy?
             Tries to match the longest conclusion, not the shortest *)
    apply reorder_meta in H1.
    mlRevertLast. mlApplyMeta H1. mlExact "H1".
    Unshelve. all: wf_auto2.
    cbn. rewrite mu_free_bevar_subst; wf_auto2.
  Defined.

  (* Since this isn't very useful for multi version, maybe delete? *)
  Lemma Lemma₂_single : forall Γ φ x φ',
    theory ⊆ Γ -> well_formed φ -> mu_free φ -> well_formed φ' ->
    Γ ⊢ is_functional φ ->
    Γ ⊢ φ^[[evar: x ↦ φ']] and patt_free_evar x =ml φ' --->
    φ and patt_free_evar x =ml φ'.
  Proof.
    intros Γ φ x φ' HΓ wfφ mfφ wfφ' fpφ.
    pose proof (equality_elimination_basic Γ (patt_free_evar x) φ' {| pcEvar := x ; pcPattern := φ |} HΓ ltac:(wf_auto2) wfφ' ltac:(wf_auto2) mfφ).
    cbn in H.
    rewrite free_evar_subst_id in H.
    mlIntro "H".
    mlAdd H as "H0".
    mlDestructAnd "H" as "H1" "H2".
    mlAssert ("H3" : (φ <---> φ^[[evar:x↦φ']])). wf_auto2.
    mlApply "H0".
    mlExact "H2".
    mlSplitAnd.
    mlDestructAnd "H3" as "H4" "H5".
    mlRevert "H1".
    mlExact "H5".
    mlExact "H2".
  Defined.

  (* stdpp_ext *)
  Lemma fold_left_preserves_function {A : Type} (t : A -> Pattern) (P : Pattern -> Prop) (f : Pattern -> A -> Pattern) x xs :
    P x -> foldr (fun c a => P (t c) /\ a) True xs -> (forall a b, P a -> P (t b) -> P (f a b)) -> P (fold_left f xs x).
  Proof.
    intros px pxs ppf.
    revert x px.
    induction xs; intros.
    exact px.
    simpl in pxs.
    destruct pxs.
    apply IHxs.
    exact H0.
    apply ppf.
    exact px.
    exact H.
  Defined.

  Lemma foldr_preserves_function {A : Type} (t : A -> Pattern) (P : Pattern -> Prop) (f : A -> Pattern -> Pattern) x xs :
    P x -> foldr (fun c a => P (t c) /\ a) True xs -> (forall a b, P a -> P (t b) -> P (f b a)) -> P (foldr f x xs).
  Proof.
    intros px pxs ppf.
    revert x px.
    induction xs; intros.
    exact px.
    simpl in pxs.
    destruct pxs.
    simpl.
    apply ppf.
    apply IHxs.
    exact H0.
    exact px.
    exact H.
  Defined.

  Lemma foldr_preserves_function_set {A : Type} (t : A -> Pattern) (P : Pattern -> Set) (f : A -> Pattern -> Pattern) x xs :
    P x -> foldr (fun c a => (P (t c) * a)%type) True xs -> (forall a b, P a -> P (t b) -> P (f b a)) -> P (foldr f x xs).
  Proof.
    intros px pxs ppf.
    revert x px.
    induction xs; intros.
    exact px.
    simpl in pxs.
    destruct pxs.
    simpl.
    apply ppf.
    apply IHxs.
    exact f0.
    exact px.
    exact p.
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

  (* pattern.v *)
  Lemma wf_fold_left {A : Type} (f : Pattern -> A -> Pattern) (t : A -> Pattern) x xs :
    well_formed x ->
    wf (map t xs) ->
    (forall a b, well_formed a -> well_formed (t b) -> well_formed (f a b)) ->
    well_formed (fold_left f xs x).
  Proof.
    (* intros wfx wfxs wfpf. *)
    (* revert x wfx. *)
    (* induction xs; simpl. *)
    (* intro. exact id. *)
    (* intros. apply IHxs, wfpf; wf_auto2. *)
  (* Restart. *)
    intros wfx wfxs wfpf.
    pose proof (fold_left_preserves_function t well_formed f x xs wfx).
    simpl in H.
    ospecialize* H.
    apply foldr_andb_equiv_foldr_conj. unfold wf in wfxs. rewrite ! foldr_map_thing in wfxs. exact wfxs.
    exact wfpf.
    exact H.
  Defined.

  Lemma wf_foldr {A : Type} (f : A -> Pattern -> Pattern) (t : A -> Pattern) x xs :
    well_formed x ->
    wf (map t xs) ->
    (forall a b, well_formed a -> well_formed (t b) -> well_formed (f b a)) ->
    well_formed (foldr f x xs).
  Proof.
    (* intros wfx wfxs wfpf. *)
    (* revert x wfx. *)
    (* induction xs; simpl. *)
    (* intro. exact id. *)
    (* intros. apply wfpf; [apply IHxs |]; wf_auto2. *)
  (* Restart. *)
    intros wfx wfxs wfpf.
    pose proof (foldr_preserves_function t well_formed f x xs wfx).
    simpl in H.
    ospecialize* H.
    apply foldr_andb_equiv_foldr_conj.
    unfold wf in wfxs. rewrite ! foldr_map_thing in wfxs. exact wfxs.
    exact wfpf.
    exact H.
  Defined.

  Lemma mf_fold_left {A : Type} (f : Pattern -> A -> Pattern) (t : A -> Pattern) x xs :
    mu_free x ->
    foldr (fun c a => mu_free c && a) true (map t xs) ->
    (forall a b, mu_free a -> mu_free (t b) -> mu_free (f a b)) ->
    mu_free (fold_left f xs x).
  Proof.
    (* intros mfx mfxs mfpf. *)
    (* revert x mfx mfxs. *)
    (* induction xs; simpl. *)
    (* now intros. *)
    (* intros ? ? []%andb_prop. *)
    (* apply IHxs. apply mfpf. *)
    (* all: assumption. *)
  (* Restart. *)
    intros mfx mfxs mfpf.
    pose proof (fold_left_preserves_function t mu_free f x xs mfx).
    simpl in H.
    ospecialize* H.
    apply foldr_andb_equiv_foldr_conj. rewrite foldr_map_thing in mfxs. exact mfxs.
    exact mfpf.
    exact H.
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

  (* This might change to parallel substitution *)
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

  Lemma patt_free_evar_subst : forall x φ, (patt_free_evar x)^[[evar: x ↦ φ]] = φ.
  Proof.
    intros.
    simpl.
    case_match.
    reflexivity.
    contradiction.
  Defined.

  (* This is temporary *)
  (* Proofs will be merged later *)
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

  (* TODO highlight this in thesis *)
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

  Tactic Notation "mlSpecializeHyp" constr(f) "with" constr(x) := mlApply f in x; mlClear f; mlRename x into f.

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

  Theorem elimination_reverse : forall φ φ' x Γ, x ∉ free_evars φ ->
    theory ⊆ Γ -> mu_free φ ->
    well_formed_closed_ex_aux φ 1 ->
    well_formed_closed_mu_aux φ 0 ->
    well_formed φ' ->
    Γ ⊢ φ^[evar: 0 ↦ φ'] and φ' =ml patt_free_evar x --->
        φ^[evar: 0 ↦ patt_free_evar x] and φ' =ml patt_free_evar x
    .
  Proof.
    intros φ φ' x Γ NotIn HΓ MF WFp1 WFp2 WF2.
    assert (well_formed (φ^[evar:0↦φ'])) as WFF.
    { wf_auto2. now apply mu_free_wfp. }
    assert (well_formed (φ^[evar:0↦patt_free_evar x])) as WFFF. {
      wf_auto2. now apply mu_free_wfp. }
    toMLGoal. wf_auto2.
    mlIntro "H0".
    mlDestructAnd "H0" as "H1" "H2".
    mlSplitAnd.
    2: { mlAssumption. }
    epose proof (equality_elimination_basic Γ φ' (patt_free_evar x)
            {|pcEvar := x; pcPattern := φ^[evar: 0 ↦ patt_free_evar x]|} 
            HΓ WF2 ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
    cbn in H.
    pose proof (bound_to_free_variable_subst φ x 1 0 φ' ltac:(lia) ltac:(clear -WF2; wf_auto2) WFp1 NotIn) as H0.
    unfold evar_open in H0. rewrite <- H0 in H. (* TODO: cast_proof? *)
    rewrite free_evar_subst_id in H.
    assert (Γ ⊢ φ^[evar:0↦φ'] <---> φ^[evar:0↦patt_free_evar x] --->
                φ^[evar:0↦φ'] ---> φ^[evar:0↦patt_free_evar x] ) as Hiff. {
      toMLGoal.
      { clear H. wf_auto2. }
      mlIntro "H1". unfold patt_iff. mlDestructAnd "H1" as "H2" "H3". mlExact "H2".
    }
    use AnyReasoning in H.
    epose proof (syllogism_meta _ _ _ H Hiff).
    (* TODO: mlApplyMetaRaw buggy?
             Tries to match the longest conclusion, not the shortest *)
    apply reorder_meta in H1.
    mlRevertLast.
    mlApplyMeta H1.
    mlExact "H1".
    Unshelve. all: wf_auto2.
    cbn. rewrite mu_free_bevar_subst; wf_auto2.
  Defined.

  (**
     Should be a consequence of the injectivity axiom:

      f(x₁,...,xₙ) = f(x₁',...,xₙ') → x₁ = x₁' ∧ ... ∧ xₙ = xₙ'

     The question is, why can we assume this axiom?
  *)
  (* TODO move this definition to a more general place. *)
  Definition application_chain (φ : Pattern) (φs : list Pattern) : Pattern :=
    fold_left (fun Acc φ => patt_app Acc φ) φs φ.

  Theorem application_equal : forall φs ψ φ's Γ,
    length φs = length φ's ->
    well_formed ψ -> (* Forall well_formed φs -> Forall well_formed φ's *)
    (forall i, i < length φs -> well_formed (nth i φs ⊥)) ->
    (forall i, i < length φ's -> well_formed (nth i φ's ⊥))
  ->
    Γ ⊢ application_chain ψ φs =ml application_chain ψ φ's --->
         fold_right (fun '(x, y) Acc => Acc and x =ml y) Top (zip φs φ's)
    .
  Proof.
    induction φs;
    intros ψ φ's Γ Len WF WFs1 WFs2.
    * apply eq_sym, length_zero_iff_nil in Len. subst. cbn.
      toMLGoal. wf_auto2.
      mlIntro "H0". mlClear "H0". (* TODO: mlExact for meta theorems *)
      fromMLGoal. wf_auto2.
      useBasicReasoning.
      apply (top_holds Γ).
    * destruct φ's. simpl in Len. congruence.
      simpl in Len. inversion Len. clear Len.
      cbn.
      admit.
  Abort.

End ProofSystemTheorems.

Section UnificationProcedure.
  Context {Σ : Signature} {ΣS : Syntax}.

  Definition unification_problem : Set := option (list (Pattern * Pattern)).

  Definition is_free_evar_in (x t : Pattern) : bool :=
    match x with
    | patt_free_evar x => match decide (x ∈ free_evars t) with
                          | left  _ => false
                          | right _ => true
                          end
    | _                => false
    end.

  Definition in_solved_form (P : unification_problem) : bool := from_option (forallb (uncurry is_free_evar_in)) true P.


  (* fin_set gset gmap.v *)







  (* Fixpoint apps_r (C : Application_context) : bool :=
  match C with
   | box => true
   | ctx_app_l cc p => apps_r cc
   | ctx_app_r p cc => false
  end. *)

  (** Based on https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf *)
  Definition Unification_problem : Set := list (Pattern * Pattern) * 
                                          list (evar * Pattern).

  Fixpoint get_apps (p : Pattern) : option (symbols * list Pattern) :=
  match p with
  | patt_app p1 p2 =>
    match get_apps p1 with
    | Some (s, ps) => Some (s, ps ++ [p2])
    | None => None
    end
  | patt_sym s => Some (s, [])
  | _ => None
  end.

  Definition u_remove := remove (prod_eqdec Pattern_eqdec Pattern_eqdec).

  Definition subst_ziplist (x : evar) (p : Pattern) 
    : list (Pattern * Pattern) -> list (Pattern * Pattern) :=
    map (fun '(p1, p2) => ( p1^[[evar: x ↦ p]] , p2^[[evar: x ↦ p]] )).
  Definition subst_list (x : evar) (p : Pattern) 
    : list (evar * Pattern) -> list (evar * Pattern) :=
    map (fun '(y, p2) => ( y , p2^[[evar: x ↦ p]] )).

  Reserved Notation "u ===> u'" (at level 80).
  Inductive unify_step : Unification_problem -> option Unification_problem -> Set :=
  (* trivial/delete *)
  | u_trivial t U S U' :
    (U ++ (t, t)::U', S) ===> Some (U ++ U', S)
  (* decomposition *)
  | u_decompose U U' S t1 t2 f ps ps' :
    get_apps t1 = Some (f, ps) -> get_apps t2 = Some (f, ps') ->
    length ps = length ps'
   ->
    (U ++ (t1, t2)::U', S) ===> Some (zip ps ps' ++ U ++ U', S)
  (* symbol_clash *)
  | u_clash U U' S t1 t2 f g ps ps' :
    get_apps t1 = Some (f, ps) -> get_apps t2 = Some (g, ps') ->
    f <> g
   ->
    (U ++ (t1, t2)::U', S) ===> None
  (* orient *)
  | u_orient U U' S t x:
    (U ++ (t, patt_free_evar x)::U', S) ===> Some (U ++ (patt_free_evar x, t)::U', S)
  (* occurs check *)
  | u_check U U' S x t:
    x ∈ free_evars t ->
    patt_free_evar x <> t
   ->
    (U ++ (t, patt_free_evar x)::U', S) ===> None
  (* elimination *)
  | u_elim U U' S x t:
    x ∉ free_evars t
   ->
    (U ++ (patt_free_evar x, t)::U', S) ===> Some (subst_ziplist x t (U ++ U'), 
                                                   (x, t) :: subst_list x t S)
  where "u ===> u'" := (unify_step u u').

  Definition eq_pats := (fun '(p1, p2) => p1 =ml p2).
  Definition eq_vars := (fun '(x, p2) => patt_free_evar x =ml p2).

  Definition unification_to_pattern (u : Unification_problem) : Pattern :=
    match u with
    | (Us, Ss) => 
        foldr patt_and Top (map eq_pats Us)
        and
        foldr patt_and Top (map eq_vars Ss)
    end.
  Definition wf_unification (u : Unification_problem) :=
    wf (map fst u.1) && wf (map snd u.1) && wf (map snd u.2).

(*   Theorem foldr_equiv :
    forall l p l' p0, well_formed p -> well_formed (foldr patt_and p0 l) -> well_formed (foldr patt_and p0 l') ->
    forall Γ, Γ ⊢ foldr patt_and p0 (l ++ p::l') <---> foldr patt_and p0 (p::l ++ l').
  Proof.
    intros l. induction l; intros p l' p0 WFp WFl WFl' Γ.
    * simpl. useBasicReasoning. apply pf_iff_equiv_refl. wf_auto2.
    * simpl.
  Admitted. *)

  Theorem wf_unify_step :
    forall u u' : Unification_problem,
    u ===> Some u' ->
    wf_unification u ->
    wf_unification u'.
  Proof.
    intros u u' D. dependent induction D; intros WF.
    * 
  Admitted.

  Theorem wf_unify_pattern :
    forall u, wf_unification u -> well_formed (unification_to_pattern u).
  Proof.
  Admitted.

  Theorem foldr_last_element :
    forall Γ xs x y,
    well_formed x -> well_formed y -> wf xs ->
    Γ ⊢i foldr patt_and (x and y) xs <--->
    ((foldr patt_and y xs) and x) using AnyReasoning.
  Proof.
    induction xs; intros x y Wf1 Wf2 Wf3; simpl.
    * gapply patt_and_comm; auto. apply pile_any.
    * apply wf_tail' in Wf3 as Wf4.
      specialize (IHxs x y Wf1 Wf2 Wf4).
      unshelve(toMLGoal).
      {
        assert (well_formed a) by now apply andb_true_iff in Wf3.
        apply well_formed_and; apply well_formed_imp;
        repeat apply well_formed_and; auto;
        apply well_formed_foldr_and; wf_auto2.
      }
      mlSplitAnd; mlIntro "H"; mlDestructAnd "H" as "H0" "H1".
      - mlRevertLast. mlRewrite IHxs at 1. mlIntro "H1". mlDestructAnd "H1".
        mlSplitAnd; [mlSplitAnd;mlAssumption|mlAssumption].
      - mlRewrite IHxs at 1. mlDestructAnd "H0".
        mlSplitAnd; [mlAssumption|mlSplitAnd;mlAssumption].
    Unshelve.
  Admitted.

  Theorem unification_soundness :
    forall u u' : Unification_problem,
    u ===> Some u' ->
    wf_unification u ->
    forall Γ, theory ⊆ Γ -> Γ ⊢ unification_to_pattern u ---> unification_to_pattern u' .
  Proof.
    intros u u' D WF.
    assert (wf_unification u') as H.
    { eapply wf_unify_step; eassumption. }
    inversion D; intros Γ HΓ.
    * subst.
      (* TODO: why does toMyGoal simplify??? *)
      (* Opaque unification_to_pattern. *)
      with_strategy opaque [unification_to_pattern] toMLGoal.
      { apply well_formed_imp; apply wf_unify_pattern; auto. }
      (* Transparent unification_to_pattern. *)
      cbn.
      rewrite map_app. simpl map.

      mlIntro "H". mlDestructAnd "H" as "H0" "H1". mlSplitAnd. 2: mlExact "H1".
      mlClear "H1".
      replace (fix app (l m : list Pattern) {struct l} : list Pattern :=
         match l with
         | [] => m
         | a :: l1 => a :: app l1 m
         end) with (@app Pattern) by reflexivity.
      mlRevertLast.
      rewrite map_app.
      do 2 rewrite foldr_app.
      simpl.
      apply wf_unify_pattern in WF. cbn in WF.
      rewrite map_app in WF. rewrite foldr_app in WF.
      simpl in WF.
      remember (foldr patt_and Top (map eq_pats U')) as L1.
      remember (map eq_pats U) as L2.
      epose proof (@foldr_last_element Γ L2 (t =ml t) L1 _ _ _).
      mlRewrite H0 at 1.
      mlIntro "H". mlDestructAnd "H" as "H0" "H1". mlExact "H0".
    * subst. admit.
    * subst; simpl.
      with_strategy opaque [unification_to_pattern] toMLGoal.
      { apply well_formed_imp. admit. admit. }
      do 2 rewrite map_app. simpl map.
      do 2 rewrite foldr_app. simpl.
      remember (foldr patt_and Top (map eq_pats U')) as L1.
      remember (map eq_pats U) as L2.
      epose proof (@foldr_last_element Γ L2 (t =ml patt_free_evar x) L1 _ _ _).
      mlRewrite H0 at 1.
      epose proof (@foldr_last_element Γ L2 (patt_free_evar x =ml t) L1 _ _ _).
      mlRewrite H1 at 1.
      mlIntro "H". mlDestructAnd "H" as "H0" "H1". mlDestructAnd "H0" as "H0_1" "H0_2".
      mlSplitAnd. mlSplitAnd. 1, 3: mlAssumption.
      mlClear "H0_1". mlClear "H1".
      mlApplyMeta (@patt_equal_sym _ _ Γ t (patt_free_evar x) _ ltac:(wf_auto2) ltac:(wf_auto2)). mlExact "H0_2".
    * subst; simpl.
      with_strategy opaque [unification_to_pattern] toMLGoal.
      { apply well_formed_imp. admit. admit. }
      rewrite map_app. simpl map.
      rewrite foldr_app. simpl.
      mlIntro "H". mlDestructAnd "H" as "H0" "H1".
    Unshelve. all: admit.
  Abort.
























(* (*   Axiom f : symbols.
  Compute (get_apps (patt_sym f $ ⊥ $ ⊤ $ ⊥)). *)
  Fixpoint unify_step1 (u : Unification_problem) : option Unification_problem :=
  match u with
  | []           => Some []
  | (t1, t2)::xs =>
    match unify_step1 xs with
    | None => None
    | Some xs' =>
      match decide (t1 = t2) with
      | left _ => Some xs' (* delete *)
      | right _ =>
        match get_apps t1, get_apps t2 with
        | Some (s, ps), Some (s', ps') =>
          match decide (s = s') with
          | left _ => Some (xs' ++ zip ps ps') (* decomposition *)
          | right _ => None (* symbol clash *)
          end
        | _, _ => Some xs'
        end
      end
    end
  end. *)

  Definition is_free_evar (p : Pattern) : bool :=
  match p with
  | patt_free_evar _ => true
  | _ => false
  end.

  Definition swap_if {A : Type} (P : A -> bool) (p : A * A): A * A :=
  match p with
  | (p1, p2) =>
    match P p1, P p2 with
    | true, _ => (p1, p2)
    | _, true => (p2, p1)
    | _, _    => (p1, p2)
    end
  end.

  (* (* orient *)
  Definition unify_step2 (u : Unification_problem) : Unification_problem :=
     map (swap_if is_free_evar) u.

  (* occurs_check *)
  Fixpoint unify_step3 (u : Unification_problem) : option Unification_problem :=
  match u with
  | [] => Some []
  | (p1, p2)::xs =>
    match unify_step3 xs with
    | Some xs' =>
      match p1 with
      | patt_free_evar x =>
        match decide (x ∈ free_evars p2) with
        | left _ => None
        | right _ => Some ((p1, p2)::xs')
        end
      | _ => Some ((p1, p2)::xs')
      end
    | None => None
    end
  end.

  (* 1x elimination *)
  Fixpoint unify_step3 (u : Unification_problem) : Unification_problem :=
  match u with
  | [] => []
  | (patt_free_evar x, p2)::xs => 
  | (p1, p2)::xs => unify_step3 xs
  end. *)

End UnificationProcedure.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.
