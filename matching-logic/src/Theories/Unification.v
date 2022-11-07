From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import BasicProofSystemLemmas Logic ProofMode.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
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
      theory ⊆ Γ -> mu_free φ ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (φ and (φ' =ml φ)) ---> (φ and φ').
  Proof.
    intros Γ φ φ' SubTheory Mufree Wf1 Wf2.
    toMLGoal. wf_auto2.
    mlIntro "H0". mlDestructAnd "H0" as "H1" "H2".
    mlRewriteBy "H2" at 1. assumption. wf_auto2.
    mlSplitAnd; mlExact "H1".
  Defined.

  Lemma membership_imp_equal :
    forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ' ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ (ex , (φ =ml b0)) ->
      Γ ⊢ (ex , (φ' =ml b0)) ->
      Γ ⊢ (φ ∈ml φ') ---> (φ =ml φ') .
  Proof.
    intros Γ φ φ' HΓ Mufree Wf1 Wf2 Funφ Funφ'.
    unfold patt_in, patt_equal.
    toMLGoal. wf_auto2.

    (* TODO: proposal: functional_reasoning tactic, which replaces a pattern with a 
                       free variable *)
    epose proof (@forall_functional_subst _ _ (⌈ b0 and φ' ⌉ ---> ⌊ b0 <---> φ' ⌋) φ 
                    Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
    Unshelve.
    2: { cbn. case_match; auto. apply andb_true_iff in Wf2 as [_ Wf2].
         apply andb_true_iff in Wf2 as [_ Wf2].
         (* NOTE: using eapply breaks the proof *)
         apply well_formed_closed_ex_aux_ind with (ind_evar2 := 1)in Wf2.
         rewrite Wf2. auto. lia.
    } (* TODO: this should be auto... *)
    simpl in H.
    repeat rewrite bevar_subst_not_occur in H. wf_auto2. (* TODO: cast_proof? *)
    mlApplyMeta H. clear H.
    mlSplitAnd.
    2: fromMLGoal; assumption.

    epose proof (forall_functional_subst (all, (⌈ b0 and b1 ⌉ ---> ⌊ b0 <---> b1 ⌋)) φ'
                    Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) _ ltac:(wf_auto2)) as H.
    Unshelve.
    2: { cbn. do 2 case_match; auto; lia. }
    mlApplyMeta H. clear H.

    mlSplitAnd.
    2: fromMLGoal; assumption.
    remember (fresh_evar patt_bott) as x.
    remember (fresh_evar (patt_free_evar x)) as y.
    assert (x <> y) as XY.
    { intro. apply x_eq_fresh_impl_x_notin_free_evars in Heqy.
      subst. set_solver. } (* TODO: this should be auto... *)
    fromMLGoal.


   (* TODO: mlIntro for supporting 'all' *)

    pose proof (universal_generalization Γ (all , (⌈ b0 and patt_free_evar x ⌉ ---> ⌊ b0 <---> patt_free_evar x ⌋)) x AnyReasoning (pile_any _)) as H1.
    simpl in H1.
    rewrite decide_eq_same in H1.
    apply H1.
    { wf_auto2. }
    clear H1.
    pose proof (@universal_generalization _ Γ (⌈ (patt_free_evar y) and (patt_free_evar x) ⌉ ---> ⌊ (patt_free_evar y) <---> (patt_free_evar x) ⌋) y AnyReasoning (pile_any _)) as H1.
    simpl in H1.
    rewrite decide_eq_same in H1.
    destruct (decide (y = x)) eqn:Heqyx;[congruence|].
    apply H1.
    { wf_auto2. }
    clear H1.
    now apply overlapping_variables_equal.
  Defined.

  Lemma functional_pattern_defined :
    forall Γ φ, theory ⊆ Γ -> well_formed φ ->
       Γ ⊢ (ex , (φ =ml b0)) ---> ⌈ φ ⌉.
  Proof.
    intros Γ φ HΓ Wf.
    toMLGoal. wf_auto2.
    mlIntro "H0".
    mlApplyMetaRaw (forall_functional_subst ⌈ b0 ⌉ φ _ HΓ ltac:(wf_auto2)
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

  Lemma equal_imp_membership :
    forall Γ φ φ',
      theory ⊆ Γ -> mu_free φ' ->
      well_formed φ -> well_formed φ' ->
      Γ ⊢ ⌈ φ' ⌉  ->
      Γ ⊢ (φ =ml φ') ---> (φ ∈ml φ') .
  Proof.
    intros Γ φ φ' HΓ MF WF1 WF2 Def.
    toMLGoal. wf_auto2.
    mlIntro "H0".
    mlRewriteBy "H0" at 1; cbn; try_wfauto2; try assumption.
    { rewrite MF. reflexivity. }
      mlClear "H0". unfold patt_in.
      assert (Γ ⊢ ( φ' and φ' <---> φ') ) as H1.
      {
        toMLGoal. wf_auto2.
        mlSplitAnd; mlIntro "H1".
        - mlDestructAnd "H1" as "H2" "H3". mlExact "H3".
        - mlSplitAnd; mlExact "H1".
      }
      now mlRewrite H1 at 1.
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
    mlApplyMetaRaw (useAnyReasoning (bott_not_defined Γ)).
    fromMLGoal. wf_auto2.

    apply ceil_monotonic; auto.
    { apply pile_any. }
    { wf_auto2. }

    toMLGoal. wf_auto2.
    mlApplyMetaRaw (useAnyReasoning (not_not_intro Γ ((φ ∈ml φ' <---> φ =ml φ' ))
                    ltac:(wf_auto2))).
    mlSplitAnd; mlIntro.
    * mlApplyMeta membership_imp_equal; auto. mlExactn 0.
    * mlApplyMeta equal_imp_membership; auto. mlExactn 0.
      Unshelve.
      toMLGoal. wf_auto2.
      clear h. mlApplyMeta functional_pattern_defined; auto.
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
      mlApplyMetaRaw (useAnyReasoning (phi_impl_defined_phi Γ (φ and φ') HΓ ltac:(wf_auto2))).
      mlExact "H0".
    }
    replace (⌈ φ and φ' ⌉) with (φ ∈ml φ') by auto.
    mlDestructAnd "H0" as "H2" "H3". mlSplitAnd.
    * mlExact "H2".
    * mlApplyMeta membership_imp_equal; auto.
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

    apply useAnyReasoning in H.
    epose proof (syllogism_meta _ _ _ H Hiff).
    (* TODO: mlApplyMetaRaw buggy?
             Tries to match the longest conclusion, not the shortest *)
    apply reorder_meta in H1.
    mlRevertLast. mlApplyMetaRaw H1. mlExact "H1".
    Unshelve. all: wf_auto2.
    cbn. rewrite mu_free_bevar_subst; wf_auto2.
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
    apply useAnyReasoning in H.
    epose proof (syllogism_meta _ _ _ H Hiff).
    (* TODO: mlApplyMetaRaw buggy?
             Tries to match the longest conclusion, not the shortest *)
    apply reorder_meta in H1.
    mlRevertLast.
    mlApplyMetaRaw H1.
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
      mlApplyMetaRaw (@patt_eq_sym _ _ Γ t (patt_free_evar x) _ ltac:(wf_auto2) ltac:(wf_auto2)). mlExact "H0_2".
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
