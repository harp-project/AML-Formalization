From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import String Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Export Logic ProofMode.MLPM.
From MatchingLogic.Theories Require Export Definedness_Syntax Definedness_ProofSystem Sorts_Syntax FOEquality_ProofSystem.
From MatchingLogic.Utils Require Export stdpp_ext.

Require Export MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.
Import FreshnessManager.
Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Require Import MatchingLogic.Theories.DeductionTheorem.

Require MatchingLogic.Theories.Sorts_Syntax.
Export MatchingLogic.Theories.Sorts_Syntax.Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

Set Printing All.

Ltac solve_sfresh :=
  (eapply not_elem_of_larger_impl_not_elem_of;
  [|apply X_eq_fresh_impl_X_notin_free_svars; reflexivity];
  simpl; clear; set_solver) +
  by (unfold svar_is_fresh_in;
  eapply svar_is_fresh_in_richer'; [|apply set_svar_fresh_is_fresh'];
  clear; set_solver).


(*  eq-elim.0 $e #Substitution ph2 ph4 ph0 x $.   => ph2 = ph4[ph0/x]
    eq-elim.1 $e #Substitution ph3 ph4 ph1 x $.   => ph3 = ph4[ph1/x]
    eq-elim $a |- ( \imp ( \eq ph0 ph1 ) ( \imp ph2 ph3 ) ) $.
                                                  => ph0 = ph1 -> ph2 -> ph3
 *)
Lemma equality_elimination_basic 
  {Σ : Signature}
  {sy : Definedness_Syntax.Syntax}
  Γ φ1 φ2 C (* x (xs : EVarSet) X i *)
  (HΓ : theory ⊆ Γ)
  (WF1 : well_formed φ1)
  (WF2 :  well_formed φ2)
  (WFC : PC_wf C)
  (Hmu : pattern_kt_well_formed (pcPattern C))
  (* (Hmu : bound_svar_is_banned_under_mus (pcPattern C) 0 0) *)
(*   (Hfree : {[ev_x; x]} ∪ free_evars φ1 ∪ free_evars φ2 ∪ free_evars (pcPattern C) ## xs)
  (Hfree2 : x ∉ free_evars φ1 ∪ free_evars φ2 ∪ free_evars (pcPattern C))
  (* (Hfree3 : x ∉ free_svars ) *)
  (Henough : size xs >= maximal_exists_depth_to 0 (pcEvar C) (pcPattern C)):
(*   mu_free (pcPattern C) -> *)
  ProofInfoLe (ExGen := {[ev_x; x]} ∪ coGset.gset_to_coGset xs,
         SVSubst := {[X]},
         KT := false,
         AKT := false) i -> *) :
  Γ ⊢i (φ1 =ml φ2) --->
    (emplace C φ1) ---> (emplace C φ2)
  using AnyReasoning.
Proof.
  destruct C as [y φ4]. cbn in *.
  assert (well_formed φ4) by wf_auto2. clear WFC.
  remember (size' φ4) as sz.
  assert (size' φ4 <= sz) by lia. clear Heqsz.
  revert φ4 φ1 φ2 (* xs x X *) Γ HΓ H0 H WF1 WF2 Hmu (* Hfree Hfree2 Henough *). induction sz; intros.
  {
    destruct φ4; simpl in H0; lia.
  }
  destruct φ4; simpl in *.
  * case_match.
    - subst.
      mlIntro "H".
      (* ExGen : {[ev_x; x]} is needed for this: *)
      mlApplyMeta total_phi_impl_phi in "H".
      (***)
      mlDestructAnd "H".
      mlAssumption.
      2: assumption.
      1: instantiate (1 := fresh_evar (φ1 ---> φ2)); solve_fresh.
    - do 2 mlIntro. mlAssumption.
  * do 2 mlIntro. mlAssumption.
  * do 2 mlIntro. mlAssumption.
  * do 2 mlIntro. mlAssumption.
  * do 2 mlIntro. mlAssumption.
  * mlIntro "H".
    epose proof (IH1 := IHsz φ4_1 φ1 φ2 (* xs x X *) Γ HΓ ltac:(lia) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(by destruct_and!) (*_ ltac:(set_solver) ltac:(lia) H1 *)).
    epose proof (IH2 := IHsz φ4_2 φ1 φ2 (* xs x X *) Γ HΓ ltac:(lia) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(by destruct_and!) (* _ ltac:(set_solver) ltac:(lia) H1 *)).
    clear IHsz.
    mlAssert ("H2" : (φ1 =ml φ2)). wf_auto2. mlAssumption.
    eapply framing_left_under_tot_impl with (x := fresh_evar ((φ1 <---> φ2) ---> φ4_2^[[evar:y↦φ2]])) in IH1.
    eapply framing_right_under_tot_impl with (x := fresh_evar ((φ1 <---> φ2) ---> φ4_1^[[evar:y↦φ1]])) in IH2.
    mlApplyMeta IH1 in "H".
    mlApplyMeta IH2 in "H2".
    mlIntro "H0".
    mlApply "H".
    mlApply "H2".
    mlAssumption.
    6, 13: solve_fresh.
    6, 12: try_solve_pile.
    all: try assumption; wf_auto2.
  * do 2 mlIntro. mlAssumption.
  * mlIntro "H".
    epose proof (IH1 := IHsz φ4_1 φ2 φ1 (* xs x X *) Γ HΓ ltac:(lia) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(by destruct_and!)(* _ ltac:(set_solver) ltac:(lia) H1 *)).
    epose proof (IH2 := IHsz φ4_2 φ1 φ2 (* xs x X *) Γ HΓ ltac:(lia) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(by destruct_and!)(* _ ltac:(set_solver) ltac:(lia) H1 *)).
    clear IHsz.
    mlAssert ("H2" : (φ2 =ml φ1)). wf_auto2.
    {
      mlApplyMeta patt_equal_sym. mlAssumption. assumption.
    }
    mlApplyMeta IH1 in "H2".
    mlApplyMeta IH2 in "H".
    mlIntro "H0". mlIntro "S".
    clear. mlApply "H". mlApply "H0". mlApply "H2". mlAssumption.
  * mlIntro.
    mlIntro.
    destruct (decide (y ∈ free_evars φ4)).
    2: {
      rewrite free_evar_subst_no_occurrence. assumption.
      rewrite free_evar_subst_no_occurrence. assumption.
      mlAssumption.
    }

    (* TODO
       manually applied mlDestructEx, because it does not automatically solve the
       side conditions, thus fails *)
    mlFreshEvar as z.
    _mlReshapeHypsByName "1".
    eapply MLGoal_destructEx with z. apply pile_any.

    1: ltac2:(_fm_export_everything()); cbn; set_solver.
    1: ltac2:(_fm_export_everything()); cbn; set_solver.
    1: ltac2:(_fm_export_everything()); cbn; pose proof free_evars_free_evar_subst; set_solver.
    1: ltac2:(_fm_export_everything()); cbn; pose proof free_evars_free_evar_subst; set_solver.
    (* *** *)
    simpl. mlExists z.
    opose proof* (IHsz (evar_open z 0 φ4) φ1 φ2 (* (list_to_set l) x X *) Γ HΓ).
    2-4: wf_auto2.
    1: rewrite evar_open_size'; lia.
    1: by apply kt_well_formed_evar_open.
    rewrite evar_open_free_evar_subst_swap. fm_solve. wf_auto2.
    rewrite evar_open_free_evar_subst_swap. fm_solve. wf_auto2.
    mlApplyMeta H1. mlSplitAnd; mlAssumption.
  * do 2 mlIntro.
    mlConj "0" "1" as "H". mlClear "0". mlClear "1".
    opose proof* (mu_and_predicate_propagation Γ (φ4^[[evar:y↦φ1]]) (φ1 =ml φ2) HΓ
      ltac:(wf_auto2) ltac:(wf_auto2)).
    {
      destruct_and!.
      apply bound_svar_is_banned_under_mus_fevar_subst_alternative.
      * wf_auto2.
      * apply bsvar_occur_false_impl_banned.
        apply wfc_mu_aux_implies_not_bsvar_occur. wf_auto2.
      * assumption.
    }
    {
      remember (fresh_evar (φ1 ---> φ2)) as x.
      remember (fresh_evar (φ1 ---> φ2 ---> patt_free_evar x)) as z.
      remember (fresh_evar (φ1 ---> φ2 ---> patt_free_evar x --->
                patt_free_evar z)) as w.
      eapply floor_is_predicate with (x := x) (y := z) (z := w); try eassumption.
      wf_auto2.
      1-3: subst; simpl; solve_fresh.
      try_solve_pile.
    }
    apply pf_iff_proj2 in H1. 2-3: wf_auto2.
    2-5: try apply wfc_impl_no_pos_occ; try apply wfc_impl_no_neg_occ; wf_auto2.
    mlApplyMeta H1 in "H".
    remember (fresh_svar (φ1 ---> φ2 ---> φ4 ---> patt_free_evar y)) as X.
    fromMLGoal.
    replace ((mu , φ1 =ml φ2 and φ4^[[evar:y↦φ1]]) ---> (mu , φ4^[[evar:y↦φ2]]))
      with
      ((mu , (φ1 =ml φ2 and φ4^[[evar:y↦φ1]])^{svar:0↦X}^{{svar:X↦0}}) ---> (mu , φ4^[[evar:y↦φ2]]^{svar:0↦X}^{{svar:X↦0}})).
    (* TODO: solve_sfresh seems to not work well here *)
    2: {
      mlSimpl.
      rewrite !svar_quantify_svar_open.
      1-8: try wf_auto2.
      1-2: solve_sfresh.
      1-2: pose proof free_svars_free_evar_subst.
      1-2: eapply not_elem_of_larger_impl_not_elem_of;
  [|apply X_eq_fresh_impl_X_notin_free_svars; reflexivity];
      cbn; set_solver.
      reflexivity.
    }

    aapply mu_monotone.
    {
      apply svar_hno_bsvar_subst.
      * intros. cbn in H2. congruence.
      * intros. clear-H WF1 WF2. wf_auto2.
        all: try apply wfc_impl_no_pos_occ; try apply wfc_impl_no_neg_occ; wf_auto2.
      * apply fresh_svar_no_neg. unfold svar_is_fresh_in.
        subst X.
        pose proof free_svars_free_evar_subst.
        eapply not_elem_of_larger_impl_not_elem_of;
  [|apply X_eq_fresh_impl_X_notin_free_svars; reflexivity];
      cbn; set_solver.
    }
    {
      apply svar_hno_bsvar_subst.
      * intros. cbn in H2. congruence.
      * intros. clear-H WF1 WF2. wf_auto2.
        all: try apply wfc_impl_no_pos_occ; try apply wfc_impl_no_neg_occ; wf_auto2.
      * apply fresh_svar_no_neg. unfold svar_is_fresh_in.
        subst X.
        pose proof free_svars_free_evar_subst.
        eapply not_elem_of_larger_impl_not_elem_of;
  [|apply X_eq_fresh_impl_X_notin_free_svars; reflexivity];
      cbn; set_solver.
    }
    mlSimpl.
    rewrite svar_open_not_occur. wf_auto2.
    rewrite svar_open_not_occur. wf_auto2.
    unfold svar_open.
    rewrite -free_evar_subst_bsvar_subst. wf_auto2. unfold evar_is_fresh_in; set_solver.
    rewrite -free_evar_subst_bsvar_subst. wf_auto2. unfold evar_is_fresh_in; set_solver.
    mlIntro. mlDestructAnd "0".
    fromMLGoal.
    apply IHsz.
    - assumption.
    - rewrite svar_open_size'. lia.
    - wf_auto2.
    - wf_auto2.
    - wf_auto2.
    - destruct_and!.
      apply kt_well_formed_svar_open; wf_auto2.
Defined.


Local Lemma simplTest
  {Σ : Signature}
  {syntax : Sorts_Syntax.Syntax}
  (Γ : Theory)
  (φ ψ τ: Pattern)
  (s : symbols) x:
  well_formed (ex , φ) ->
  well_formed ψ ->
  well_formed τ ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢ ((all ψ , φ) ---> ex ψ ,  φ)^[[evar:x↦τ]].
Proof.
  intros. mlSimpl. mlSortedSimpl. mlSortedSimpl. mlSimpl.
  remember (fresh_evar (ψ $ φ $ τ)) as y.
  mlIntro.
  mlSpecialize "0" with x.
  mlExists x.
Abort.

Lemma ex_sort_impl_ex
  {Σ : Signature}
  {syntax : Sorts_Syntax.Syntax}
  (Γ : Theory)
  (ϕ : Pattern)
  (s : symbols)
  :
  well_formed (ex , ϕ) ->
  Definedness_Syntax.theory ⊆ Γ ->
  Γ ⊢ (ex (patt_sym s) , ϕ) ---> (ex , ϕ).
Proof.
  intros wfϕ HΓ.

  unfold "ex _ , _".

  unfold nest_ex; simpl.

  remember (fresh_evar (b0 ∈ml 〚 patt_sym s 〛 and ϕ)) as x.
  rewrite <- evar_quantify_evar_open with (n := 0) (x := x) (phi := b0 ∈ml 〚 patt_sym s 〛 and ϕ).
  2: {
    subst x. eapply evar_is_fresh_in_richer'.
    2: apply set_evar_fresh_is_fresh'.
    clear. set_solver.
  }
  2: {
    wf_auto2.
  }

  gapply BasicProofSystemLemmas.Ex_gen.
  { apply pile_any. }
  { apply pile_any. }
  {
    subst x. eapply evar_is_fresh_in_richer'.
    2: { apply set_evar_fresh_is_fresh'. }
    clear. set_solver.
  }

  mlSimpl. unfold evar_open. simpl.

  toMLGoal.
  { wf_auto2. }
  mlIntro "H".
  mlDestructAnd "H" as "H0" "H1".
  mlClear "H0".

  mlApplyMeta BasicProofSystemLemmas.Ex_quan. simpl.
  mlExact "H1".
Defined.

Theorem top_includes_everything {Σ : Signature} {syntax : Sorts_Syntax.Syntax}:
  ∀ (Γ : Theory) (x : evar),
  Definedness_Syntax.theory ⊆ Γ -> 
  Γ ⊢i patt_free_evar x  ∈ml patt_top using AnyReasoning.
Proof.
  intros.
  pose proof proved_membership_functional Γ (patt_top) (patt_free_evar x) ltac:(set_solver) ltac:(wf_auto2) ltac:(wf_auto2).
  mlApplyMeta H0.
  * unfold  is_functional.
    mlExists x.
    mlSimpl. cbn.
    mlReflexivity.
  * pose proof top_holds Γ.
    use AnyReasoning in H1.
    mlExactMeta H1.
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.