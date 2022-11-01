(*
  This file contains admits for some cases of well formedness.
  Those cases are indeed well formed and could be reasoned about by hand.
  However, time is better spent by making wf_auto2 be able to fix them.
*)

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

From stdpp Require Import base fin_sets sets propset proof_irrel option list coGset finite infinite gmap.

From MatchingLogic Require Import BasicProofSystemLemmas
                                  Logic
                                  DerivedOperators_Syntax
                                  ProofMode.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.
Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.

Set Default Proof Mode "Classic".

Import Notations.

Open Scope ml_scope.
Open Scope string_scope.
Open Scope list_scope.

(* TODO: These 3 lemmas are used only here as is, but maybe it should be somewhere else? *)
Local Lemma impl_ctx_impl {Σ : Signature} Γ ctx ϕ ψ i :
  well_formed ϕ ->
  well_formed ψ ->
  well_formed (pcPattern ctx) ->
  ProofInfoLe AnyReasoning i ->
  Γ ⊢i ϕ ---> ψ using i ->
  (is_positive_context ctx ->
  Γ ⊢i (emplace ctx ϕ) ---> (emplace ctx ψ) using i)
  *
  (is_negative_context ctx ->
  Γ ⊢i (emplace ctx ψ) ---> (emplace ctx ϕ) using i).
Proof.
  intros wfϕ wfψ wfc pile H.

  remember (size' (pcPattern ctx)) as sz.
  assert (Hsz: size' (pcPattern ctx) <= sz) by lia.
  clear Heqsz.

  unfold emplace.

  destruct ctx as [cvar cpatt].
  simpl in *.

  generalize dependent cpatt.

  induction sz.
  {
    destruct cpatt; simpl in *; lia.
  }

  intros cpatt wfc Hsz.

  split.
  {
    intro Hp.
    destruct cpatt; simpl in *.

    (* trivial cases *)
    2,5,7: aapply A_impl_A;[eapply pile_trans;[|apply pile];try_solve_pile;try_solve_pile|wf_auto2].
    (* not well formed cases*)
    2,3: cbv in wfc; discriminate wfc.

    + destruct decide.
      { assumption. }
      { gapply A_impl_A. eapply pile_trans;[|apply pile]; try_solve_pile. wf_auto2. }

    + pose proof (IH1 := IHsz cpatt1).
      feed specialize IH1.
      { wf_auto2. }
      { lia. }
      destruct IH1 as [IH1 _]. feed specialize IH1.
      {
        clear -Hp. unfold is_positive_context in *. simpl in *.
        unfold evar_has_negative_occurrence in Hp.
        simpl in Hp. fold evar_has_negative_occurrence in Hp.
        rewrite negb_or in Hp. destruct_and! Hp.
        assumption.
      }
      pose proof (IH2 := IHsz cpatt2).
      feed specialize IH2.
      { wf_auto2. }
      { lia. }
      destruct IH2 as [IH2 _]. feed specialize IH2.
      {
        clear -Hp. unfold is_positive_context in *. simpl in *.
        unfold evar_has_negative_occurrence in Hp.
        simpl in Hp. fold evar_has_negative_occurrence in Hp.
        rewrite negb_or in Hp. destruct_and! Hp.
        assumption.
      }

      eapply syllogism_meta.
      4: {
        unshelve(eapply Framing_left;[|apply IH1]).
        { wf_auto2. }
        { eapply pile_trans;[|apply pile]. apply pile_any. }
      }
      { wf_auto2. }
      { wf_auto2. }
      { wf_auto2. }
      
      unshelve(eapply Framing_right).
      { wf_auto2. }
      { eapply pile_trans;[|apply pile]. apply pile_any. }
      apply IH2.

    + unfold is_positive_context in Hp. simpl in Hp.
      unfold evar_has_negative_occurrence in Hp. simpl in Hp.
      fold evar_has_positive_occurrence evar_has_negative_occurrence in Hp.
      rewrite negb_orb in Hp.
      destruct_and! Hp.

      pose proof (IH := IHsz (cpatt2)).
      feed specialize IH.
      { wf_auto2. }
      { lia. }
      destruct IH as [IH _]. feed specialize IH.
      {
        unfold is_positive_context. simpl. assumption.
      }

      toMLGoal.
      { wf_auto2. }
      mlAdd IH as "IH". clear IH.
      mlIntro "H".
      mlIntro "Hc".
      mlApply "IH". mlClear "IH".
      mlApply "H". mlClear "H".
      fromMLGoal.

      pose proof (IH := IHsz cpatt1).
      feed specialize IH.
      { wf_auto2. }
      { lia. }
      destruct IH as [_ IH]. feed specialize IH.
      { unfold is_negative_context. simpl. assumption. }
      assumption.

    + remember (evar_fresh_s ({[cvar]} ∪ free_evars cpatt ∪ free_evars ψ ∪ free_evars ϕ)) as x.
      pose proof (IH := IHsz (evar_open x 0 cpatt)).
      feed specialize IH.
      { wf_auto2. }
      { rewrite evar_open_size'. lia. }
      destruct IH as [IH _]. feed specialize IH.
      {
        clear -Hp Heqx. unfold is_positive_context in *. simpl in *.
        unfold evar_has_negative_occurrence in Hp.
        simpl in Hp. fold evar_has_negative_occurrence in Hp.
        rewrite <- neg_occurrence_bevar_subst.
        + assumption.
        + subst. solve_fresh_neq.
      }
      rewrite <- evar_quantify_evar_open with (n := 0) (phi := cpatt^[[evar:cvar↦ϕ]]) (x := x).
      rewrite <- evar_quantify_evar_open with (n := 0) (phi := cpatt^[[evar:cvar↦ψ]]) (x := x).
      apply ex_quan_monotone.
      { eapply pile_trans;[|apply pile]. try_solve_pile. }
      unfold evar_open.
      unfold evar_open in IH.

      rewrite free_evar_subst_free_evar_subst.
      { wf_auto2. }
      {
        apply count_evar_occurrences_0.
        subst; clear; simpl.
        rewrite not_elem_of_singleton.
        solve_fresh_neq.
      }

      rewrite free_evar_subst_free_evar_subst.
      { wf_auto2. }
      {
        apply count_evar_occurrences_0.
        subst; clear; simpl.
        rewrite not_elem_of_singleton.
        solve_fresh_neq.
      }

      assumption.

      {
        subst x; clear.
        eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        pose proof (Hfree := free_evars_free_evar_subst cpatt ψ cvar).
        set_solver.
      }
      { wf_auto2. }
      {
        subst x. 
        eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        pose proof (Hfree := free_evars_free_evar_subst cpatt ϕ cvar).
        clear -Hfree.
        set_solver.
      }
      { wf_auto2. }

    + remember (svar_fresh_s (free_svars cpatt ∪ free_svars ψ ∪ free_svars ϕ ∪ free_svars cpatt^[[evar:cvar↦ϕ]] ∪ free_svars cpatt^[[evar:cvar↦ψ]])) as X.
      pose proof (IH := IHsz (svar_open X 0 cpatt)).
      feed specialize IH.
      { wf_auto2. }
      { rewrite svar_open_size'. lia. }
      destruct IH as [IH _]. feed specialize IH.
      {
        clear -Hp. unfold is_positive_context in *. simpl in *.
        cbn in Hp.
        rewrite <- neg_occurrence_bsvar_subst.
        assumption.
      }
      rewrite <- svar_quantify_svar_open with (n := 0) (phi := cpatt^[[evar:cvar↦ϕ]]) (X := X).
      rewrite <- svar_quantify_svar_open with (n := 0) (phi := cpatt^[[evar:cvar↦ψ]]) (X := X).
      apply mu_monotone.
      { eapply pile_trans;[|apply pile]. try_solve_pile. }
      {
        unfold is_positive_context in Hp. simpl in Hp. 
        unfold well_formed in wfc. simpl in wfc.
        destruct_and! wfc.
        pose proof (Hneg := free_evar_subst_preserves_no_negative_occurrence cvar cpatt ϕ 0).
        feed specialize Hneg.
        { wf_auto2. }
        { assumption. }
        cbn in Hp.
        apply positive_negative_occurrence_db_named.
        { assumption. }
        apply fresh_svar_no_neg.
        subst.
        clear.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        set_solver.
      }
      {
        unfold is_positive_context in Hp. simpl in Hp. 
        unfold well_formed in wfc. simpl in wfc.
        destruct_and! wfc.
        pose proof (Hneg := free_evar_subst_preserves_no_negative_occurrence cvar cpatt ψ 0).
        feed specialize Hneg.
        { wf_auto2. }
        { assumption. }
        cbn in Hp.
        apply positive_negative_occurrence_db_named.
        { assumption. }
        apply fresh_svar_no_neg.
        subst.
        clear.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        set_solver.
      }
      unfold svar_open.
      unfold svar_open in IH.
      rewrite <- free_evar_subst_bsvar_subst.
      rewrite <- free_evar_subst_bsvar_subst.
      apply IH.
      { wf_auto2. }
      { unfold evar_is_fresh_in. set_solver. }
      { wf_auto2. }
      { unfold evar_is_fresh_in. set_solver. }
      {
        clear -HeqX.
        intro Hcontra.
        pose proof (Hfree := free_svars_free_evar_subst cpatt cvar ψ).
        assert (X ∉ free_svars cpatt /\ X ∉ free_svars ψ).
        {
          subst.
          split.
          {
            eapply svar_is_fresh_in_richer'.
            2: apply set_svar_fresh_is_fresh'.
            clear.
            set_solver.
          }
          {
            eapply svar_is_fresh_in_richer'.
            2: apply set_svar_fresh_is_fresh'.
            clear.
            set_solver.
          }
        }
        set_solver.
      }
      { wf_auto2. }
      {
        subst X.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        clear.
        set_solver.
      }
      { wf_auto2. }
  }
  {
    intro Hp.
    destruct cpatt; simpl in *.

    (* trivial cases *)
    2,5,7: aapply A_impl_A;[eapply pile_trans;[|apply pile];try_solve_pile;try_solve_pile|wf_auto2].
    (* not well formed cases*)
    2,3: cbv in wfc; discriminate wfc.

    + destruct decide.
      {
        subst.
        unfold is_negative_context in Hp. cbn in Hp.
        destruct decide in Hp; simpl in Hp; congruence.
      }
      { gapply A_impl_A. eapply pile_trans;[|apply pile]; try_solve_pile. wf_auto2. }

    + pose proof (IH1 := IHsz cpatt1).
      feed specialize IH1.
      { wf_auto2. }
      { lia. }
      destruct IH1 as [_ IH1]. feed specialize IH1.
      {
        clear -Hp. unfold is_negative_context in *. simpl in *.
        cbn in Hp.
        rewrite negb_or in Hp. destruct_and! Hp.
        assumption.
      }
      pose proof (IH2 := IHsz cpatt2).
      feed specialize IH2.
      { wf_auto2. }
      { lia. }
      destruct IH2 as [_ IH2]. feed specialize IH2.
      {
        clear -Hp. unfold is_negative_context in *. simpl in *.
        cbn in Hp.
        rewrite negb_or in Hp. destruct_and! Hp.
        assumption.
      }

      eapply syllogism_meta.
      4: {
        unshelve(eapply Framing_left;[|apply IH1]).
        { wf_auto2. }
        { eapply pile_trans;[|apply pile]. apply pile_any. }
      }
      { wf_auto2. }
      { wf_auto2. }
      { wf_auto2. }
      
      unshelve(eapply Framing_right).
      { wf_auto2. }
      { eapply pile_trans;[|apply pile]. apply pile_any. }
      apply IH2.

    + unfold is_negative_context in Hp. simpl in Hp.
      unfold evar_has_positive_occurrence in Hp. simpl in Hp.
      fold evar_has_positive_occurrence evar_has_negative_occurrence in Hp.
      rewrite negb_orb in Hp.
      destruct_and! Hp.

      pose proof (IH := IHsz (cpatt2)).
      feed specialize IH.
      { wf_auto2. }
      { lia. }
      destruct IH as [_ IH]. feed specialize IH.
      {
        unfold is_negative_context. simpl. assumption.
      }

      toMLGoal.
      { wf_auto2. }
      mlAdd IH as "IH". clear IH.
      mlIntro "H".
      mlIntro "Hc".
      mlApply "IH". mlClear "IH".
      mlApply "H". mlClear "H".
      fromMLGoal.

      pose proof (IH := IHsz cpatt1).
      feed specialize IH.
      { wf_auto2. }
      { lia. }
      destruct IH as [IH _]. feed specialize IH.
      { unfold is_positive_context. simpl. assumption. }
      assumption.

    + remember (evar_fresh_s ({[cvar]} ∪ free_evars cpatt ∪ free_evars ψ ∪ free_evars ϕ)) as x.
      pose proof (IH := IHsz (evar_open x 0 cpatt)).
      feed specialize IH.
      { wf_auto2. }
      { rewrite evar_open_size'. lia. }
      destruct IH as [_ IH]. feed specialize IH.
      {
        clear -Hp Heqx. unfold is_negative_context in *. simpl in *.
        cbn in Hp.
        rewrite <- pos_occurrence_bevar_subst.
        + assumption.
        + subst. solve_fresh_neq.
      }
      rewrite <- evar_quantify_evar_open with (n := 0) (phi := cpatt^[[evar:cvar↦ϕ]]) (x := x).
      rewrite <- evar_quantify_evar_open with (n := 0) (phi := cpatt^[[evar:cvar↦ψ]]) (x := x).
      apply ex_quan_monotone.
      { eapply pile_trans;[|apply pile]. try_solve_pile. }
      unfold evar_open.
      unfold evar_open in IH.

      rewrite free_evar_subst_free_evar_subst.
      { wf_auto2. }
      {
        apply count_evar_occurrences_0.
        subst; clear; simpl.
        rewrite not_elem_of_singleton.
        solve_fresh_neq.
      }

      rewrite free_evar_subst_free_evar_subst.
      { wf_auto2. }
      {
        apply count_evar_occurrences_0.
        subst; clear; simpl.
        rewrite not_elem_of_singleton.
        solve_fresh_neq.
      }

      assumption.

      {
        subst x; clear.
        eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        pose proof (Hfree := free_evars_free_evar_subst cpatt ψ cvar).
        set_solver.
      }
      { wf_auto2. }
      {
        subst x. 
        eapply evar_is_fresh_in_richer'.
        2: { apply set_evar_fresh_is_fresh'. }
        pose proof (Hfree := free_evars_free_evar_subst cpatt ϕ cvar).
        clear -Hfree.
        set_solver.
      }
      { wf_auto2. }

    + remember (svar_fresh_s (free_svars cpatt ∪ free_svars ψ ∪ free_svars ϕ ∪ free_svars cpatt^[[evar:cvar↦ϕ]] ∪ free_svars cpatt^[[evar:cvar↦ψ]])) as X.
      pose proof (IH := IHsz (svar_open X 0 cpatt)).
      feed specialize IH.
      { wf_auto2. }
      { rewrite svar_open_size'. lia. }
      destruct IH as [_ IH]. feed specialize IH.
      {
        clear -Hp. unfold is_negative_context in *. simpl in *.
        cbn in Hp.
        rewrite <- pos_occurrence_bsvar_subst.
        assumption.
      }
      rewrite <- svar_quantify_svar_open with (n := 0) (phi := cpatt^[[evar:cvar↦ϕ]]) (X := X).
      rewrite <- svar_quantify_svar_open with (n := 0) (phi := cpatt^[[evar:cvar↦ψ]]) (X := X).
      apply mu_monotone.
      { eapply pile_trans;[|apply pile]. try_solve_pile. }
      {
        unfold is_negative_context in Hp. simpl in Hp. 
        unfold well_formed in wfc. simpl in wfc.
        destruct_and! wfc.
        pose proof (Hneg := free_evar_subst_preserves_no_negative_occurrence cvar cpatt ψ 0).
        feed specialize Hneg.
        { wf_auto2. }
        { assumption. }
        cbn in Hp.
        apply positive_negative_occurrence_db_named.
        { assumption. }
        apply fresh_svar_no_neg.
        subst.
        clear.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        set_solver.
      }
      {
        unfold is_negative_context in Hp. simpl in Hp. 
        unfold well_formed in wfc. simpl in wfc.
        destruct_and! wfc.
        pose proof (Hneg := free_evar_subst_preserves_no_negative_occurrence cvar cpatt ϕ 0).
        feed specialize Hneg.
        { wf_auto2. }
        { assumption. }
        cbn in Hp.
        apply positive_negative_occurrence_db_named.
        { assumption. }
        apply fresh_svar_no_neg.
        subst.
        clear.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        set_solver.
      }
      unfold svar_open.
      unfold svar_open in IH.
      rewrite <- free_evar_subst_bsvar_subst.
      rewrite <- free_evar_subst_bsvar_subst.
      apply IH.
      { wf_auto2. }
      { unfold evar_is_fresh_in. set_solver. }
      { wf_auto2. }
      { unfold evar_is_fresh_in. set_solver. }
      {
        clear -HeqX.
        intro Hcontra.
        pose proof (Hfree := free_svars_free_evar_subst cpatt cvar ψ).
        assert (X ∉ free_svars cpatt /\ X ∉ free_svars ψ).
        {
          subst.
          split.
          {
            eapply svar_is_fresh_in_richer'.
            2: apply set_svar_fresh_is_fresh'.
            clear.
            set_solver.
          }
          {
            eapply svar_is_fresh_in_richer'.
            2: apply set_svar_fresh_is_fresh'.
            clear.
            set_solver.
          }
        }
        set_solver.
      }
      { wf_auto2. }
      {
        subst X.
        eapply svar_is_fresh_in_richer'.
        2: apply set_svar_fresh_is_fresh'.
        clear.
        set_solver.
      }
      { wf_auto2. }
  }
Defined.

Lemma impl_ctx_impl_pos {Σ : Signature} Γ ctx ϕ ψ i :
  well_formed ϕ ->
  well_formed ψ ->
  well_formed (pcPattern ctx) ->
  is_positive_context ctx ->
  ProofInfoLe AnyReasoning i ->
  Γ ⊢i ϕ ---> ψ using i ->
  Γ ⊢i (emplace ctx ϕ) ---> (emplace ctx ψ) using i.
Proof.
  intros wfϕ wfψ wfc Hp pile H.
  pose proof (impl := impl_ctx_impl Γ ctx ϕ ψ i wfϕ wfψ wfc pile H).
  destruct impl as [impl _].
  apply impl in Hp.
  assumption.
Defined.

Lemma impl_ctx_impl_neg {Σ : Signature} Γ ctx ϕ ψ i :
  well_formed ϕ ->
  well_formed ψ ->
  well_formed (pcPattern ctx) ->
  is_negative_context ctx ->
  ProofInfoLe AnyReasoning i ->
  Γ ⊢i ϕ ---> ψ using i ->
  Γ ⊢i (emplace ctx ψ) ---> (emplace ctx ϕ) using i.
Proof.
  intros wfϕ wfψ wfc Hn pile H.
  pose proof (impl := impl_ctx_impl Γ ctx ϕ ψ i wfϕ wfψ wfc pile H).
  destruct impl as [_ impl].
  apply impl in Hn.
  assumption.
Defined.

(* TODO:
  This lemma is lemma 88 in in the matching mu logic paper.
  As is there is no way to determine the mu requirement and
  propagation of predicates is unproved.
*)
Lemma pred_and_ctx_and {Σ : Signature} {syntax : Syntax} Γ ctx ϕ ψ i :
  well_formed ϕ ->
  well_formed ψ ->
  well_formed (pcPattern ctx) ->
  Γ ⊢i is_predicate_pattern ψ using i ->
  Γ ⊢i ψ and (emplace ctx ϕ) <---> ψ and (emplace ctx (ψ and ϕ)) using (ExGen := ∅, SVSubst := ∅, KT := false, FP := ∅).
Proof.
  intros wfm wfψ wfc Hp.

  remember (size' (pcPattern ctx)) as sz.
  assert (Hsz: size' (pcPattern ctx) <= sz) by lia.
  clear Heqsz.

  unfold emplace.

  destruct ctx as [cvar cpatt].
  simpl in *.

  generalize dependent cpatt.

  induction sz.
  {
    destruct cpatt; simpl in *; lia.
  }

  intros cpatt wfc Hsz.
  destruct cpatt. all: simpl in *.

  (* trivial cases *)
  2,5,7: apply pf_iff_split;[wf_auto2|wf_auto2|aapply A_impl_A;[try_solve_pile|wf_auto2]|aapply A_impl_A;[try_solve_pile|wf_auto2] ].
  (* not well formed cases*)
  2,3: cbv in wfc; discriminate wfc.

  + destruct decide.
    {
      apply pf_iff_split; wf_auto2.
      toMLGoal. wf_auto2. mlIntro. mlDestructAnd "0". mlSplitAnd.
      { mlExact "1". }
      {
        mlSplitAnd.
        * mlExact "1".
        * mlExact "2".
      }
      toMLGoal. wf_auto2. mlIntro. mlDestructAnd "0". mlDestructAnd "2". mlSplitAnd.
      * mlExact "1".
      * mlExact "3".
    }
    { apply pf_iff_split;[wf_auto2|wf_auto2|aapply A_impl_A|aapply A_impl_A];wf_auto2. }
  + pose proof (IH1 := IHsz cpatt1).
    feed specialize IH1.
    { wf_auto2. }
    { lia. }
    pose proof (IH2 := IHsz cpatt2).
    feed specialize IH2.
    { wf_auto2. }
    { lia. }

    remember_constraint as pi.
    assert (H : forall a b c, (Γ ⊢i a and b <---> a and c using pi) = (Γ ⊢i b <---> c using pi)).
    {
      intros.
      admit.
    }
    clear H.

    toMLGoal.
    { wf_auto2. }
    admit.
  + pose proof (IH1 := IHsz cpatt1).
    feed specialize IH1.
    { wf_auto2. }
    { lia. }
    pose proof (IH2 := IHsz cpatt2).
    feed specialize IH2.
    { wf_auto2. }
    { lia. }
    admit.
  + pose proof (IH := IHsz (ex , cpatt)).
    feed specialize IH.
    { wf_auto2. }
    { simpl. admit. }
    admit.
  + pose proof (IH := IHsz (mu , cpatt)).
    feed specialize IH.
    { wf_auto2. }
    { simpl. admit. }
    assumption.
Admitted.

Lemma mu_and_predicate_propagation {Σ : Signature} {syntax : Syntax} i Γ ϕ ψ X :
  well_formed (mu, ϕ) ->
  well_formed ψ ->
  svar_is_fresh_in X ϕ ->
  svar_is_fresh_in X ψ ->
  ProofInfoLe AnyReasoning i ->
  Γ ⊢i is_predicate_pattern ψ using i ->
  Γ ⊢i (mu, (ψ and ϕ)) <---> (ψ and (mu, ϕ)) using i.
Proof.
  intros wfm wfψ fϕ fψ pile Hp.

  apply pf_iff_split.
  { clear -wfm wfψ. wf_auto2. admit. }
  { wf_auto2. }
  
  (* Makes set_solver work later in the proof. *)
  unfold svar_is_fresh_in in fϕ, fψ.
  
  {
    toMLGoal.
    { wf_auto2. admit. }
    mlIntro "H".
    mlSplitAnd; fromMLGoal.
    {
      apply Knaster_tarski.
      { eapply pile_trans;[|apply pile]. try_solve_pile. }
      { wf_auto2. admit. }
      unfold instantiate.
      mlSimpl.
      rewrite -> well_formed_bsvar_subst with (k := 0).
      toMLGoal.
      { wf_auto2. }
      mlIntro.
      mlDestructAnd "0".
      mlExact "1".
      { lia. }
      { wf_auto2. }
    }
    {
      rewrite <- svar_quantify_svar_open with (n := 0) (phi := (ψ and ϕ)) (X := X).
      rewrite <- svar_quantify_svar_open with (n := 0) (phi := ϕ) (X := X) at 2.
      apply mu_monotone.
      { eapply pile_trans;[|apply pile]. try_solve_pile. }
      { wf_auto2. admit. }
      { wf_auto2. }
      {
        unfold svar_open.
        mlSimpl.
        gapply pf_conj_elim_r.
        { eapply pile_trans;[|apply pile]. try_solve_pile. }
        { wf_auto2. }
        { wf_auto2. }
      }
      { assumption. }
      { wf_auto2. }
      { set_solver. }
      { wf_auto2. }
    }
  }
  
  {
    toMLGoal.
    { wf_auto2. admit. }
    mlRewrite (useBasicReasoning i (@patt_and_comm Σ Γ ψ (mu , ϕ) wfψ wfm)) at 1.
    2: { eapply pile_trans;[|apply pile]. try_solve_pile. }
    fromMLGoal.
    apply lhs_from_and.
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. admit. }

    apply Knaster_tarski.
    { eapply pile_trans;[|apply pile]. try_solve_pile. }
    { wf_auto2. }

    apply lhs_to_and.
    { wf_auto2. admit. }
    { wf_auto2. }
    { wf_auto2. admit. }
    
    toMLGoal.
    { wf_auto2. admit. admit. }
    assert (Htmp : is_true (well_formed (mu , ϕ) ^ [ψ ---> (mu , ψ and ϕ)])).
    {
      wf_auto2. admit.
    }
    mlRewrite (useBasicReasoning i (@patt_and_comm Σ Γ ((mu , ϕ) ^ [ψ ---> (mu , ψ and ϕ)]) ψ Htmp wfψ)) at 1.
    2: { eapply pile_trans;[|apply pile]. try_solve_pile. }
    
    mlIntro "H".
    mlApplyMeta Pre_fixp.
    2: { wf_auto2. admit. }
    unfold instantiate.
    mlSimpl.
    fromMLGoal.
    rewrite -> well_formed_bsvar_subst with (φ := ψ) (k := 0).
    2: auto.
    2: wf_auto2.

    remember (evar_fresh_s (free_evars ϕ)) as x.
    pose proof (H := pred_and_ctx_and Γ
      {|
        pcEvar := x;
        pcPattern := ϕ^[svar:0↦patt_free_evar x];
      |}
      (ψ ---> (mu , ψ and ϕ)) ψ i).
    unfold emplace in H. simpl in H.
    feed specialize H.
    { wf_auto2. admit. }
    { wf_auto2. }
    { wf_auto2. }
    { assumption. }

    toMLGoal.
    { wf_auto2. admit. }
    rewrite subst_svar_evar_svar in H.
    { apply count_evar_occurrences_0. subst. apply set_evar_fresh_is_fresh'. }
    rewrite subst_svar_evar_svar in H.
    { apply count_evar_occurrences_0. subst. apply set_evar_fresh_is_fresh'. }
    clear Htmp.
    unshelve(epose proof (Htmp := @liftPi _ _ _ _ i _ H)).
    { eapply pile_trans;[|apply pile]. apply pile_any. }
    mlRewrite Htmp at 1.
    2: { eapply pile_trans;[|apply pile]. apply pile_any. }

    clear Heqx x H Htmp.

    remember (evar_fresh_s (free_evars ϕ)) as x.
    pose proof (H := impl_ctx_impl_pos Γ
      {|
        pcEvar := x;
        pcPattern := ϕ^[svar:0↦patt_free_evar x];
      |}
      (ψ and (ψ ---> (mu , ψ and ϕ)))
      (mu , ψ and ϕ)
      i
      ).
    unfold emplace in H. simpl in H.
    feed specialize H.
    { wf_auto2. admit. }
    { wf_auto2. admit. }
    { wf_auto2. }
    { unfold is_positive_context. cbn.
      unfold well_formed in wfm.
      cbn in wfm.
      destruct_and! wfm. clear -H2 Heqx.
      apply no_neg_svar_subst.
      { subst. eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh. set_solver. }
      { assumption. }
    }
    { eapply pile_trans;[|apply pile]. try_solve_pile. }
    toMLGoal.
    { wf_auto2. admit. admit. }
    { mlIntro "H". mlDestructAnd "H". mlApply "1". mlExact "0". }

    rewrite subst_svar_evar_svar in H.
    {
      apply count_evar_occurrences_0. subst. apply set_evar_fresh_is_fresh'.
    }
    
    rewrite subst_svar_evar_svar in H.
    {
      apply count_evar_occurrences_0. subst. apply set_evar_fresh_is_fresh'.
    }

    mlIntro "H".
    mlDestructAnd "H" as "H0" "H1".
    mlSplitAnd.
    + mlExact "H0".
    + mlApplyMeta H. mlExact "H1".
  }
Admitted. (* TODO: This lemma is awaiting for wf_auto2 to be smart enough for (mu , ϕ and ψ ) *)

Theorem deduction_theorem {Σ : Signature} {syntax : Syntax} Γ ϕ ψ
  (gpi : ProofInfo)
  (pf : Γ ∪ {[ ψ ]} ⊢i ϕ using gpi) :
  well_formed ϕ ->
  well_formed ψ ->
  theory ⊆ Γ ->
  pi_generalized_evars gpi ## (gset_to_coGset (free_evars ψ)) ->
  pi_substituted_svars gpi ## (gset_to_coGset (free_svars ψ)) ->
  Γ ⊢i ⌊ ψ ⌋ ---> ϕ
  using AnyReasoning.
Proof.
  intros wfϕ wfψ HΓ HnoExGen HnoSvarSubst.
  destruct pf as [pf Hpf]. simpl.
  induction pf.
  - (* hypothesis *)
    rename axiom into axiom0.
    (* We could use [apply elem_of_union in e; destruct e], but that would be analyzing Prop
        when building Set, which is prohibited. *)
    destruct (decide (axiom0 = ψ)).
    + subst.
      eapply useGenericReasoning.
      2: {
        apply total_phi_impl_phi; assumption.
      }
      {
        apply pile_evs_svs_kt.
        {
          clear. set_solver.
        }
        {
          clear. set_solver.
        }
        { reflexivity. }
        { clear. set_solver. }
      }

    + assert (axiom0 ∈ Γ).
      { clear -e n. set_solver. }
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      eapply useGenericReasoning.
      2: apply (BasicProofSystemLemmas.hypothesis Γ axiom0 i H).
      apply pile_evs_svs_kt.
      {
        set_solver.
      }
      {
        set_solver.
      }
      {
        simpl. reflexivity.
      }
      { clear. set_solver. }
  - (* P1 *)
    toMLGoal.
    { wf_auto2. }
    do 3 mlIntro. mlExactn 1.
  - (* P2 *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0". fromMLGoal.
    useBasicReasoning.
    apply P2; assumption.
  - (* P3 *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0". fromMLGoal.
    useBasicReasoning.
    apply P3; assumption.
  - (* Modus Ponens *)
    assert (well_formed phi2).
    { unfold well_formed, well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto.
    }
    assert (well_formed phi1).
    {
      clear -pf1. apply proved_impl_wf in pf1. exact pf1.
    }

    remember_constraint as i'.

    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    simpl in Hpf2, Hpf3, Hpf4.
    feed specialize IHpf1.
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { unfold implb in *.
        destruct (uses_kt pf1) eqn:Hktpf1;[|reflexivity]. simpl in *.
        exact Hpf4.
      }
      { clear -pwi_pf_fp. set_solver. }
    }
    { assumption. }
    feed specialize IHpf2.
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { unfold implb in *.
        destruct (uses_kt pf2) eqn:Hktpf2;[|reflexivity].
        rewrite orb_comm in Hpf4. simpl in *.
        exact Hpf4.
      }
      {
        clear -pwi_pf_fp. set_solver.
      }
    }
    { wf_auto2. }
    
    (*
    (* simplify the constraint *)
    unfold dt_exgen_from_fp. simpl.
    rewrite map_app.
    rewrite list_to_set_app_L.
    simpl.
    *)

    (*
    (* weaken the induction hypotheses so that their constraint
        matches the constraint of the goal *)
    apply useGenericReasoning with (i := i') in IHpf1.
    2: {
      subst i'.
      apply pile_evs_svs_kt.
      { clear. set_solver. }
      { clear. set_solver. }
      { reflexivity. }
    }

    apply useGenericReasoning with (i := i') in IHpf2.
    2: {
      subst i'.
      apply pile_evs_svs_kt.
      { clear. set_solver. }
      { clear. set_solver. }
      { reflexivity. }
    }
    *)

    toMLGoal.
    { wf_auto2. }
    mlIntro.
    mlAdd IHpf2.
    mlAssert ((phi1 ---> phi2)).
    { wf_auto2. }
    { mlApply "1". mlExactn 1. }
    mlApply "2".
    mlAdd IHpf1.
    mlApply "3".
    mlExactn 2.
  - (* Existential Quantifier *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0". fromMLGoal.
    useBasicReasoning.
    apply Ex_quan. wf_auto2.
  - (* Existential Generalization *)
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    simpl in Hpf2, Hpf3, Hpf4.
    (*
    simpl in HnoExGen.
    case_match;[congruence|]. *)
    feed specialize IHpf.
    {
      constructor; simpl.
      { clear -Hpf2. set_solver. }
      { clear -Hpf3. set_solver. }
      { apply Hpf4. }
      { clear -pwi_pf_fp. set_solver. }
    }
    { clear pwi_pf_fp. wf_auto2. }

    apply reorder_meta in IHpf.
    2-4: clear pwi_pf_fp; wf_auto2.
    apply Ex_gen with (x := x) in IHpf.
    3: { simpl. set_solver. }
    2: { apply pile_evs_svs_kt.
      { clear -Hpf2. set_solver. }
      { set_solver. }
      { reflexivity. }
      { clear. set_solver. }
    }
    apply reorder_meta in IHpf.
    2-4: clear pwi_pf_fp; wf_auto2.
    exact IHpf.
    
  - (* Propagation of ⊥, left *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0". fromMLGoal.
    useBasicReasoning.
    apply Prop_bott_left; assumption.
  - (* Propagation of ⊥, right *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0"; auto. fromMLGoal.
    useBasicReasoning.
    apply Prop_bott_right; assumption.
  - (* Propagation of 'or', left *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0"; auto. fromMLGoal.
    useBasicReasoning.
    apply Prop_disj_left; assumption.
  - (* Propagation of 'or', right *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0"; auto. fromMLGoal.
    useBasicReasoning.
    apply Prop_disj_right; assumption.
  - (* Propagation of 'exists', left *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0"; auto. fromMLGoal.
    useBasicReasoning.
    apply Prop_ex_left; assumption.
  - (* Propagation of 'exists', right *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0"; auto. fromMLGoal.
    useBasicReasoning.
    apply Prop_ex_right; assumption.
  - (* Framing left *)
    assert (well_formed (phi1)).
    { unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto. }

    assert (well_formed (phi2)).
    { unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto. }

    assert (well_formed (psi)).
    { unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto. }
    
    assert (well_formed (phi1 ---> phi2)).
    { unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto. }
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    simpl in Hpf2,Hpf3,Hpf4.
    feed specialize IHpf.
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { apply Hpf4. }
      { clear -pwi_pf_fp. set_solver. }
    }
    { wf_auto2. }

    remember_constraint as i'.

    (*
    apply useGenericReasoning with (i0 := i') in IHpf.
    2: {
      subst i'.
      apply pile_evs_svs_kt.
      { clear. set_solver. }
      { apply reflexivity. }
      { reflexivity. }
    }
    *)
    assert (S2: Γ ⊢i phi1 ---> (phi2 or ⌈ ! ψ ⌉) using i').
    { toMLGoal.
      { clear pwi_pf_fp; wf_auto2. }
      mlAdd IHpf. mlIntro.
      mlAdd (useBasicReasoning i' (A_or_notA Γ (⌈ ! ψ ⌉) ltac:(clear pwi_pf_fp; wf_auto2))).
      mlDestructOr "0".
      - mlRight. mlExact "3".
      - mlLeft.
        mlApply "4". mlExact "1".
    }

    assert (S3: Γ ⊢i (⌈ ! ψ ⌉ $ psi) ---> ⌈ ! ψ ⌉ using i').
    {
      replace (⌈ ! ψ ⌉ $ psi)
        with (subst_ctx (ctx_app_l AC_patt_defined psi ltac:(assumption)) (! ψ))
        by reflexivity.
      subst i'.
      gapply in_context_impl_defined; auto.
      try_solve_pile.
    }

    assert (S4: Γ ⊢i (phi1 $ psi) ---> ((phi2 or ⌈ ! ψ ⌉) $ psi) using i').
    { 
      unshelve (eapply Framing_left).
      { wf_auto2. } 2: exact S2.
      subst i'. clear. try_solve_pile.
    }

    assert (S5: Γ ⊢i (phi1 $ psi) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) using i').
    {
      pose proof (Htmp := prf_prop_or_iff Γ (ctx_app_l box psi ltac:(assumption)) phi2 (⌈! ψ ⌉)).
      feed specialize Htmp.
      { clear pwi_pf_fp;wf_auto2. }
      { clear pwi_pf_fp;wf_auto2. }
      simpl in Htmp.
      apply pf_iff_proj1 in Htmp.
      3: clear pwi_pf_fp; wf_auto2.
      2: clear pwi_pf_fp; wf_auto2.
      subst i'.
      eapply syllogism_meta.
      5: {
        gapply Htmp.
        clear. try_solve_pile.
      }
      4: assumption.
      all: clear pwi_pf_fp; wf_auto2.
    }

    assert (S6: Γ ⊢i ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉)) using i').
    {
      toMLGoal.
      { clear pwi_pf_fp; wf_auto2. }
      mlIntro. mlAdd S3.
      (* TODO we need a tactic for adding  something with stronger constraint. *)
      mlAdd (useBasicReasoning i' (A_or_notA Γ (phi2 $ psi) ltac:(auto))).
      mlDestructOr "2".
      - mlLeft. mlExact "3".
      - mlRight. mlApply "1". mlApply "0". mlExactn 0.
    }

    assert (S7: Γ ⊢i (phi1 $ psi) ---> ((phi2 $ psi)  or ⌈ ! ψ ⌉) using i').
    {
      toMLGoal.
      { clear pwi_pf_fp; wf_auto2. }
      mlAdd S5. mlAdd S6. mlIntro.
      mlAssert (((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
      { clear pwi_pf_fp; wf_auto2. }
      { mlApply "0". mlExactn 2. }
      mlDestructOr "3".
      - mlLeft. mlExactn 3.
      - mlApply "1". mlRight. mlExactn 3.
    }

    toMLGoal.
    { clear pwi_pf_fp; wf_auto2. }
    do 2 mlIntro. mlAdd S7.
    mlAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
    { clear pwi_pf_fp; wf_auto2. }
    { mlApply "2". mlExactn 2. }
    mlDestructOr "3".
    + mlExactn 3.
    + mlAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
      { clear pwi_pf_fp; wf_auto2. }
      { mlApply "2". mlExactn 2. }
      mlAdd (useBasicReasoning i' (A_or_notA Γ (phi2 $ psi) ltac:(auto))).
      mlDestructOr "4".
      * mlExactn 0.
      * mlAdd (useBasicReasoning i' (bot_elim Γ (phi2 $ psi) ltac:(auto))).
        mlApply "4".
        mlApply "0".
        mlExactn 5.
  - (* Framing right *)
    assert (well_formed (phi1)).
    { unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto. }

    assert (well_formed (phi2)).
    { unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto. }

    assert (well_formed (psi)).
    { unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto. }

    assert (well_formed (phi1 ---> phi2)).
    { unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. split_and!; auto. }
    simpl in HnoExGen. simpl in HnoSvarSubst.

    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    simpl in Hpf2,Hpf3,Hpf4.
    feed specialize IHpf.
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { apply Hpf4. }
      { clear -pwi_pf_fp. set_solver. }
    }
    { wf_auto2. }


    remember_constraint as i'.

    (*
    apply useGenericReasoning with (i := i') in IHpf.
    2: {
      subst i'.
      apply pile_evs_svs_kt.
      { clear. set_solver. }
      { apply reflexivity. }
      { reflexivity. }
    }
    *)
    assert (S2: Γ ⊢i phi1 ---> (phi2 or ⌈ ! ψ ⌉) using i').
    { toMLGoal.
      { clear pwi_pf_fp; wf_auto2. }
      mlAdd IHpf. mlIntro.
      mlAdd (useBasicReasoning i' (A_or_notA Γ (⌈ ! ψ ⌉) ltac:(clear pwi_pf_fp;wf_auto2))).
      mlDestructOr "2".
      - mlRight. mlExactn 0.
      - mlLeft.
        mlAssert((phi1 ---> phi2)).
        { wf_auto2. }
        { mlApply "0". mlExactn 0. }
        mlApply "2". mlExactn 2.
    }

    assert (S3: Γ ⊢i (psi $ ⌈ ! ψ ⌉) ---> ⌈ ! ψ ⌉ using i').
    {
      replace (psi $ ⌈ ! ψ ⌉)
        with (subst_ctx (ctx_app_r psi AC_patt_defined ltac:(assumption)) (! ψ))
        by reflexivity.
        subst i'.
        gapply in_context_impl_defined; auto.
        try_solve_pile.
    }

    assert (S4: Γ ⊢i (psi $ phi1) ---> (psi $ (phi2 or ⌈ ! ψ ⌉)) using i').
    { 
      (* TODO: have a variant of apply which automatically solves all wf constraints.
        Like: unshelve (eapply H); try_wfauto
      *)
      unshelve (eapply Framing_right).
      { clear pwi_pf_fp; wf_auto2. }
      2: exact S2.
      subst i'. try_solve_pile.
    }

    assert (S5: Γ ⊢i (psi $ phi1) ---> ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) using i').
    {
      pose proof (Htmp := prf_prop_or_iff Γ (ctx_app_r psi box ltac:(assumption)) phi2 (⌈! ψ ⌉)).
      feed specialize Htmp.
      { clear pwi_pf_fp; wf_auto2. }
      { clear pwi_pf_fp; wf_auto2. }
      simpl in Htmp.
      apply pf_iff_proj1 in Htmp.
      2,3: clear pwi_pf_fp; wf_auto2.
      subst i'.
      eapply syllogism_meta.
      5: gapply Htmp; try_solve_pile.
      4: assumption.
      all: clear pwi_pf_fp; wf_auto2.
    }

    assert (S6: Γ ⊢i ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) ---> ((psi $ phi2) or (⌈ ! ψ ⌉)) using i').
    {
      toMLGoal.
      { clear pwi_pf_fp; wf_auto2. }
      mlIntro. mlAdd S3.
      mlAdd (useBasicReasoning i' (A_or_notA Γ (psi $ phi2) ltac:(auto))).
      mlDestructOr "2".
      - mlLeft. mlExactn 0.
      - mlRight. mlApply "1". mlApply "0". mlExactn 0.
    }

    assert (S7: Γ ⊢i (psi $ phi1) ---> ((psi $ phi2)  or ⌈ ! ψ ⌉) using i').
    {
      toMLGoal.
      { clear pwi_pf_fp; wf_auto2. }
      mlAdd S5. mlAdd S6. mlIntro.
      mlAssert (((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
      { clear pwi_pf_fp; wf_auto2. }
      { mlApply "0". mlExactn 2. }
      mlDestructOr "3".
      - mlLeft. mlExactn 3.
      - mlApply "1". mlRight. mlExactn 3.
    }

    toMLGoal.
    { clear pwi_pf_fp; wf_auto2. }
    do 2 mlIntro. mlAdd S7.
    mlAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
    { clear pwi_pf_fp; wf_auto2. }
    { mlApply "2". mlExactn 2. }
    mlDestructOr "3".
    + mlExactn 3.
    + mlAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
      { clear pwi_pf_fp; wf_auto2. }
      { mlApply "2". mlExactn 2. }
      mlAdd (useBasicReasoning i' (A_or_notA Γ (psi $ phi2) ltac:(auto))).
      mlDestructOr "4".
      * mlExactn 0.
      * mlAdd (useBasicReasoning i' (bot_elim Γ (psi $ phi2) ltac:(auto))).
        mlApply "4".
        mlApply "0".
        mlExactn 5.
  - (* Set variable substitution *)
    simpl in HnoExGen. simpl in HnoSvarSubst. simpl in IHpf.
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    simpl in Hpf2, Hpf3, Hpf4.
    feed specialize IHpf.
    {
      constructor; simpl.
      { exact Hpf2. }
      { clear -Hpf3. set_solver. }
      { exact Hpf4. }
      { clear -pwi_pf_fp. set_solver. }
    }
    {
      clear pwi_pf_fp; wf_auto2.
    }
    
    remember_constraint as i'.

    replace (⌊ ψ ⌋ ---> phi^[[svar: X ↦ psi]])
      with ((⌊ ψ ⌋ ---> phi)^[[svar: X ↦ psi]]).
    2: {  simpl.
        rewrite [ψ^[[svar: X ↦ psi]]]free_svar_subst_fresh.
        {
          clear -HnoSvarSubst Hpf3. unfold svar_is_fresh_in. set_solver.
        }
        reflexivity.
    }
    apply Svar_subst.
    3: {
      apply IHpf.
    }
    {
      subst i'.
      apply pile_evs_svs_kt.
      {
        clear. set_solver.
      }
      {
        clear -Hpf3. set_solver.
      }
      {
        reflexivity.
      }
      { clear. set_solver. }
    }
    { clear pwi_pf_fp; wf_auto2. }

  - (* Prefixpoint *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0". fromMLGoal.
    apply useBasicReasoning.
    apply Pre_fixp. wf_auto2.
  - (* Knaster-Tarski *)
    destruct Hpf as [Hpf2 Hpf3 Hpf4].
    apply lhs_to_and.
    1-3: clear Hpf2 Hpf3 Hpf4 pwi_pf_fp; wf_auto2.
    remember_constraint as pi.

    epose proof (Htmp := @mu_and_predicate_propagation _ _ pi Γ phi ⌊ ψ ⌋ _ _ _ _).
    feed specialize Htmp.
    { apply set_svar_fresh_is_fresh. }
    { subst pi. simpl. try_solve_pile. }
    { eapply (liftPi _ _ _ _ (@floor_is_predicate _ _ _ _ _ _)). }
    toMLGoal.
    { clear Hpf2 Hpf3 Hpf4 pwi_pf_fp; wf_auto2. }
    mlIntro.
    apply pf_iff_proj2 in Htmp.
    mlApplyMeta Htmp in "0". clear Htmp.
    fromMLGoal.
    apply Knaster_tarski.
    { subst pi. try_solve_pile. }
    1,3,4:clear Hpf2 Hpf3 Hpf4 pwi_pf_fp; wf_auto2.
    1: admit.

    unfold instantiate.
    mlSimpl.
    apply lhs_from_and.

    1-3:clear Hpf2 Hpf3 Hpf4 pwi_pf_fp; wf_auto2.
    
    rewrite -> well_formed_bsvar_subst with (k := 0).
    simpl in IHpf.
    apply IHpf.
    constructor; try assumption.
    {
      clear -Hpf4.
      destruct (uses_kt pf) eqn:H; rewrite H; simpl.
      2: reflexivity.
      simpl in Hpf4.
      assumption.
    }
    { clear -wfϕ; wf_auto2. }
    { lia. }
    { clear -wfψ; wf_auto2. } 


  - (* Existence *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0". fromMLGoal.
    apply useBasicReasoning.
    apply Existence.
  - (* Singleton *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0". fromMLGoal.
    apply useBasicReasoning.
    apply Singleton_ctx. wf_auto2.
Admitted.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.