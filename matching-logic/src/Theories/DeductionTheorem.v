From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Import Equations.Prop.Equations.

From Coq Require Import String Setoid Btauto.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From stdpp Require Import base fin_sets sets propset proof_irrel option list coGset finite infinite gmap.

From MatchingLogic Require Import
  Logic
  DerivedOperators_Syntax
  ProofMode.MLPM
  FreshnessManager
.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.
Import extralibrary.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.

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
      ospecialize* IH1.
      { wf_auto2. }
      { lia. }
      destruct IH1 as [IH1 _]. ospecialize* IH1.
      {
        clear -Hp. unfold is_positive_context in *. simpl in *.
        unfold evar_has_negative_occurrence in Hp.
        simpl in Hp. fold evar_has_negative_occurrence in Hp.
        rewrite negb_or in Hp. destruct_and! Hp.
        assumption.
      }
      pose proof (IH2 := IHsz cpatt2).
      ospecialize* IH2.
      { wf_auto2. }
      { lia. }
      destruct IH2 as [IH2 _]. ospecialize* IH2.
      {
        clear -Hp. unfold is_positive_context in *. simpl in *.
        unfold evar_has_negative_occurrence in Hp.
        simpl in Hp. fold evar_has_negative_occurrence in Hp.
        rewrite negb_or in Hp. destruct_and! Hp.
        assumption.
      }

      eapply syllogism_meta.
      4: {
        unshelve(eapply Framing_left;[| |apply IH1]).
        { wf_auto2. }
        { try_solve_pile. }
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
      ospecialize* IH.
      { wf_auto2. }
      { lia. }
      destruct IH as [IH _]. ospecialize* IH.
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
      ospecialize* IH.
      { wf_auto2. }
      { lia. }
      destruct IH as [_ IH]. ospecialize* IH.
      { unfold is_negative_context. simpl. assumption. }
      assumption.

    + remember (evar_fresh_s ({[cvar]} ∪ free_evars cpatt ∪ free_evars ψ ∪ free_evars ϕ)) as x.
      pose proof (IH := IHsz (evar_open x 0 cpatt)).
      ospecialize* IH.
      { wf_auto2. }
      { rewrite evar_open_size'. lia. }
      destruct IH as [IH _]. ospecialize* IH.
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

      rewrite free_evar_subst_bevar_subst_fresh.
      { wf_auto2. }
      { subst x. simpl.
        rewrite not_elem_of_singleton.
        solve_fresh_neq.
      }

      rewrite free_evar_subst_bevar_subst_fresh.
      { wf_auto2. }
      {
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
      ospecialize* IH.
      { wf_auto2. }
      { rewrite svar_open_size'. lia. }
      destruct IH as [IH _]. ospecialize* IH.
      {
        clear -Hp. unfold is_positive_context in *. simpl in *.
        cbn in Hp.
        rewrite <- neg_occurrence_bsvar_subst.
        assumption.
      }

      apply mu_monotone with (X := X).
      { eapply pile_trans;[|apply pile]. try_solve_pile. }
      {
        wf_auto2.
      }
      {
        wf_auto2.
      }
      {
        subst X. unfold svar_fresh_s.
        pose proof free_svars_free_evar_subst.
        pose proof set_svar_fresh_is_fresh' (free_svars cpatt ∪ free_svars ψ ∪ free_svars ϕ ∪ free_svars cpatt^[[evar:cvar↦ϕ]]
      ∪ free_svars cpatt^[[evar:cvar↦ψ]]).
        clear-H0 H1.
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
      ospecialize* IH1.
      { wf_auto2. }
      { lia. }
      destruct IH1 as [_ IH1]. ospecialize* IH1.
      {
        clear -Hp. unfold is_negative_context in *. simpl in *.
        cbn in Hp.
        rewrite negb_or in Hp. destruct_and! Hp.
        assumption.
      }
      pose proof (IH2 := IHsz cpatt2).
      ospecialize* IH2.
      { wf_auto2. }
      { lia. }
      destruct IH2 as [_ IH2]. ospecialize* IH2.
      {
        clear -Hp. unfold is_negative_context in *. simpl in *.
        cbn in Hp.
        rewrite negb_or in Hp. destruct_and! Hp.
        assumption.
      }

      eapply syllogism_meta.
      4: {
        unshelve(eapply Framing_left;[| |apply IH1]).
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
      ospecialize* IH.
      { wf_auto2. }
      { lia. }
      destruct IH as [_ IH]. ospecialize* IH.
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
      ospecialize* IH.
      { wf_auto2. }
      { lia. }
      destruct IH as [IH _]. ospecialize* IH.
      { unfold is_positive_context. simpl. assumption. }
      assumption.

    + remember (evar_fresh_s ({[cvar]} ∪ free_evars cpatt ∪ free_evars ψ ∪ free_evars ϕ)) as x.
      pose proof (IH := IHsz (evar_open x 0 cpatt)).
      ospecialize* IH.
      { wf_auto2. }
      { rewrite evar_open_size'. lia. }
      destruct IH as [_ IH]. ospecialize* IH.
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

      rewrite free_evar_subst_bevar_subst_fresh.
      { wf_auto2. }
      {
        rewrite not_elem_of_singleton.
        solve_fresh_neq.
      }

      rewrite free_evar_subst_bevar_subst_fresh.
      { wf_auto2. }
      {
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
      ospecialize* IH.
      { wf_auto2. }
      { rewrite svar_open_size'. lia. }
      destruct IH as [_ IH]. ospecialize* IH.
      {
        clear -Hp. unfold is_negative_context in *. simpl in *.
        cbn in Hp.
        rewrite <- pos_occurrence_bsvar_subst.
        assumption.
      }

      apply mu_monotone with (X := X).
      { eapply pile_trans;[|apply pile]. try_solve_pile. }
      { wf_auto2. }
      { wf_auto2. }
      {
        subst X. unfold svar_fresh_s.
        pose proof free_svars_free_evar_subst.
        pose proof set_svar_fresh_is_fresh' (free_svars cpatt ∪ free_svars ψ ∪ free_svars ϕ
          ∪ free_svars cpatt^[[evar:cvar↦ϕ]] ∪ free_svars cpatt^[[evar:cvar↦ψ]]).
        clear-H0 H1.
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

(* Lemma 88 in in the matching mu logic paper.*)
Lemma pred_and_ctx_and {Σ : Signature} {syntax : Syntax} Γ ctx ϕ ψ:
  Definedness_Syntax.theory ⊆ Γ ->
  well_formed ϕ ->
  well_formed ψ ->
  well_formed (pcPattern ctx) ->
  mu_in_evar_path (pcEvar ctx) (pcPattern ctx) 0 = false ->
  Γ ⊢ is_predicate_pattern ψ ->
  Γ ⊢ ψ and (emplace ctx ϕ) <---> ψ and (emplace ctx (ψ and ϕ)).
Proof.
  intros HΓ wfm wfψ wfc Hmf Hp.

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

  intros cpatt wfc Hmf Hsz.
  destruct cpatt. all: simpl in *.

  (* trivial cases *)
  2,5,7: useBasicReasoning; apply pf_iff_equiv_refl; wf_auto2.
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
    { apply pf_iff_split;[wf_auto2|wf_auto2|aapply A_impl_A|aapply A_impl_A];wf_auto2; set_solver. }
  + pose proof (IH1 := IHsz cpatt1).
    ospecialize* IH1.
    { wf_auto2. }
    {
      unfold mu_in_evar_path in *.
      simpl in Hmf.
      case_match. 
      2: { lia. }
      rewrite negb_false_iff.
      eapply (introT (Nat.eqb_spec 0 _)).
      lia.
    }
    {
      lia.
    }
    pose proof (IH2 := IHsz cpatt2).
    ospecialize* IH2.
    { wf_auto2. }
    {
      unfold mu_in_evar_path in *.
      simpl in Hmf.
      case_match. 
      2: { lia. }
      rewrite negb_false_iff.
      eapply (introT (Nat.eqb_spec 0 _)).
      lia.
    }
    { lia. }

    toMLGoal.
    { wf_auto2. }
    pose proof (Htmp := predicate_propagate_right_2_meta Γ
      (cpatt2^[[evar:cvar↦ϕ]])
      ψ
      (cpatt1^[[evar:cvar↦ϕ]])
      HΓ
      ltac:(wf_auto2)
      ltac:(wf_auto2)
      ltac:(wf_auto2)
      Hp
    ).
    mlRewrite Htmp at 1.
    clear Htmp.
    mlRewrite IH2 at 1.
    pose proof (Htmp := predicate_propagate_right_2_meta Γ
      (cpatt2^[[evar:cvar↦ψ and ϕ]])
      ψ
      (cpatt1^[[evar:cvar↦ϕ]])
      HΓ
      ltac:(wf_auto2)
      ltac:(wf_auto2)
      ltac:(wf_auto2)
      Hp
    ).
    mlRewrite <- Htmp at 1.
    clear Htmp.
    pose proof (Htmp := predicate_propagate_left_2_meta Γ
      (cpatt2^[[evar:cvar↦ψ and ϕ]])
      ψ
      (cpatt1^[[evar:cvar↦ϕ]])
      HΓ
      ltac:(wf_auto2)
      ltac:(wf_auto2)
      ltac:(wf_auto2)
      Hp
    ).
    mlRewrite Htmp at 1.
    clear Htmp.
    mlRewrite IH1 at 1.
    pose proof (Htmp := predicate_propagate_left_2_meta Γ
      (cpatt2^[[evar:cvar↦ψ and ϕ]])
      ψ
      (cpatt1^[[evar:cvar↦ψ and ϕ]])
      HΓ
      ltac:(wf_auto2)
      ltac:(wf_auto2)
      ltac:(wf_auto2)
      Hp
    ).
    mlRewrite <- Htmp at 1.
    fromMLGoal.
    useBasicReasoning.
    apply pf_iff_equiv_refl.
    wf_auto2.
  + pose proof (IH1 := IHsz cpatt1).
    ospecialize* IH1.
    { wf_auto2. }
    {
      unfold mu_in_evar_path in *.
      simpl in Hmf.
      case_match. 
      2: { lia. }
      rewrite negb_false_iff.
      eapply (introT (Nat.eqb_spec 0 _)).
      lia.
    }
    { lia. }
    pose proof (IH2 := IHsz cpatt2).
    ospecialize* IH2.
    { wf_auto2. }
    {
      unfold mu_in_evar_path in *.
      simpl in Hmf.
      case_match. 
      2: { lia. }
      rewrite negb_false_iff.
      eapply (introT (Nat.eqb_spec 0 _)).
      lia.
    }
    { lia. }
    toMLGoal.
    { wf_auto2. }
    mlSplitAnd.
    {
      mlIntro "H1".
      mlDestructAnd "H1" as "Hψ" "Himp".
      mlSplitAnd.
      { mlExact "Hψ". }
      mlAdd IH2 as "IH2".
      mlDestructAnd "IH2" as "IH21" "IH22".
      mlIntro "H".
      mlAssert ("Htmp": ((ψ and cpatt2^[[evar:cvar↦ψ and ϕ]]) ---> cpatt2^[[evar:cvar↦ψ and ϕ]])).
      { wf_auto2. }
      {
        mlIntro "H0".
        mlDestructAnd "H0" as "H00" "H01".
        mlExact "H01".
      }
      mlApply "Htmp".
      mlClear "Htmp".
      mlAdd IH1 as "IH1".
      mlDestructAnd "IH1" as "IH11" "IH12".
      mlApply "IH21".
      mlSplitAnd. mlExact "Hψ".
      mlApply "Himp".
      mlClear "Himp".
      mlAssert ("Htmp": ((ψ and cpatt1^[[evar:cvar↦ϕ]]) ---> cpatt1^[[evar:cvar↦ϕ]])).
      { wf_auto2. }
      {
        mlIntro "H0".
        mlDestructAnd "H0" as "H00" "H01".
        mlExact "H01".
      }
      mlApply "Htmp".
      mlClear "Htmp".
      mlApply "IH12".
      mlSplitAnd.
      { mlExact "Hψ". }
      { mlExact "H". }
    }
    {
      mlAdd IH1 as "IH1".
      mlAdd IH2 as "IH2".
      mlDestructAnd "IH1" as "IH11" "IH12".
      mlDestructAnd "IH2" as "IH21" "IH22".
      mlIntro "H1".
      mlDestructAnd "H1" as "Hψ" "H2".
      mlSplitAnd. mlExact "Hψ".
      mlIntro "H3".
      mlAssert ("IH11'": (ψ and cpatt1^[[evar:cvar↦ψ and ϕ]])).
      { wf_auto2. }
      {
        mlApply "IH11".
        mlSplitAnd.
        { mlExact "Hψ". }
        { mlExact "H3". }
      }
      mlClear "IH11".
      mlAssert ("H4": (ψ and cpatt2^[[evar:cvar↦ψ and ϕ]])).
      { wf_auto2. }
      {
        mlDestructAnd "IH11'" as "IH11'1" "IH11'2".
        mlSplitAnd. mlExact "Hψ".
        mlApply "H2".
        mlExact "IH11'2".
      }
      mlAssert ("IH22'": (ψ and cpatt2^[[evar:cvar↦ϕ]])).
      { wf_auto2. }
      {
        mlApply "IH22".
        mlExact "H4".
      }
      mlClear "IH22".
      mlDestructAnd "IH22'" as "IH22'1" "IH22'2".
      mlExact "IH22'2".
    }
  + 
    remember (cpatt^[[evar:cvar↦ϕ]]) as cpatt_1.
    remember (cpatt^[[evar:cvar↦ψ and ϕ]]) as cpatt_2.
    toMLGoal.
    { wf_auto2. }
    mlApplyMeta extract_common_from_equivalence_1.
    mlIntro "Hψ".
    (*remember (evar_fresh_s (free_evars (cpatt ---> ϕ ---> ψ) ∪ {[cvar]})) as x0.*)
    
    mlSplitAnd; mlIntro "H".
    {
      mlDestructEx "H" as x0.
      specialize (IHsz (cpatt^{evar:0↦x0})).
      ospecialize* IHsz.
      {
        wf_auto2.
      }
      {
        unfold mu_in_evar_path in *.
        simpl in Hmf.
        case_match. 
        2: { lia. }
        rewrite negb_false_iff.
        eapply (introT (Nat.eqb_spec 0 _)).
        rewrite evar_open_mu_depth.
        {
          fm_solve.
        }
        (*{ solve_fresh_neq. }*)
        symmetry in H.
        exact H.
      }
      {
        rewrite evar_open_size'. lia.
      }

      mlExists x0. mlSimpl.
      mlAssert ("Hand": (ψ and (cpatt^{evar:0↦x0}^[[evar:cvar↦ϕ]]))).
      { wf_auto2. }
      { subst cpatt_1.
        rewrite evar_open_free_evar_subst_swap.
        { fm_solve. }
        { wf_auto2. }
        mlSplitAnd; mlAssumption.
      }
      mlClear "Hψ". mlClear "H".
      mlRevertLast.
      mlRewrite IHsz at 1.
      mlIntro "H".
      mlDestructAnd "H" as "H1" "H2".
      subst cpatt_2.
      rewrite evar_open_free_evar_subst_swap.
      { fm_solve. }
      { wf_auto2. }
      mlExact "H2".
    }
    {
      mlDestructEx "H" as x0.
      specialize (IHsz (cpatt^{evar:0↦x0})).
      ospecialize* IHsz.
      {
        wf_auto2.
      }
      {
        unfold mu_in_evar_path in *.
        simpl in Hmf.
        case_match. 
        2: { lia. }
        rewrite negb_false_iff.
        eapply (introT (Nat.eqb_spec 0 _)).
        rewrite evar_open_mu_depth.
        {
          fm_solve.
        }
        symmetry in H.
        exact H.
      }
      {
        rewrite evar_open_size'. lia.
      }
      mlExists x0. mlSimpl.
      mlAssert ("Hand": (ψ and (cpatt^{evar:0↦x0}^[[evar:cvar↦ψ and ϕ]]))).
      { wf_auto2. }
      { 
        subst cpatt_2.
        rewrite evar_open_free_evar_subst_swap.
        { fm_solve. }
        { wf_auto2. }
        mlSplitAnd; mlAssumption.
      }
      mlClear "Hψ". mlClear "H".
      mlRevertLast.
      mlRewrite <- IHsz at 1.
      mlIntro "H".
      mlDestructAnd "H" as "H1" "H2".
      subst cpatt_1.
      rewrite evar_open_free_evar_subst_swap.
      { fm_solve. }
      { wf_auto2. }
      mlExact "H2".
    }
    
  + 
    destruct (decide (cvar ∈ free_evars cpatt)).
    {
      unfold mu_in_evar_path in Hmf.
      cbn in Hmf.
      case_match.
      2: { lia. }
      rewrite maximal_mu_depth_to_S in H.
      assumption.
      inversion H.
    }
    {
      rewrite free_evar_subst_no_occurrence.
      { assumption. }
      rewrite free_evar_subst_no_occurrence.
      { assumption. }
      useBasicReasoning.
      apply pf_iff_equiv_refl.
      wf_auto2.
    }
Defined.

(* Lemma 89 *)
(* TODO: it is worth splitting this theorem, since the ---> direction requires
         fewer side conditions *)
Lemma mu_and_predicate_propagation {Σ : Signature} {syntax : Syntax} Γ ϕ ψ :
  Definedness_Syntax.theory ⊆ Γ ->
  well_formed (mu, ϕ) ->
  well_formed ψ ->
  (* "Let X be a set variable that does not occur under any µ-binder in ϕ" *)
  bound_svar_is_banned_under_mus ϕ 0 0 ->
  Γ ⊢ is_predicate_pattern ψ ->
  Γ ⊢ (mu, (ψ and ϕ)) <---> (ψ and (mu, ϕ)).
Proof.
  intros HΓ wfm wfψ Hbsltϕ1 Hp.

  assert (well_formed (mu , ψ and ϕ)).
  {
    clear -wfm wfψ.
    unfold well_formed,well_formed_closed in *.
    cbn in *. fold no_negative_occurrence_db_b.
    destruct_and!.
    split_and!; try reflexivity; try assumption.
    {
      apply wfc_impl_no_neg_occ.
      assumption.
    }
    {
      wf_auto2.
    }
  }

  apply pf_iff_split.
  { assumption. }
  { wf_auto2. }
  {
    toMLGoal.
    {
      wf_auto2.
    }
    mlIntro "H".
    mlSplitAnd.
    {
      fromMLGoal.
      apply Knaster_tarski.
      { try_solve_pile. }
      { wf_auto2. }
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
      fromMLGoal.
      mlFreshSvar as X.
      apply mu_monotone with (X := X).
      { apply pile_any. }
      1-2: wf_auto2.
      1: fm_solve.
      {
        mlSimpl.
        gapply pf_conj_elim_r.
        { try_solve_pile. }
        { wf_auto2. }
        { wf_auto2. }
      }
    }
  }
  {
    toMLGoal.
    { wf_auto2. }
    mlRewrite (useBasicReasoning AnyReasoning (@patt_and_comm Σ Γ ψ (mu , ϕ) wfψ wfm)) at 1.
    fromMLGoal.
    apply lhs_from_and.
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }

    apply Knaster_tarski.
    { try_solve_pile. }
    { wf_auto2. }

    apply lhs_to_and.
    { wf_auto2.
      fold no_negative_occurrence_db_b.
      apply wfc_impl_no_neg_occ. wf_auto2.
    }
    { wf_auto2. }
    { wf_auto2. }
    
    toMLGoal.
    { wf_auto2. fold no_negative_occurrence_db_b. apply wfc_impl_no_neg_occ. wf_auto2. }
    assert (Htmp : is_true (well_formed (mu , ϕ) ^ [ψ ---> (mu , ψ and ϕ)])).
    {
      wf_auto2. fold no_negative_occurrence_db_b. apply wfc_impl_no_neg_occ. wf_auto2.
    }
    cbn in Htmp.
    simpl.
    mlRewrite (useBasicReasoning AnyReasoning (@patt_and_comm Σ Γ _ ψ Htmp wfψ)) at 1.
    
    mlIntro "H".
    mlApplyMeta Pre_fixp.
    unfold instantiate.
    mlSimpl.
    fromMLGoal.
    rewrite -> well_formed_bsvar_subst with (φ := ψ) (k := 0).
    2: auto.
    2: wf_auto2.

    (* apply Lemma 88 of the paper. *)
    remember (evar_fresh_s (free_evars (ϕ ---> ψ))) as x.
    pose proof (HH := pred_and_ctx_and Γ
      {|
        pcEvar := x;
        pcPattern := ϕ^[svar:0↦patt_free_evar x];
      |}
      (ψ ---> (mu , ψ and ϕ)) ψ HΓ).
    unfold emplace in HH. simpl in HH.
    ospecialize* HH.
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    {
      unfold mu_in_evar_path.
      rewrite negb_false_iff. cbn.
      case_match; try reflexivity.
      exfalso.
      pose proof (Htmp2 := maximal_mu_depth_to_svar_subst_evar_banned x ϕ 0 0 0).
      cbn in Htmp2.
      ospecialize* Htmp2.
      {
        wf_auto2.
      }
      {
        subst x. clear.
        eapply evar_is_fresh_in_richer'.
        2: apply set_evar_fresh_is_fresh'.
        {
          cbn. set_solver.
        }
      }
      { exact Hbsltϕ1. }
      {
        lia.
      }
    }
    { assumption. }

    assert (no_negative_occurrence_db_b 0 ψ = true).
    {
      apply wfc_impl_no_neg_occ. wf_auto2.
    }

    toMLGoal.
    { wf_auto2. }
    rewrite subst_svar_evar_svar in HH.
    { subst x. solve_fresh. }
    rewrite subst_svar_evar_svar in HH.
    { subst x. solve_fresh. }
    clear Htmp.
    unshelve(epose proof (Htmp := @liftProofInfoLe _ _ _ _ AnyReasoning _ HH)).
    { try_solve_pile. }
    mlRewrite Htmp at 1.

    clear Heqx x H Htmp.

    remember (evar_fresh_s (free_evars ϕ)) as x.
    pose proof (HH' := impl_ctx_impl_pos Γ
      {|
        pcEvar := x;
        pcPattern := ϕ^[svar:0↦patt_free_evar x];
      |}
      (ψ and (ψ ---> (mu , ψ and ϕ)))
      (mu , ψ and ϕ)
      AnyReasoning
      ).
    unfold emplace in HH'. simpl in HH'.
    ospecialize* HH'.
    { wf_auto2. }
    { wf_auto2. }
    { wf_auto2. }
    { unfold is_positive_context. cbn.
      unfold well_formed in wfm.
      cbn in wfm.
      destruct_and! wfm.
      apply no_neg_svar_subst.
      {  clear -H2 Heqx. subst. eapply evar_is_fresh_in_richer'. 2: apply set_evar_fresh_is_fresh. set_solver. }
      { assumption. }
    }
    { try_solve_pile. }
    toMLGoal.
    { wf_auto2. }
    { mlIntro "H". mlDestructAnd "H". mlApply "1". mlExact "0". }

    rewrite subst_svar_evar_svar in HH'.
    {
      subst x. solve_fresh.
    }
    
    rewrite subst_svar_evar_svar in HH'.
    {
      subst x. solve_fresh.
    }

    mlIntro "H".
    mlDestructAnd "H" as "H0" "H1".
    mlSplitAnd.
    + mlExact "H0".
    + mlApplyMeta HH'. mlExact "H1".
  }
Defined.


Theorem deduction_theorem {Σ : Signature} {syntax : Syntax} Γ ϕ ψ
  (gpi : ProofInfo)
  (pf : Γ ∪ {[ ψ ]} ⊢i ϕ using gpi) :
  well_formed ϕ ->
  well_formed ψ ->
  theory ⊆ Γ ->
  pi_generalized_evars gpi ## (gset_to_coGset (free_evars ψ)) ->
  pi_substituted_svars gpi ## (gset_to_coGset (free_svars ψ)) ->
  pi_uses_advanced_kt gpi = false ->
  Γ ⊢i ⌊ ψ ⌋ ---> ϕ
  using AnyReasoning.
Proof.
  intros wfϕ wfψ HΓ HnoExGen HnoSvarSubst Hnoakt.
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
        apply total_phi_impl_phi; try assumption.
        instantiate (1 := fresh_evar ψ). solve_fresh.
      }
      {
        try_solve_pile.
      }

    + assert (axiom0 ∈ Γ).
      { clear -e n. set_solver. }
      toMLGoal.
      { wf_auto2. }
      mlIntro. mlClear "0". fromMLGoal.
      eapply useGenericReasoning.
      2: apply (BasicProofSystemLemmas.hypothesis Γ axiom0 i H).
      try_solve_pile.
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
    ospecialize* IHpf1.
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { unfold implb in *.
        destruct (uses_kt pf1) eqn:Hktpf1;[|reflexivity]. simpl in *.
        exact Hpf4.
      }
      {
        cbn in *.
        unfold is_true.
        rewrite implb_true_iff.
        intro Hakt1.
        rewrite Hakt1 in pwi_pf_kta. simpl in pwi_pf_kta.
        unfold is_true in pwi_pf_kta.
        rewrite andb_true_iff in pwi_pf_kta.
        destruct pwi_pf_kta as [HH1 HH2].
        rewrite HH1.
        simpl.
        apply kt_unreasonably_implies_somehow.
        exact Hakt1.
      }
    }
    { assumption. }
    ospecialize* IHpf2.
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
        cbn in *.
        unfold is_true.
        rewrite implb_true_iff.
        intro Hakt1.
        rewrite Hakt1 in pwi_pf_kta. rewrite orb_true_r in pwi_pf_kta.
        simpl in pwi_pf_kta.
        unfold is_true in pwi_pf_kta.
        rewrite andb_true_iff in pwi_pf_kta.
        destruct pwi_pf_kta as [HH1 HH2].
        rewrite HH1.
        simpl.
        apply kt_unreasonably_implies_somehow.
        exact Hakt1.
      }
    }
    { wf_auto2. }

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
    destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
    simpl in Hpf2, Hpf3, Hpf4.
    (*
    simpl in HnoExGen.
    case_match;[congruence|]. *)
    ospecialize* IHpf.
    {
      constructor; simpl.
      { clear -Hpf2. set_solver. }
      { clear -Hpf3. set_solver. }
      { apply Hpf4. }
      { apply Hpf5. }
    }
    { clear Hpf5; wf_auto2. }

    apply reorder_meta in IHpf.
    2-4:  clear Hpf5; wf_auto2.
    apply Ex_gen with (x := x) in IHpf.
    3: { simpl. set_solver. }
    2: { try_solve_pile. }
    apply reorder_meta in IHpf.
    2-4: clear Hpf5; wf_auto2.
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
    destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
    simpl in Hpf2,Hpf3,Hpf4.
    ospecialize* IHpf.
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { apply Hpf4. }
      { apply Hpf5. }
    }
    { wf_auto2. }
    mlFreshEvar as x.
    apply framing_left_under_tot_impl with (x := x).
    1-4: solve [wf_auto2].
    { exact HΓ. }
    { clear-FM. ltac2:(_fm_export_everything()). set_solver. }
    { try_solve_pile. }
    { exact IHpf. }
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

    destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
    simpl in Hpf2,Hpf3,Hpf4.
    ospecialize* IHpf.
    {
      constructor; simpl.
      { set_solver. }
      { set_solver. }
      { apply Hpf4. }
      { apply Hpf5. }
    }
    { clear Hpf5; wf_auto2. }

    mlFreshEvar as x.
    apply framing_right_under_tot_impl with (x := x).
    1-4: solve [wf_auto2].
    { exact HΓ. }
    { clear-FM. ltac2:(_fm_export_everything()). set_solver. }
    { try_solve_pile. }
    { exact IHpf. }
    
  - (* Set variable substitution *)
    simpl in HnoExGen. simpl in HnoSvarSubst. simpl in IHpf.
    destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
    simpl in Hpf2, Hpf3, Hpf4.
    ospecialize* IHpf.
    {
      constructor; simpl.
      { exact Hpf2. }
      { clear -Hpf3. set_solver. }
      { exact Hpf4. }
      { exact Hpf5. }
    }
    {
      wf_auto2.
    }
    clear Hpf5.
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
      subst i'. try_solve_pile.
    }
    { wf_auto2. }

  - (* Prefixpoint *)
    toMLGoal.
    { wf_auto2. }
    mlIntro. mlClear "0". fromMLGoal.
    apply useBasicReasoning.
    apply Pre_fixp. wf_auto2.
  - (* Knaster-Tarski *)
    destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
    apply lhs_to_and.
    1-3: clear Hpf2 Hpf3 Hpf4 Hpf5; wf_auto2.
    remember_constraint as pi.
    ospecialize* IHpf.
    {
      cbn. constructor; try assumption.
      {
        clear -Hpf4.
        destruct (uses_kt pf) eqn:H; rewrite H; simpl.
        2: reflexivity.
        simpl in Hpf4.
        assumption.
      }
      {
        unfold is_true.
        rewrite implb_true_iff. intros HH.
        cbn in *.
        unfold is_true in Hpf5.
        rewrite HH in Hpf5. rewrite orb_true_r in Hpf5. simpl in Hpf5.
        rewrite Hnoakt in Hpf5. inversion Hpf5.
      }
    }
    { clear Hpf2 Hpf3 Hpf4 Hpf5.
      wf_auto2.
    }

    cbn in *.
    unfold is_true in Hpf5.
    rewrite andb_true_r in Hpf5.
    rewrite Hnoakt in Hpf5.
    rewrite implb_false_r in Hpf5.
    rewrite negb_orb in Hpf5.
    destruct (decide (~~ bound_svar_is_banned_under_mus phi 0 0 = true)) as [Ht|Hf].
    {
      rewrite Ht in Hpf5. simpl in Hpf5. inversion Hpf5.
    }
    apply not_true_is_false in Hf.
    rewrite Hf in Hpf5.
    cbn in Hpf5.
    apply negb_true_iff in Hpf5.
    remember (svar_fresh_s (free_svars ⌊ ψ ⌋ ∪ free_svars phi)) as X.
    epose proof (Htmp := @mu_and_predicate_propagation _ _ Γ phi ⌊ ψ ⌋ _ _ _).
    ospecialize* Htmp.
    { 
      rewrite negb_false_iff in Hf.
      exact Hf.
    }
    {
      gapply floor_is_predicate.
      { try_solve_pile. }
      { exact HΓ. }
      { wf_auto2. }
      { instantiate (1 := fresh_evar ψ). solve_fresh. }
      { instantiate (1 := fresh_evar (ψ ⋅ patt_free_evar (fresh_evar ψ))). solve_fresh. }
      { instantiate (1 := fresh_evar (ψ ⋅ patt_free_evar (fresh_evar ψ) ⋅ 
                      patt_free_evar (fresh_evar (ψ ⋅ patt_free_evar (fresh_evar ψ))))). solve_fresh. }
      { try_solve_pile. }
    }
    toMLGoal.
    { clear Hpf2 Hpf3 Hpf4; wf_auto2. }
    mlIntro.
    apply pf_iff_proj2 in Htmp.
    mlApplyMeta Htmp in "0". clear Htmp.
    fromMLGoal.
    apply Knaster_tarski.
    { subst pi. try_solve_pile. }
    1,4,5:clear Hpf2 Hpf3 Hpf4 Hpf5; wf_auto2.
    {
      fold no_negative_occurrence_db_b.
      apply wfc_impl_no_neg_occ.
      wf_auto2.
    }
    {
      fold no_negative_occurrence_db_b.
      apply wfc_impl_no_neg_occ.
      wf_auto2.
    }
    2: { try_solve_pile. }

    unfold instantiate.
    mlSimpl.
    apply lhs_from_and.

    1-3:clear Hpf2 Hpf3 Hpf4; wf_auto2. 
    
    rewrite -> well_formed_bsvar_subst with (k := 0).
    3: wf_auto2.
    2: lia.
    simpl in IHpf.
    apply IHpf.

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
    Unshelve.
    2,3: wf_auto2.
    1: exact HΓ.
Defined.


Lemma MLGoal_deduct'
  {Σ : Signature}
  {syntax : Syntax}
  (Γ : Theory)
  (l : hypotheses)
  name
  (ψ g : Pattern)
  (C : PatternCtx)
  (i : ProofInfo)
  :
  theory ⊆ Γ ->
  pi_generalized_evars i ## gset_to_coGset (free_evars ψ) ->
  pi_substituted_svars i ## gset_to_coGset (free_svars ψ) ->
  pi_uses_advanced_kt i = false ->
  mkMLGoal Σ (Γ ∪ {[ψ]}) l g i ->
  mkMLGoal Σ Γ ((mkNH _ name ⌊ ψ ⌋) :: l) g AnyReasoning .
Proof.
  intros HΓ Hge Hse Hakt H.
  intros wf1 wf2. cbn in *.
  ospecialize* H.
  { wf_auto2. }
  { cbn in wf2. cbn. destruct_and!. assumption. }
  cbn in *.
  eapply deduction_theorem.
  { apply H. }
  { wf_auto2. }
  { wf_auto2. }
  { exact HΓ. }
  { assumption. }
  { assumption. }
  { assumption. }
Defined.

Lemma MLGoal_deduct
  {Σ : Signature}
  {syntax : Syntax}
  (Γ : Theory)
  (l₁ l₂ : hypotheses)
  name
  (ψ g : Pattern)
  :
  theory ⊆ Γ ->
  mkMLGoal Σ (Γ ∪ {[ψ]}) (l₁ ++ l₂) g
    ((ExGen := ⊤ ∖ gset_to_coGset (free_evars ψ), SVSubst := ⊤ ∖ gset_to_coGset (free_svars ψ), KT := true, AKT := false)) ->
  mkMLGoal Σ Γ (l₁ ++ (mkNH _ name ⌊ ψ ⌋) :: l₂) g AnyReasoning .
Proof.
  intros HΓ H.
  intros wf1 wf2. cbn in *.

  rewrite map_app in wf2. cbn in wf2.
  rewrite map_app in wf2. cbn in wf2.
  rewrite foldr_app in wf2. cbn in wf2.
  rewrite foldr_andb_true_iff in wf2.

  assert (well_formed ψ).
  {
    wf_auto2.
  }
  assert (wf (map nh_patt l₁)).
  {
    destruct_and!. assumption.
  }
  assert (wf (map nh_patt l₂)).
  {
    destruct_and!. assumption.
  }
  
  ospecialize* H.
  { wf_auto2. }
  { cbn in wf2. cbn.
    rewrite map_app. cbn.
    rewrite map_app. cbn.
    rewrite foldr_app. cbn.
    rewrite foldr_andb_true_iff.
    destruct_and!.
    split_and!;assumption.
  }
  cbn in *.
  rewrite map_app.
  apply reorder_middle_to_head_meta.
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  { wf_auto2. }
  cbn.
  eapply deduction_theorem.
  { 
    rewrite map_app in H.
    apply H.
  }
  { wf_auto2. }
  { wf_auto2. }
  { exact HΓ. }
  { cbn. rewrite union_empty_l_L.
    unfold disjoint.
    unfold set_disjoint_instance.
    intros x Hx HContra.
    rewrite elem_of_gset_to_coGset in HContra.
    cbn in Hx.
    clear -Hx HContra.
    contradiction.
  }
  { cbn. rewrite union_empty_l_L.
    unfold disjoint.
    unfold set_disjoint_instance.
    intros x Hx HContra.
    rewrite elem_of_gset_to_coGset in HContra.
    cbn in Hx.
    clear -Hx HContra.
    contradiction.
  }
  {
    reflexivity.
  }
Defined.


Tactic Notation "mlDeduct" constr(name) :=
  _ensureProofMode;
  _mlReshapeHypsByName name;
  apply MLGoal_deduct;
  [try assumption|_mlReshapeHypsBack]
.

#[local]
Example ex_deduct
  {Σ : Signature} {syntax : Syntax} (Γ : Theory) (ϕ₁ ϕ₂ ϕ₃ : Pattern)
  : 
  well_formed ϕ₁ ->
  well_formed ϕ₂ ->
  well_formed ϕ₃ ->
  theory ⊆ Γ ->
  Γ ⊢ ϕ₁ ---> ⌊ ϕ₂ ⌋ ---> ϕ₃ ---> ϕ₂
.
Proof.
  intros wf1 wf2 wf3 HΓ.
  mlIntro "H1".
  mlIntro "H2".
  mlIntro "H3".
  mlDeduct "H2".
  useBasicReasoning.
  mlClear "H1".
  mlClear "H3".
  fromMLGoal.
  apply hypothesis.
  { wf_auto2. }
  { set_solver. }
Defined.

(*  eq-elim.0 $e #Substitution ph2 ph4 ph0 x $.   => ph2 = ph4[ph0/x]
    eq-elim.1 $e #Substitution ph3 ph4 ph1 x $.   => ph3 = ph4[ph1/x]
    eq-elim $a |- ( \imp ( \eq ph0 ph1 ) ( \imp ph2 ph3 ) ) $.
                                                  => ph0 = ph1 -> ph2 -> ph3

  Improved version of equality elimination - we can use the following lemma for
  all contexts in which μs bind set variables only on their outermost level.
  (Basically, this means, that all bound set variables are 0s)
 *)
Lemma equality_elimination
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
  destruct C as [y C]. unfold emplace. simpl in *.
  (** C is the context pattern, and y is the context variable from now on *)
  assert (well_formed C) by wf_auto2. clear WFC.
  revert φ1 φ2 Γ HΓ H WF1 WF2 Hmu.
  (** size-based induction on the context *)
  size_induction C; simpl in *; intros.

  (** C = x *)
  * case_match.

    (** C = □ (the context's hole) *)
    - subst.
      mlIntro "H".
      mlFreshEvar as y.
      (* ExGen : {[ev_x; x]} is needed for this: *)
      mlApplyMeta total_phi_impl_phi in "H".
      (***)
      mlDestructAnd "H".
      mlAssumption.
      2: assumption.
      1: instantiate (1 := y); fm_solve.

    (** C = x ≠ □ *)
    - do 2 mlIntro. mlAssumption.

  (** C = X *)
  * do 2 mlIntro. mlAssumption.

  (** C is a bound element variable --- C is not well-formed *)
  * do 2 mlIntro. mlAssumption.

  (** C is a bound set variable --- C is not well-formed *)
  * do 2 mlIntro. mlAssumption.

  (** C = σ *)
  * do 2 mlIntro. mlAssumption.

  (** C = C₁ ⋅ C₂ *)
  * mlIntro "H".
    pose proof (IH1 := IHsz C1 ltac:(lia) φ1 φ2
                            Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)
                            ltac:(by apply andb_true_iff in Hmu as [? ?])).
    pose proof (IH2 := IHsz C2 ltac:(lia) φ1 φ2
                            Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)
                            ltac:(by apply andb_true_iff in Hmu as [? ?])).
    clear IHsz Hmu.
    mlAssert ("H2" : (φ1 =ml φ2)). wf_auto2. mlAssumption.

    apply framing_left_under_tot_impl with (x := fresh_evar ((φ1 <---> φ2) ---> C2^[[evar:y↦φ2]])) (psi := C2^[[evar:y↦φ2]]) in IH1. 2-8: shelve. (** side conditions *)
    apply framing_right_under_tot_impl with (x := fresh_evar ((φ1 <---> φ2) ---> C1^[[evar:y↦φ1]])) (psi := C1^[[evar:y↦φ1]]) in IH2. 2-8: shelve. (** side conditions *)

    mlApplyMeta IH1 in "H".
    mlApplyMeta IH2 in "H2".
    mlIntro "H0".
    mlApply "H".
    mlApply "H2".
    mlAssumption.

    (** solving the side conditions from above *)
    Unshelve.
    6, 13: solve_fresh.
    6, 12: try_solve_pile.
    5, 10: assumption.
    all: wf_auto2.

  (** C = ⊥ *)
  * do 2 mlIntro. mlAssumption.

  (** C = C₁ ---> C₂ *)
  * mlIntro "H".
    pose proof (IH1 := IHsz C1 ltac:(lia) φ2 φ1
                            Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)
                            ltac:(by apply andb_true_iff in Hmu as [? ?])).
    pose proof (IH2 := IHsz C2 ltac:(lia) φ1 φ2
                            Γ HΓ ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)
                            ltac:(by apply andb_true_iff in Hmu as [? ?])).
    clear IHsz Hmu.
    mlAssert ("H2" : (φ2 =ml φ1)). wf_auto2.
    {
      mlSymmetry. mlAssumption.
    }
    mlApplyMeta IH1 in "H2".
    mlApplyMeta IH2 in "H".
    mlIntro "H0". mlIntro "S".
    clear.
    mlApply "H".
    mlApply "H0".
    mlApply "H2".
    mlAssumption.

  (** C = ∃x.C *)
  * do 2 mlIntro.

    mlDestructEx "1" as z.

    mlExists z.

    epose proof (IHsz (evar_open z 0 C) _ φ1 φ2 Γ HΓ _ _ _ _).
                                  (** _-s are side conditions *)

    (** swapping substitutions *)
    rewrite evar_open_free_evar_subst_swap. fm_solve. wf_auto2.
    rewrite evar_open_free_evar_subst_swap. fm_solve. wf_auto2.

    mlApplyMeta H0.
    mlSplitAnd; mlAssumption.

    Unshelve.
    rewrite evar_open_size'; lia.
    1-3: wf_auto2.
    by apply kt_well_formed_evar_open.

  (** C = μX.C *)
  * do 2 mlIntro.
    mlConj "0" "1" as "H".
    mlClear "0".
    mlClear "1".
    (**
      Γ ⊢ φ1 = φ2 ∧ (μX.C[y↦φ1]) ↔ μX.φ1 = φ2 ∧ C[y↦φ1]
    *)
    epose proof (mu_and_predicate_propagation Γ (C^[[evar:y↦φ1]]) (φ1 =ml φ2) HΓ _ _ _). (* _-s are side conditions *)
    ospecialize* H0.
    {
      (**
        conjunction propagation under μ - side condition:
        Γ ⊢ is_predicate_pattern (φ1 =ml φ2)
      *)
      mlFreshEvar as x.
      mlFreshEvar as z.
      mlFreshEvar as w.
      (** This theorem uses Ex-Gen for some fresh x, y, z for which we
          generate concrete variables above *)
      eapply floor_is_predicate with (x := x) (y := z) (z := w); try eassumption.
      wf_auto2.
      fm_solve.
      fm_solve.
      fm_solve.
      try_solve_pile.
    }


    mlAdd H0 as "H0".
    mlDestructAnd "H0" as "H0_1" "H0_2". mlClear "H0_1".
    mlApply "H0_2" in "H". mlClear "H0_2". clear H0.

    mlFreshSvar as X.
    (**
        Γ ⊢ φ1 → φ2
     ---------------------
      Γ ⊢ (μX.φ1) → μX.φ2
    *)
    mlApplyMeta mu_monotone. 3-4: shelve.
    mlAssumption.

    (** Proof of the premise of monotonicity of μ *)
    instantiate (1 := X).

    (** Substiutions do not affect the equality, since they do not contain μ's
        bound variable 
      *)
    mlSimpl.
    rewrite svar_open_not_occur. wf_auto2.
    rewrite svar_open_not_occur. wf_auto2.

    (** Swapping the substitutions *)
    unfold svar_open.
    rewrite -free_evar_subst_bsvar_subst. wf_auto2. unfold evar_is_fresh_in; set_solver.
    rewrite -free_evar_subst_bsvar_subst. wf_auto2. unfold evar_is_fresh_in; set_solver.

    mlIntro. mlDestructAnd "0".
    fromMLGoal.
    (** size-based induction is needed to make this `apply` *)
    apply IHsz.
    Unshelve.
    rewrite svar_open_size'. lia.
    assumption.
    1-3, 5-6: wf_auto2.
    destruct_and!. apply kt_well_formed_svar_open; wf_auto2.
    {
      (** Mu-pattern side condition of the monotonicity theorem *)
      destruct_and!.
      apply bound_svar_is_banned_under_mus_fevar_subst_alternative.
      * wf_auto2.
      * apply bsvar_occur_false_impl_banned.
        apply wfc_mu_aux_implies_not_bsvar_occur. wf_auto2.
      * assumption.
    }
    { (** monotonicity side condition, originating from the locally-nameless
          approach *)
      ltac2:(_fm_export_everything()).
      pose proof free_svars_free_evar_subst.
      set_solver.
    }
    {
      wf_auto2.
      all: fold no_negative_occurrence_db_b.
      all: fold no_positive_occurrence_db_b.
      all: wf_auto2.
    }
Defined.

Lemma pattern_kt_well_formed_free_evar_subst {Σ : Signature}:
  forall φ ψ x,
    pattern_kt_well_formed φ ->
    pattern_kt_well_formed ψ ->
    well_formed ψ ->
    pattern_kt_well_formed (free_evar_subst ψ x φ).
Proof.
  induction φ; simpl; intros; try reflexivity.
  * case_match; by simpl.
  * rewrite -> IHφ1, -> IHφ2. reflexivity.
    all: naive_bsolver.
  * rewrite -> IHφ1, -> IHφ2. reflexivity.
    all: naive_bsolver.
  * by rewrite IHφ.
  * rewrite IHφ. 2: assumption. 1: naive_bsolver. 1: assumption.
    rewrite bound_svar_is_banned_under_mus_fevar_subst_alternative.
    wf_auto2. 2: naive_bsolver. 2: reflexivity.
    apply bsvar_occur_false_impl_banned.
    apply wfc_mu_aux_implies_not_bsvar_occur. wf_auto2.
Qed.


Corollary equality_elimination_eq
  {Σ : Signature}
  {sy : Definedness_Syntax.Syntax}
  Γ φ1 φ2 C
  (HΓ : theory ⊆ Γ)
  (WF1 : well_formed φ1)
  (WF2 :  well_formed φ2)
  (WFC : PC_wf C)
  (Hmu : pattern_kt_well_formed (pcPattern C))
  (Htechnical : pattern_kt_well_formed φ1) :
  Γ ⊢i (φ1 =ml φ2) --->
    (emplace C φ1) =ml (emplace C φ2)
  using AnyReasoning.
Proof.
  unfold PC_wf in WFC. destruct C as [x C]. cbn in *.
  mlIntro "H".
  mlFreshEvar as y.
  epose proof (equality_elimination Γ φ1 φ2
       {| pcEvar := y; pcPattern := C^[[evar:x↦φ1]] =ml
                                    C^[[evar:x↦patt_free_evar y]] |}
              HΓ WF1 WF2 ltac:(wf_auto2) _).
  unfold emplace in H. mlSimpl in H. simpl in H.
  rewrite free_evar_subst_chain in H. 1: fm_solve.
  rewrite free_evar_subst_chain in H. 1: fm_solve.
  rewrite (free_evar_subst_no_occurrence y) in H. 1: fm_solve.
  rewrite (free_evar_subst_no_occurrence y) in H. 1: fm_solve.
  mlApplyMeta H in "H".
  mlApply "H".
  mlReflexivity.
Unshelve.
  cbn.
  rewrite !pattern_kt_well_formed_free_evar_subst; try reflexivity.
  all: wf_auto2.
Defined.

Lemma exists_singleton {Σ : Signature} {syntax : Definedness_Syntax.Syntax} Γ φ :
  theory ⊆ Γ ->
  well_formed (ex, φ) ->
  pattern_kt_well_formed φ ->
  Γ ⊢ patt_exists (patt_and (patt_bound_evar 0) φ) --->
                  (patt_forall ((patt_bound_evar 0) ---> φ)).
Proof.
  intros.
  mlIntro. mlDestructEx "0" as x. mlSimpl. cbn.
  mlDestructAnd "0".
  mlRevert "2". mlRevert "1".
  mlApplyMeta membership_implies_implication.
  mlApplyMeta membership_imp_2. 2: assumption.
  mlIntro.
  unfold patt_forall.
  mlApplyMeta membership_not_2. 2: assumption.
  mlIntro.
  mlFreshEvar as y.
  mlApplyMeta membership_exists_1 in "1".
  2: instantiate (1 := y); fm_solve.
  2: assumption.
  _mlReshapeHypsByName "1".
  apply MLGoal_destructEx with (x := y). try_solve_pile.
  2: fm_solve.
  2: fm_solve.
  2: fm_solve.
  1: ltac2:(_fm_export_everything()); cbn; pose proof (free_evars_evar_open); set_solver.
  simpl. mlSimpl. cbn.
  mlApplyMeta membership_not_1 in "1". 2: assumption.
  mlApply "1".
  mlClear "1".
  mlApplyMeta membership_imp_2. 2: assumption.
  mlIntro.
  mlApplyMeta overlapping_variables_equal in "1". 2: assumption.
  mlFreshEvar as z.
  opose proof* (equality_elimination Γ (patt_free_evar x) (patt_free_evar y)
     {| pcEvar := z; pcPattern := patt_free_evar x ∈ml φ^{evar:0↦z}|} H
     ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
   {
     cbn. rewrite kt_well_formed_evar_open. assumption. reflexivity.
   }
   unfold emplace in H2. mlSimpl in H2. cbn in H2.
   case_match. 1: subst z; ltac2:(_fm_export_everything()); exfalso; set_solver.
   erewrite <- !bound_to_free_variable_subst in H2.
   2: instantiate (1 := 1); lia.
   5: instantiate (1 := 1); lia.
   2-3, 5-6: wf_auto2.
   2: fm_solve.
   2: fm_solve.
   mlApplyMeta H2.
   mlSplitAnd; mlAssumption.
Defined.

Close Scope ml_scope.
Close Scope string_scope.
Close Scope list_scope.