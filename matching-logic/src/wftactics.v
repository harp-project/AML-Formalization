From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import countable infinite.
From stdpp Require Import pmap gmap mapset fin_sets propset.
Require Import stdpp_ext.

From MatchingLogic
Require Import
  Utils.extralibrary
  Pattern
  Substitution
  ApplicationContext
  SyntaxLemmas.FreshnessSubstitution
  SyntacticConstruct
.


Tactic Notation "wf_auto" int_or_var(n)
  := auto n; unfold well_formed, well_formed_closed in *; destruct_and?; simpl in *; split_and?; auto n.
Tactic Notation "wf_auto" := wf_auto 5.

Ltac wf_auto2 := unfold is_true in *;
repeat (try assumption; try reflexivity; try (solve [wf_auto]); (* TODO: get rid of [wf_auto] *)
apply nvnullary_wf || apply unary_wf || apply binary_wf ||
match goal with
| [ |- (forall _, _) ]
  => intro

| [ |- size' (evar_open _ _ _) < _ ]
  => rewrite evar_open_size'

| [ |- size' (svar_open _ _ _) < _ ]
  => rewrite svar_open_size'

| [ |- size' _ < size' (patt_app _ _) ]
  => simpl; lia

| [ |- size' _ < size' (patt_imp _ _) ]
  => simpl; lia

| [ |- size' _ < size' (patt_exists _) ]
  => simpl; lia

| [ |- well_formed (foldr patt_imp ?g ?xs) = true ]
  => apply well_formed_foldr

| [ |- wf (take ?n ?xs) = true ]
  => apply wf_take

| [ |- wf (drop ?n ?xs) = true ]
  => apply wf_drop

| [ |- wf (<[?n := ?p]> ?xs) = true ]
  => apply wf_insert

| [ |- wf (?x :: ?xs) = true ]
  => apply wf_cons

| [ |- wf (?xs ++ ?ys) = true ]
  => apply wf_app

| [ |- well_formed (patt_free_evar _) = true]
  => reflexivity

| [ |- well_formed (patt_free_svar _) = true]
  => reflexivity

| [ H : well_formed (patt_app ?p ?q) = true |- _]
  => assert (well_formed p = true);
    [eapply well_formed_app_proj1; eassumption|];
    assert ( well_formed q = true);
    [eapply well_formed_app_proj2; eassumption|];
    clear H

| [ H : well_formed (patt_imp ?p ?q) = true |- _]
  => assert (well_formed p = true);
    [eapply well_formed_imp_proj1; eassumption|];
    assert ( well_formed q = true);
    [eapply well_formed_imp_proj2; eassumption|];
    clear H

| [ |- well_formed (free_evar_subst ?phi ?p ?E) = true ]
  => apply well_formed_free_evar_subst

| [ |- ?x ∉ ?E ]
  => progress simpl

| [ |- ?x ∉ free_evars (free_evar_subst _ _ _) ]
  => eapply not_elem_of_larger_impl_not_elem_of;
     [apply free_evars_free_evar_subst|]

| [frx: ?x ∉ _ |- ?x <> ?E ]
  => clear -frx; set_solver

| [frx: ?x ∉ _ |- ?x ∉ ?E ]
  => clear -frx; set_solver

| [ |- well_formed (evar_open _ _ _) = true]
  => apply wf_evar_open_from_wf_ex

| [ |- well_formed (@subst_ctx _ _ _) = true]
  => apply wf_sctx

  (* fallback *)
| [ |- well_formed _ = true]
  => unfold well_formed, well_formed_closed in *; simpl in *;
     destruct_and?; split_and?

| [ |- well_formed_positive (free_evar_subst _ _ _) = true ]
  => apply wfp_free_evar_subst

| [H: well_formed_positive (patt_exists _) = true |- _]
  => simpl in H

| [H: well_formed_closed_mu_aux (patt_exists _) _ = true |- _]
  => simpl in H

| [H: well_formed_closed_ex_aux (patt_exists _) _ = true |- _]
  => simpl in H

| [ |- well_formed_closed_mu_aux (free_evar_subst _ _ _) _ = true]
  => apply wfc_mu_free_evar_subst

| [ |- well_formed_closed_ex_aux (free_evar_subst _ _ _) _ = true]
  => apply wfc_ex_free_evar_subst_2; simpl

| [ |- well_formed_positive (bsvar_subst _ _ _) = true ]
  => apply wfp_bsvar_subst

| [ |- well_formed_positive _ = true ]
  => progress (simpl; split_and?)

| [ |- no_negative_occurrence_db_b _ (free_evar_subst _ _ _) = true ]
  => apply free_evar_subst_preserves_no_negative_occurrence

| [ |- well_formed_closed_mu_aux (bsvar_subst _ _ _) _ = true ]
  => apply wfc_mu_aux_bsvar_subst

| [ |- well_formed_closed_ex_aux (bsvar_subst _ _ _) _ = true ]
  => apply wfc_ex_aux_bsvar_subst

| [ |- svar_has_negative_occurrence _ (svar_open _ _ _) = false] =>
  unfold svar_open; apply svar_hno_bsvar_subst

|[ |- context C [ svar_quantify ?X ?n (svar_open ?n ?X _) ] ]
  => rewrite svar_quantify_svar_open

| [ |- well_formed_closed_mu_aux (svar_open _ _ _) _ = true] =>
  unfold svar_open; apply wfc_mu_aux_bsvar_subst

| [ |- well_formed_closed_ex_aux (svar_open _ _ _) _ = true] =>
  unfold svar_open; apply wfc_ex_aux_bsvar_subst

| [ |- no_negative_occurrence_db_b _ _ = true ]
  => solve [unfold well_formed in *; simpl in *; destruct_and!; assumption]

| [ |- no_negative_occurrence_db_b _ (free_evar_subst _ _ _) = true ]
  => apply free_evar_subst_preserves_no_negative_occurrence

(* last option for [svar_has_negative_occurrence] *)
| [ |- svar_has_negative_occurrence _ _ = false ]
  => apply svar_hno_false_if_fresh

| [ |- svar_is_fresh_in _ _ ]
  => unfold svar_is_fresh_in

  (* last option for well_formed_closed_ex_aux: try decreasing n *)
| [ |- well_formed_closed_ex_aux ?p (S ?n) = true ]
  => eapply well_formed_closed_ex_aux_ind with (ind_evar1 := n);[lia|]

  (* last option for well_formed_closed_mu_aux: try decreasing n *)
| [ |- well_formed_closed_mu_aux ?p (S ?n) = true ]
  => eapply well_formed_closed_mu_aux_ind with (ind_svar1 := n);[lia|]

end; unfold is_true in *
).

Ltac try_wfauto2 :=
lazymatch goal with
| [|- is_true (well_formed _)] => wf_auto2
| [|- well_formed _ = true ] => wf_auto2
| [|- is_true (well_formed_closed _)] => wf_auto2
| [|- well_formed_closed _ = true ] => wf_auto2
| [|- is_true (wf _)] => wf_auto2
| [|- wf _ = true ] => wf_auto2
| _ => idtac
end.


Ltac simpl_bevar_subst :=
  repeat (rewrite simpl_bevar_subst';try_wfauto2).
Ltac simpl_bsvar_subst :=
  repeat (rewrite simpl_bsvar_subst';try_wfauto2).