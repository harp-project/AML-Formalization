From LibHyps Require Import LibHyps.

From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Btauto.

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

Set Default Proof Mode "Classic".

(*
Example oah a b c :
  a /\ b /\ c = true ->
  c = true
.
Proof.
  intros H.
  onAllHyps (fun h => try destruct h).
Qed.
*)

Definition wfPositiveSimplifications := (
  @well_formed_positive_foldr_binary,
  @nullary_wfp,
  @unary_wfp,
  @binary_wfp,
  @wfp_evar_quan
).

Definition wfCexSimplifications := (
  @well_formed_cex_foldr_binary,
  @nullary_wfcex,
  @unary_wfcex,
  @binary_wfcex
).

Definition wfCmuSimplifications := (
  @well_formed_cmu_foldr_binary,
  @nullary_wfcmu,
  @unary_wfcmu,
  @binary_wfcmu,
  @wfcmu_evar_quan
).

Definition wfSimplifications := (
  @wf_corr,
  @andb_true_r
).

Definition lwfPositiveSimplifications := (
  @lwf_positive_cons,
  @lwf_positive_app
).

Definition lwfCmuSimplifications := (
  @lwf_cmu_cons,
  @lwf_cmu_app
).

Definition lwfCexSimplifications := (
  @lwf_cex_cons,
  @lwf_cex_app
).

Ltac simplifyWfHyp H :=
  let t := type of H in
  (* idtac "SimplifyWfHyp " H " (" t ")"; *)
  lazymatch type of H with
  | well_formed_positive _ = true
    =>
      rewrite ?wfPositiveSimplifications in H;
      destruct_andb? H
  | well_formed_closed_ex_aux _ _ = true
    =>
      rewrite ?wfCexSimplifications in H;
      destruct_andb? H
  | well_formed_closed_mu_aux _ _ = true
    =>
      rewrite ?wfCmuSimplifications in H;
      destruct_andb? H
  | Pattern.wf _ = true
    =>
      rewrite wf_corr in H;
      destruct_andb? H
  | lwf_positive _ = true
    =>
      rewrite ?lwfPositiveSimplifications in H;
      destruct_andb? H
  | lwf_cmu _ _ = true
    =>
      rewrite ?lwfCmuSimplifications in H;
      destruct_andb? H
  | lwf_cex _ _ = true
    =>
      rewrite ?lwfCexSimplifications in H;
      destruct_andb? H
  | _ => idtac
  end
.

Ltac simplifyAllWfHyps :=
  (onAllHyps simplifyWfHyp) ;{ simplifyWfHyp }
.

Ltac decomposeWfGoal :=
  rewrite -?wfxy00_wf;
  rewrite !(wfPositiveSimplifications,
            wfCexSimplifications,
            wfCmuSimplifications,
            wfSimplifications,
            lwfPositiveSimplifications,
            lwfCmuSimplifications,
            lwfCexSimplifications)
.

Ltac towfxy H := rewrite -wfxy00_wf in H.
Ltac simplify_wfxy H := rewrite ?wfSimplifications in H.

Ltac decomposeWfHyps :=
  simplifyAllWfHyps
.
(*
  repeat (
    match goal with
    | [H : _ |- _]
      => simplifyWfHyp H
      (*
    | [H : well_formed_xy _ _ _ |- _]
      => simplify_wfxy H*)
    end
  )
.
*)

Ltac propagateTrueInHyps :=
  repeat (
    match goal with
    | [H: _ |- _] => (
        rewrite !(andb_true_r,andb_true_l) in H
      )
    end
  )
.

Ltac propagateTrueInGoal :=
  rewrite !(andb_true_r,andb_true_l)
.

Tactic Notation "wf_auto" int_or_var(n)
  := auto n; unfold well_formed, well_formed_closed in *; destruct_and?; simpl in *; split_and?; auto n.
Tactic Notation "wf_auto" := wf_auto 5.

(* This hook is specifically intended to be filled with a tactic which
   transforms provability hypotheses into well_formedness hypotheses.
   We call it early, before any goal splitting is done,
   so that it is not called for all the subgoals again and again.
 *)
Ltac2 mutable proved_hook_wfauto
:= (fun () => () (* Message.print (Message.of_string "hook_wfauto base") *)).

(* We give a name to the wrapper so that it is shown in the profile (when profiling). *)
Ltac proved_hook_wfauto := ltac2:(|- proved_hook_wfauto ()).

(*Ltac destruct_and_where_*)

Ltac clear_all_impls :=
  repeat (
    match goal with
    | [ H : forall _, _ |- _] => clear H
    end
  ).

Ltac wf_auto2_step := 
  first [
    progress clear_all_impls|
  progress unfold
    is_true,
    well_formed,
    well_formed_closed,
    well_formed_xy,
    evar_open,
    svar_open,
    free_evar_subst,
    free_evar_subst
    in *|
  assumption|
  reflexivity|
  progress proved_hook_wfauto|
  progress decomposeWfHyps|
  progress destruct_andb?|
  progress simpl in *|
  progress subst|
  progress propagateTrueInGoal|
  progress propagateTrueInHyps|
  (* I do not want to do all the heavy multiple times, once for each subgoal.
     First, decompose all the hypotheses. Then we may start
     decomposing and splitting the goal.
  *)
  progress decomposeWfGoal|
  progress split_and?|
  congruence|
  btauto|
  apply bevar_subst_closed_mu|
  apply bevar_subst_closed_ex|
  apply bevar_subst_positive_2|
  apply evar_quantify_closed_ex|
  apply svar_quantify_closed_ex|
  apply evar_quantify_closed_mu|
  apply svar_quantify_closed_mu|
  apply wfp_free_svar_subst_1|
  apply wfc_mu_free_svar_subst|
  apply wfc_ex_free_svar_subst|
  apply wp_sctx|
  apply wcmu_sctx|
  apply wcex_sctx|
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

  |[ |- context C [ svar_quantify _ _ (svar_open _ _ _) ] ]
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

  end
  ]
.
Ltac wf_auto2 :=
  repeat (
    wf_auto2_step
  )
.

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

Tactic Notation "mlSimpl" :=
  repeat (rewrite mlSimpl'); try rewrite [increase_ex _ _]/=; try rewrite [increase_mu]/=.

Tactic Notation "mlSimpl" "in" hyp(H) :=
  repeat (rewrite mlSimpl' in H); try rewrite [increase_ex _ _]/= in H; try rewrite [increase_mu _ _]/= in H.

Tactic Notation "mlSortedSimpl" := simpl_sorted_quantification; try rewrite [increase_mu]/=.
Tactic Notation "mlSortedSimpl" "in" hyp(H) := simpl_sorted_quantification H; try rewrite [increase_mu]/=.

