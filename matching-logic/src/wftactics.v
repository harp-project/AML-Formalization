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


(* This hook is specifically intended to be filled with a tactic which
   transforms provability hypotheses into well_formedness hypotheses.
   We call it early, before any goal splitting is done,
   so that it is not called for all the subgoals again and again.
 *)
 Ltac2 mutable proved_hook_wfauto
 := (fun () => () (* Message.print (Message.of_string "hook_wfauto base") *)).
 
 (* We give a name to the wrapper so that it is shown in the profile (when profiling). *)
 Ltac proved_hook_wfauto := ltac2:(|- proved_hook_wfauto ()).
 

Definition wfToWfxySimplifications := (
  @wf_wfxy00,
  @wf_lwf_xy
).

Definition wfxySimplifications := (
  @binary_wfxy,
  @unary_wfxy,
  @nullary_wfxy,
  @lwf_xy_app,
  @lwf_xy_cons,
  @well_formed_xy_foldr_binary
).

Ltac simplifyWfxyHyp H :=
  unfold is_true in H;
  lazymatch type of H with
  | well_formed _ = true
    => apply wf_wfxy00_decompose in H
  | Pattern.wf _ = true
    => apply wf_lwf_xy_decompose in H
  | _ => idtac
  end;
  try lazymatch type of H with
  | well_formed_xy ?m ?n (foldr ?binary ?g ?xs) = true
    => apply (well_formed_xy_foldr_binary_decompose _) in H;
       let H1 := fresh "H1" in
       let H2 := fresh "H2" in
       destruct H as [H1 H2];
       simplifyWfxyHyp H1;
       simplifyWfxyHyp H2
  | lwf_xy ?m ?n (?x::?xs) = true
    => apply lwf_xy_cons_decompose in H;
       let H1 := fresh "H1" in
       let H2 := fresh "H2" in
       destruct H as [H1 H2];
       simplifyWfxyHyp H1;
       simplifyWfxyHyp H2
  | lwf_xy ?m ?n (?xs ++ ?ys) = true
    => apply lwf_xy_app_decompose in H;
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      destruct H as [H1 H2];
      simplifyWfxyHyp H1;
      simplifyWfxyHyp H2
  | well_formed_xy ?x ?y (?binary ?ψ1 ?ψ2) = true
    => apply (binary_wfxy_decompose _) in H;
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      destruct H as [H1 H2];
      simplifyWfxyHyp H1;
      simplifyWfxyHyp H2
  | well_formed_xy ?x ?y (?unary ?ψ1) = true
    => apply (unary_wfxy_decompose _) in H;
       simplifyWfxyHyp H
  (* No point in simplifying these *)
  (*
  | well_formed_xy ?x ?y ?nullary = true
    => apply nullary_wfxy in H
    *)
  | _ => idtac
  end
.

Ltac compositeSimplifyAllWfHyps :=
  (*proved_hook_wfauto;*)
  (onAllHyps simplifyWfxyHyp)
.


Ltac compoundDecomposeWfGoal :=
  rewrite ?wfToWfxySimplifications;
  rewrite ?wfxySimplifications;
  lazymatch goal with
  | [ |- ?g] =>
    split_and?;
    lazymatch goal with
    | [ |- ?g'] => idtac (*"Goal " g' " from " g "."*)
    end
  end
.


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

Ltac clear_all_impls :=
  repeat (
    match goal with
    | [ H : forall _, _ |- _] => clear H
    end
  ).


  Ltac wf_auto2_decompose_hyps :=
    proved_hook_wfauto;
    unfold
      is_true,
      evar_open,
      svar_open
    in *;
    simpl in *
  .
  

Ltac solve_size :=
  repeat (
  match goal with
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
  end
  )
.
Ltac wf_auto2_fast_done :=
  try solve_size;
  try assumption;
  try reflexivity;
  try congruence;
  try btauto
.
  
Ltac wf_auto2_composite_step :=
  unfold is_true;
  simpl;
  first [
    split |
    apply wf_wfxy00_compose |
    apply wf_lwf_xy_compose |
    apply free_evar_subst_preserves_no_negative_occurrence |
    apply wf_sctx |
    apply well_formed_xy_free_evar_subst |
    apply (well_formed_xy_foldr_binary_compose _) |
    apply lwf_xy_cons_compose |
    apply lwf_xy_app_compose |
    apply (binary_wfxy_compose _) |
    apply (unary_wfxy_compose _) |
    apply (nullary_wfxy _) |
    apply wf_evar_open_from_wf_ex |
    apply wf_sctx
  ];
  wf_auto2_fast_done
  (*compoundDecomposeWfGoal*)
.

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

Ltac partsDecomposeWfGoal :=
  rewrite -?wfxy00_wf;
  rewrite !(wfPositiveSimplifications,
            wfCexSimplifications,
            wfCmuSimplifications,
            wfSimplifications,
            lwfPositiveSimplifications,
            lwfCmuSimplifications,
            lwfCexSimplifications,
            lwf_xy_decompose)
.


Ltac simplifyWfHypParts H :=
  let t := type of H in
  (* idtac "SimplifyWfHypParts " H " (" t ")"; *)
  lazymatch type of H with
  | well_formed_positive _ = true
    =>
      rewrite ?wfPositiveSimplifications in H;
      destruct_andb? H
  (* We are doing lazymatch, so this has to be before the general case*)
  | well_formed_closed_ex_aux (bevar_subst (patt_free_evar ?x) ?k ?p) ?k = true
      =>
        apply wfc_ex_aux_S_bevar_subst_fe in H
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
  | lwf_xy _ _ _ = true
    =>
      rewrite lwf_xy_decompose in H;
      destruct_andb? H
  | _ => idtac
  end
.

Ltac toBeRunOnAllHypsParts h := simplifyWfHypParts h.

Ltac simplifyAllWfHypsParts :=
  (onAllHyps toBeRunOnAllHypsParts) ;{ toBeRunOnAllHypsParts }
.


Ltac decomposeWfHypsIntoParts :=
  simplifyAllWfHypsParts
.


Ltac wf_auto2_unfolds :=
  unfold
    is_true,
    well_formed,
    well_formed_closed,
    well_formed_xy,
    evar_open,
    svar_open(*,
    free_evar_subst,
    free_evar_subst*)
  in *
.

Ltac wf_auto2_decompose_hyps_parts :=
  proved_hook_wfauto;
  wf_auto2_unfolds;
  simpl in *;
  destruct_andb?;
  decomposeWfHypsIntoParts
.

Ltac wf_auto2_step_parts :=
  wf_auto2_unfolds;
  try partsDecomposeWfGoal;
  simpl in *; subst; simpl in *;
  split_and?;
  wf_auto2_fast_done;
  try first [
  apply well_formed_positive_svar_quantify |
  apply free_evar_subst_preserves_no_negative_occurrence |
  apply no_negative_occurrence_svar_quantify |
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
  apply wfp_bsvar_subst|
  apply wfc_mu_aux_bsvar_subst|
  apply wfc_ex_aux_bsvar_subst
  ];
  try (lazymatch goal with
  | [ H : well_formed_closed_mu_aux ?p 0 = true |- no_negative_occurrence_db_b _ ?p = true]
    => apply wfc_impl_no_neg_occ; apply H

  | [ H : well_formed_closed_mu_aux ?p 0 = true |- no_positive_occurrence_db_b _ ?p = true]
    => apply wfc_impl_no_pos_occ; apply H

  | [ H : well_formed_closed_ex_aux ?p _ = true |- well_formed_closed_ex_aux ?p (S ?n) = true ]
    => eapply well_formed_closed_ex_aux_ind;[|apply H]; lia

    (* last option for well_formed_closed_mu_aux: try decreasing n *)
  | [ H : well_formed_closed_mu_aux ?p _ = true |- well_formed_closed_mu_aux ?p (S ?n) = true ]
    => eapply well_formed_closed_mu_aux_ind;[|apply H]; lia
  end)
.

Ltac wf_auto2_fast :=
  wf_auto2_fast_done;
  compositeSimplifyAllWfHyps;
  repeat wf_auto2_composite_step
.

Ltac print_hyps :=
  try match goal with
  | [H : ?t |- _] => idtac t; fail
  end
.

Ltac wf_auto2_fallback :=
  match goal with
  | [ |- ?G ] => idtac "Falling back on " G (*; print_hyps*)
  end;
  repeat wf_auto2_decompose_hyps_parts;
  repeat wf_auto2_step_parts
.

Ltac wf_auto2 :=
  subst;
  proved_hook_wfauto;
  clear_all_impls;
  (*clear_others;*)
  wf_auto2_fast;
  wf_auto2_fallback
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

