From Coq Require Import ssreflect.
From Coq Require Extraction extraction.ExtrHaskellString.

From Coq Require Import Strings.String.
From Equations Require Import Equations.

From stdpp Require Export base.
From MatchingLogic Require Import Syntax StringSignature ProofSystem .
From MatchingLogicProver Require Import Named.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset.

Section named_proof_system.

  Context {signature : Signature}.

  Definition NamedTheory := propset NamedPattern.
  
  Reserved Notation "theory ⊢N pattern" (at level 76).
  Inductive NP_ML_proof_system (theory : NamedTheory) :
    NamedPattern -> Set :=

  (* Hypothesis *)
  | N_hypothesis (axiom : NamedPattern) :
      named_well_formed axiom = true ->
      axiom ∈ theory -> theory ⊢N axiom

  (* FOL reasoning *)
  (* Propositional tautology *)
  | N_P1 (phi psi : NamedPattern) :
      named_well_formed phi = true -> named_well_formed psi = true ->
      theory ⊢N npatt_imp phi (npatt_imp psi phi)
  | N_P2 (phi psi xi : NamedPattern) :
      named_well_formed phi = true -> named_well_formed psi = true -> named_well_formed xi = true ->
      theory ⊢N npatt_imp (npatt_imp phi (npatt_imp psi xi))
                          (npatt_imp (npatt_imp phi psi) (npatt_imp phi xi))
  | N_P3 (phi : NamedPattern) :
      named_well_formed phi = true ->
      theory ⊢N npatt_imp (npatt_imp (npatt_imp phi npatt_bott) npatt_bott) phi

  (* Modus ponens *)
  | N_Modus_ponens (phi1 phi2 : NamedPattern) :
      named_well_formed phi1 = true -> named_well_formed (npatt_imp phi1 phi2) = true ->
      theory ⊢N phi1 ->
      theory ⊢N npatt_imp phi1 phi2 ->
      theory ⊢N phi2

  (* Existential quantifier *)
  | N_Ex_quan (phi : NamedPattern) (x y : evar) :
      theory ⊢N npatt_imp (rename_free_evar phi y x) (npatt_exists x phi)

  (* Existential generalization *)
  | N_Ex_gen (phi1 phi2 : NamedPattern) (x : evar) :
      named_well_formed phi1 = true ->
      named_well_formed phi2 = true ->
      theory ⊢N npatt_imp phi1 phi2 ->
      x ∉ named_free_evars phi2 ->
      theory ⊢N npatt_imp (npatt_exists x phi1) phi2

  (* Frame reasoning *)
  (* Propagation bottom *)
  | N_Prop_bott_left (phi : NamedPattern) :
      named_well_formed phi = true ->
      theory ⊢N npatt_imp (npatt_app npatt_bott phi) npatt_bott

  | N_Prop_bott_right (phi : NamedPattern) :
      named_well_formed phi = true ->
      theory ⊢N npatt_imp (npatt_app phi npatt_bott) npatt_bott

  (* Propagation disjunction *)
  | N_Prop_disj_left (phi1 phi2 psi : NamedPattern) :
      named_well_formed phi1 = true ->
      named_well_formed phi2 = true ->
      named_well_formed psi = true ->
      theory ⊢N npatt_imp (npatt_app (npatt_or phi1 phi2) psi)
                          (npatt_or (npatt_app phi1 psi) (npatt_app phi2 psi))

  | N_Prop_disj_right (phi1 phi2 psi : NamedPattern) :
      named_well_formed phi1 = true ->
      named_well_formed phi2 = true ->
      named_well_formed psi = true ->
      theory ⊢N npatt_imp (npatt_app psi (npatt_or phi1 phi2))
                          (npatt_or (npatt_app psi phi1) (npatt_app psi phi2))

  (* Propagation exist *)
  | N_Prop_ex_left (phi psi : NamedPattern) (x : evar) :
      named_well_formed (npatt_exists x phi) = true -> 
      named_well_formed psi = true ->
      x ∉ named_free_evars psi ->
      theory ⊢N npatt_imp (npatt_app (npatt_exists x phi) psi)
                          (npatt_exists x (npatt_app phi psi))

  | N_Prop_ex_right (phi psi : NamedPattern) (x : evar) :
      named_well_formed (npatt_exists x phi) = true ->
      named_well_formed psi = true ->
      x ∉ named_free_evars psi ->
      theory ⊢N npatt_imp (npatt_app psi (npatt_exists x phi))
                          (npatt_exists x (npatt_app psi phi))

  (* Framing *)
  | N_Framing_left (phi1 phi2 psi : NamedPattern) :
      theory ⊢N npatt_imp phi1 phi2 ->
      theory ⊢N npatt_imp (npatt_app phi1 psi) (npatt_app phi2 psi)

  | N_Framing_right (phi1 phi2 psi : NamedPattern) :
      theory ⊢N npatt_imp phi1 phi2 ->
      theory ⊢N npatt_imp (npatt_app psi phi1) (npatt_app psi phi2)

  (* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | N_Svar_subst (phi psi : NamedPattern) (X : svar) :
      named_well_formed phi = true ->
      named_well_formed psi = true ->
      theory ⊢N phi -> theory ⊢N standard_svar_subst phi X psi

  (* Pre-Fixpoint *)
  | N_Pre_fixp (phi : NamedPattern) (X : svar) :
      theory ⊢N npatt_imp (standard_svar_subst phi X (npatt_mu X phi)) (npatt_mu X phi)

  (* Knaster-Tarski *)
  | N_Knaster_tarski (phi psi : NamedPattern) (X : svar) :
      theory ⊢N npatt_imp (standard_svar_subst phi X psi) psi ->
      theory ⊢N npatt_imp (npatt_mu X phi) psi

  (* Technical rules *)
  (* Existence *)
  | N_Existence (x : evar) :
      theory ⊢N npatt_exists x (npatt_evar x)

  (* Singleton *)
  | N_Singleton_ctx (C1 C2 : Named_Application_context) (phi : NamedPattern) (x : evar) : 
      theory ⊢N npatt_not (npatt_and
                             (named_subst_ctx C1 (npatt_and (npatt_evar x) phi))
                             (named_subst_ctx C2 (npatt_and (npatt_evar x) (npatt_not phi))))

  where "theory ⊢N pattern" := (NP_ML_proof_system theory pattern).

  (* Named.v *)
  Lemma evar_occurrences_rename ϕ :
    (forall X x y, named_no_negative_occurrence X (rename_free_evar ϕ x y) = named_no_negative_occurrence X ϕ) /\
    (forall X x y, named_no_positive_occurrence X (rename_free_evar ϕ x y) = named_no_positive_occurrence X ϕ).
  Proof.
    induction ϕ; split; intros X0 x0 y0; simpl; try reflexivity.
    * case_match; reflexivity.
    * case_match; reflexivity.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H H1. reflexivity.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H0 H2. reflexivity.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H1.
      unfold named_no_positive_occurrence in H0. rewrite H0. reflexivity.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H2.
      unfold named_no_negative_occurrence in H. rewrite H. reflexivity.
    * case_match. reflexivity. destruct IHϕ. apply H0.
    * case_match. reflexivity. destruct IHϕ. apply H1.
    * destruct IHϕ. apply H.
    * destruct IHϕ. apply H0.
  Defined.

  Lemma named_well_formed_rename ϕ x y:
    named_well_formed ϕ = true ->
    named_well_formed (rename_free_evar ϕ x y) = true.
  Proof.
    induction ϕ; intros Wf; simpl in *; auto.
    * case_match; auto.
    * case_match; auto.
    * rewrite IHϕ; auto.
      rewrite (proj1 (evar_occurrences_rename _)). auto.
  Defined.

  Lemma named_free_evars_rename ϕ x y:
    named_free_evars (rename_free_evar ϕ y x) ⊆ named_free_evars ϕ ∖ {[x]} ∪ {[y]}.
  Proof.
    induction ϕ; simpl.
    * case_match; set_solver.
    * set_solver.
    * set_solver.
    * set_solver.
    * set_solver.
    * set_solver.
    * case_match; set_solver.
    * set_solver.
  Defined.

  Lemma named_free_svars_rename ϕ X Y:
    named_free_svars (rename_free_svar ϕ Y X) ⊆ named_free_svars ϕ ∖ {[X]} ∪ {[Y]}.
  Proof.
    induction ϕ; simpl.
    * set_solver.
    * case_match; set_solver.
    * set_solver.
    * set_solver.
    * set_solver.
    * set_solver.
    * set_solver.
    * case_match; set_solver.
  Defined.

  Lemma standard_evar_subst_id ϕ X ψ:
    X ∉ named_free_svars ϕ ->
    standard_svar_subst ϕ X ψ = ϕ.
  Proof.
    revert X ψ.
    remember (nsize' ϕ) as sz. assert (nsize' ϕ <= sz) by lia. clear Heqsz.
    revert ϕ H. induction sz; intros ϕ Hsz X ψ Hin. destruct ϕ; simpl in Hsz; lia.
    destruct ϕ; simp standard_svar_subst; try reflexivity; simpl in *.
    * destruct decide; simpl; try reflexivity. subst. set_solver.
    * rewrite IHsz. lia. set_solver. rewrite IHsz. lia. set_solver. reflexivity.
    * rewrite IHsz. lia. set_solver. rewrite IHsz. lia. set_solver. reflexivity.
    * rewrite IHsz. lia. set_solver. reflexivity.
    * destruct decide; simpl.
      - reflexivity.
      - destruct decide; simpl.
        + rewrite IHsz. rewrite nsize'_rename_free_svar. lia.
          pose proof named_free_svars_rename. set_solver.
          set_solver.
        + rewrite IHsz. lia. set_solver. reflexivity.
  Defined.

  Lemma svar_subst_rename ϕ ψ X Y :
    Y ∉ named_svars ϕ ->
    standard_svar_subst ϕ X ψ = standard_svar_subst (rename_free_svar ϕ Y X) Y ψ.
  Proof.
    revert X Y ψ.
    induction ϕ; intros X0 Y0 ψ Hin; simpl; simp standard_svar_subst; try reflexivity.
    * case_match; simpl; simp standard_svar_subst.
      - destruct (decide (Y0 = Y0)); simpl. reflexivity. congruence.
      - simpl in Hin. destruct (decide (Y0 = X)); simpl. set_solver. reflexivity.
    * erewrite IHϕ1. erewrite IHϕ2. reflexivity. all: set_solver.
    * erewrite IHϕ1. erewrite IHϕ2. reflexivity. all: set_solver.
    * erewrite IHϕ. reflexivity. set_solver.
    * destruct (decide (X0 = X)); simpl.
      - rewrite standard_evar_subst_id.
        pose proof (named_free_svars_subseteq_named_svars (npatt_mu X0 ϕ)). set_solver. reflexivity.
      - subst. simp standard_svar_subst.
        destruct (decide (Y0 = X)).
        + subst. set_solver. 
        + simpl.
          destruct (decide (X ∈ named_free_svars ψ ∧ X0 ∈ named_free_svars ϕ)); simpl.
          ** destruct a as [Ha1 Ha2].
             remember (svar_fresh _) as FX.
             destruct decide; simpl.
             -- destruct a as [Ha11 Ha22].
                pose proof (named_free_svars_rename ϕ X0 Y0).
                simpl in Hin.
                remember (svar_fresh
                (elements
                   ({[Y0]} ∪ named_free_svars (rename_free_svar ϕ Y0 X0) ∪ named_free_svars ψ))) as FX2.
                (*
                  issue here:
                  ϕ[ψ/x] = ϕ[y/x][ψ/y]
                  ϕ and ϕ[y/x] do not necessarily have the same
                  free variables (x vs y), thus while generating
                  new names, x (resp. y) could be generated in
                  one case, while it cannot in the other one
                
                  One option to solve this is to give a blacklist
                  to the substitution, which additional variables
                  should be avoided. Proof system could work with
                  any blacklist.
                *)
             --
          ** 
  Defined.

  (* until here *)
  Lemma alpha_exists Γ ϕ x y :
    named_well_formed ϕ = true ->
    y ∉ named_evars ϕ ->
    Γ ⊢N npatt_imp (npatt_exists x ϕ) (npatt_exists y (rename_free_evar ϕ y x)).
  Proof.
    intros Hwf HIn.
    apply N_Ex_gen; simpl. assumption.
    by apply named_well_formed_rename.
    2: { pose proof (named_free_evars_rename ϕ x y). set_solver. }
    replace ϕ with (rename_free_evar ϕ x x) at 1. 2: by rewrite rename_free_evar_same.
    rewrite -(rename_free_evar_chain _ x y x). assumption.
    apply N_Ex_quan.
  Defined.

  Lemma alpha_exists_reverse Γ ϕ x y :
    named_well_formed ϕ = true ->
    y ∉ named_evars ϕ ->
    Γ ⊢N npatt_imp (npatt_exists y (rename_free_evar ϕ y x)) (npatt_exists x ϕ).
  Proof.
    intros Hwf HIn.
    apply N_Ex_gen; simpl. 2: assumption.
    by apply named_well_formed_rename.
    2: { pose proof named_free_evars_subseteq_named_evars. set_solver. }
    apply N_Ex_quan.
  Defined.

  Lemma alpha_mu Γ ϕ X Y :
    named_well_formed ϕ = true ->
    Y ∉ named_svars ϕ ->
    Γ ⊢N npatt_imp (npatt_mu X ϕ) (npatt_mu Y (rename_free_svar ϕ Y X)).
  Proof.
    intros Hwf HIn.
    apply N_Knaster_tarski.
    pose proof N_Pre_fixp.
  Defined.

  Lemma alpha_mu_reverse Γ ϕ X Y :
    named_well_formed ϕ = true ->
    Y ∉ named_svars ϕ ->
    Γ ⊢N npatt_imp (npatt_mu Y (rename_free_svar ϕ Y X)) (npatt_mu X ϕ).
  Proof.
    intros Hwf HIn.

  Defined.


End named_proof_system.
