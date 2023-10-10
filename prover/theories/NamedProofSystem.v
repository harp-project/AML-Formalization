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
      named_well_formed (npatt_mu X phi) = true ->
      theory ⊢N npatt_imp (standard_svar_subst phi X (npatt_mu X phi)) (npatt_mu X phi)

  (* Knaster-Tarski *)
  | N_Knaster_tarski (phi psi : NamedPattern) (X : svar) :
      named_well_formed (npatt_mu X phi) = true ->
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
    * destruct IHϕ. cbn. case_match. reflexivity. apply H.
    * destruct IHϕ. cbn. case_match. reflexivity. apply H0.
  Defined.

  Lemma svar_occurrences_rename_different ϕ :
    (forall X x y, X <> y -> X <> x -> named_no_negative_occurrence X (rename_free_svar ϕ x y) = named_no_negative_occurrence X ϕ) /\
    (forall X x y, X <> y -> X <> x -> named_no_positive_occurrence X (rename_free_svar ϕ x y) = named_no_positive_occurrence X ϕ).
  Proof.
    induction ϕ; split; intros X0 x0 y0 Hxy1 Hxy2; simpl; try reflexivity.
    * case_match; reflexivity.
    * case_match; try reflexivity. subst. cbn.
      case_match. congruence. case_match. congruence. reflexivity.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H; auto. rewrite H1; auto.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H0; auto. rewrite H2; auto.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H1; auto.
      unfold named_no_positive_occurrence in H0. rewrite H0; auto.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H2; auto.
      unfold named_no_negative_occurrence in H. rewrite H; auto.
    * destruct IHϕ. apply H; auto.
    * destruct IHϕ. apply H0; auto.
    * case_match. reflexivity. destruct IHϕ. cbn. case_match. reflexivity. apply H0; auto.
    * case_match. reflexivity. destruct IHϕ. cbn. case_match. reflexivity. apply H1; auto.
  Defined.

  Lemma no_occurence_of_nonfree_svar :
    forall ϕ x, x ∉ named_free_svars ϕ ->
      named_no_negative_occurrence x ϕ = true /\
      named_no_positive_occurrence x ϕ = true.
  Proof.
    induction ϕ; intros x0 Hin; cbn; split; try reflexivity; auto.
    * case_match; auto. set_solver.
    * rewrite (proj1 (IHϕ1 _ _)). set_solver.
      rewrite (proj1 (IHϕ2 _ _)). set_solver.
      reflexivity.
    * rewrite (proj2 (IHϕ1 _ _)). set_solver.
      rewrite (proj2 (IHϕ2 _ _)). set_solver.
      reflexivity.
    * unfold named_no_positive_occurrence in IHϕ1.
      rewrite (proj2 (IHϕ1 _ _)). set_solver.
      rewrite (proj1 (IHϕ2 _ _)). set_solver.
      reflexivity.
    * unfold named_no_negative_occurrence in IHϕ1.
      rewrite (proj1 (IHϕ1 _ _)). set_solver.
      rewrite (proj2 (IHϕ2 _ _)). set_solver.
      reflexivity.
    * apply IHϕ. set_solver.
    * apply IHϕ. set_solver.
    * case_match; auto.
      apply IHϕ. set_solver.
    * case_match; auto.
      apply IHϕ. set_solver.
  Defined.

  Lemma svar_occurrences_rename_same ϕ :
    (forall y x, x ∉ named_svars ϕ -> named_no_negative_occurrence x (rename_free_svar ϕ x y) = named_no_negative_occurrence y ϕ) /\
    (forall y x, x ∉ named_svars ϕ -> named_no_positive_occurrence x (rename_free_svar ϕ x y) = named_no_positive_occurrence y ϕ).
  Proof.
    induction ϕ; split; intros y0 x0 Hin; simpl; try reflexivity; unfold named_svars in Hin. 
    * case_match; reflexivity.
    * case_match; try reflexivity. subst. cbn.
      do 2 case_match; auto. congruence.
      cbn. do 2 case_match; auto. 2: congruence. set_solver.
    * destruct IHϕ1, IHϕ2. cbn.
      rewrite H; auto. unfold named_svars. set_solver. rewrite H1; auto.
      unfold named_svars. set_solver.
    * destruct IHϕ1, IHϕ2. cbn.
      rewrite H0; auto. unfold named_svars. set_solver. rewrite H2; auto. unfold named_svars. set_solver.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H1; auto. unfold named_svars. set_solver.
      unfold named_no_positive_occurrence in H0. rewrite H0; auto. unfold named_svars. set_solver.
    * destruct IHϕ1, IHϕ2. cbn. rewrite H2; auto. unfold named_svars. set_solver.
      unfold named_no_negative_occurrence in H. rewrite H; auto. unfold named_svars. set_solver.
    * destruct IHϕ. apply H; auto.
    * destruct IHϕ. apply H0; auto.
    * case_match.
      - subst. rewrite (proj1 (no_occurence_of_nonfree_svar _ _ _)).
        set_solver. cbn. case_match; auto. congruence.
      - destruct IHϕ. cbn.
        case_match. set_solver. case_match. set_solver.
        apply H0; auto. simpl in Hin. unfold named_svars.  
        clear -Hin. apply not_elem_of_union; split.
        2: set_solver. apply not_elem_of_union in Hin as [P1 P2].
        set_solver.
    * case_match.
      - subst. rewrite (proj2 (no_occurence_of_nonfree_svar _ _ _)).
        set_solver. cbn. case_match; auto. congruence.
      - destruct IHϕ. cbn.
        case_match. set_solver. case_match. set_solver.
        apply H1; auto. simpl in Hin. unfold named_svars.  
        clear -Hin. apply not_elem_of_union; split.
        2: set_solver. apply not_elem_of_union in Hin as [P1 P2].
        set_solver.
  Defined.

  Lemma named_well_formed_rename_evar ϕ x y:
    named_well_formed ϕ = true ->
    named_well_formed (rename_free_evar ϕ x y) = true.
  Proof.
    induction ϕ; intros Wf; simpl in *; auto.
    * case_match; auto.
    * case_match; auto.
    * rewrite IHϕ; auto.
      rewrite (proj1 (evar_occurrences_rename _)). auto.
  Defined.

  Lemma named_well_formed_rename_svar ϕ X Y:
    X ∉ named_bound_svars ϕ ->
    named_well_formed ϕ = true ->
    named_well_formed (rename_free_svar ϕ X Y) = true.
  Proof.
    induction ϕ; intros Hn Wf; simpl in *; auto.
    * case_match; auto.
    * rewrite IHϕ1. set_solver. auto. rewrite IHϕ2. set_solver. auto.
      reflexivity.
    * rewrite IHϕ1. set_solver. auto. rewrite IHϕ2. set_solver. auto.
      reflexivity.
    * case_match; auto. simpl. rewrite IHϕ; auto. set_solver.
      rewrite (proj1 (svar_occurrences_rename_different _)); auto.
      set_solver.
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

  Lemma standard_svar_subst_fold ϕ ψ X Y :
    Y ∉ named_svars ϕ ->
    named_bound_svars ϕ ## named_free_svars ψ ->
    standard_svar_subst ϕ X ψ = standard_svar_subst (rename_free_svar ϕ Y X) Y ψ.
  Proof.
    revert X Y ψ.
    induction ϕ; intros X0 Y0 ψ Hin Hdis; simpl; simp standard_svar_subst; try reflexivity.
    * case_match; simpl; simp standard_svar_subst.
      - destruct (decide (Y0 = Y0)); simpl. reflexivity. congruence.
      - simpl in Hin. destruct (decide (Y0 = X)); simpl.
        unfold named_svars in Hin. set_solver.
        reflexivity.
    * erewrite IHϕ1. erewrite IHϕ2. reflexivity.
      all: unfold named_svars in *; set_solver.
    * erewrite IHϕ1. erewrite IHϕ2. reflexivity.
      all: unfold named_svars in *; set_solver.
    * erewrite IHϕ. reflexivity.
      all: unfold named_svars in *; set_solver.
    * destruct (decide (X0 = X)); simpl.
      - rewrite standard_evar_subst_id.
        pose proof (named_free_svars_subseteq_named_svars (npatt_mu X0 ϕ)). set_solver. reflexivity.
      - subst. simp standard_svar_subst.
        destruct (decide (Y0 = X)).
        + subst. unfold named_svars in *. set_solver.
        + simpl.
          destruct (decide (X ∈ named_free_svars ψ ∧ X0 ∈ named_free_svars ϕ)); simpl.
          ** destruct a as [Ha1 Ha2]. set_solver.
          ** destruct decide.
             set_solver.
             simpl.
             erewrite IHϕ. reflexivity. all: unfold named_svars in *; set_solver. 
  Defined.

  (* until here *)
  Lemma alpha_exists Γ ϕ x y :
    named_well_formed ϕ = true ->
    y ∉ named_evars ϕ ->
    Γ ⊢N npatt_imp (npatt_exists x ϕ) (npatt_exists y (rename_free_evar ϕ y x)).
  Proof.
    intros Hwf HIn.
    apply N_Ex_gen; simpl. assumption.
    by apply named_well_formed_rename_evar.
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
    by apply named_well_formed_rename_evar.
    2: { pose proof named_free_evars_subseteq_named_evars. set_solver. }
    apply N_Ex_quan.
  Defined.

  Lemma alpha_mu Γ ϕ X Y :
    named_well_formed (npatt_mu X ϕ) = true ->
    Y ∉ named_svars ϕ ->
    named_bound_svars ϕ ## named_free_svars ϕ ->
    Γ ⊢N npatt_imp (npatt_mu X ϕ) (npatt_mu Y (rename_free_svar ϕ Y X)).
  Proof.
    intros Hwf Hin Hdis.
    apply N_Knaster_tarski. assumption.
    rewrite (standard_svar_subst_fold ϕ _ X Y).
    * assumption.
    * simpl. pose proof named_free_svars_rename ϕ X Y.
      clear -H Hdis. set_solver.
    * apply N_Pre_fixp.
      simpl in *. rewrite named_well_formed_rename_svar. set_solver. auto.
      rewrite (proj1 (svar_occurrences_rename_same _)); auto.
  Defined.

  Lemma alpha_mu_reverse Γ ϕ X Y :
    named_well_formed (npatt_mu X ϕ) = true ->
    Y ∉ named_svars ϕ ->
    named_bound_svars ϕ ## named_free_svars ϕ ->
    Γ ⊢N npatt_imp (npatt_mu Y (rename_free_svar ϕ Y X)) (npatt_mu X ϕ).
  Proof.
    intros Hwf HIn Hdis.
    apply N_Knaster_tarski. simpl in *.
    rewrite (proj1 (svar_occurrences_rename_same _)); auto.
    rewrite named_well_formed_rename_svar; auto. set_solver.
    rewrite -standard_svar_subst_fold.
    * assumption.
    * simpl. pose proof named_free_svars_rename. set_solver.
    * apply N_Pre_fixp. auto.
  Defined.

End named_proof_system.

Module Notations.

Notation "theory ⊢N pattern" := (NP_ML_proof_system theory pattern) (at level 76).

End Notations.

Section translation.

Context {Σ : Signature}.

(* This function does not work for ill-formed patterns, for example:
  0 ---> ex , 1  ==> x ---> ex x, y

  Moreover, it does not satisfy the requirements of
  alpha_mu and alpha_mu_reverse!
*)
(* Equations? translate_pattern (evs : EVarSet) (svs : SVarSet) (ϕ : Pattern) : NamedPattern by wf (size' ϕ) lt :=
  translate_pattern _ _ patt_bott := npatt_bott;
  translate_pattern _ _ (patt_sym s) := npatt_sym s;
  translate_pattern evs _ (patt_bound_evar n) :=
    match (last (evar_fresh_seq evs (S n))) with
    | Some x => npatt_evar x
    | None => npatt_evar (evar_fresh (elements evs)) (* This can never occur due to S n *)
    end;
  translate_pattern _ _ (patt_free_evar x) := npatt_evar x;
  translate_pattern _ svs (patt_bound_svar N) :=
    match (last (svar_fresh_seq svs (S N))) with
    | Some X => npatt_svar X
    | None => npatt_svar (svar_fresh (elements svs)) (* This can never occur due to S n *)
    end;
  translate_pattern _ _ (patt_free_svar X) := npatt_svar X;
  translate_pattern evs svs (patt_imp ϕ₁ ϕ₂) := 
    npatt_imp (translate_pattern evs svs ϕ₁) (translate_pattern evs svs ϕ₂);
  translate_pattern evs svs (patt_app ϕ₁ ϕ₂) :=
    npatt_app (translate_pattern evs svs ϕ₁) (translate_pattern evs svs ϕ₂);
  translate_pattern evs svs (patt_exists ϕ) :=
    let freshx := evar_fresh (elements evs) in
      npatt_exists freshx (translate_pattern ({[freshx]} ∪ evs) svs (evar_open freshx 0 ϕ));
  translate_pattern evs svs (patt_mu ϕ) :=
    let freshX := svar_fresh (elements svs) in
      npatt_mu freshX (translate_pattern evs ({[freshX]} ∪ svs) (svar_open freshX 0 ϕ)).
Proof.
  1-4: simpl; try lia.
  simpl. rewrite evar_open_size'. lia.
  simpl. rewrite svar_open_size'. lia.
Defined. *)

(*
  To fix the previous definition, we need to make sure, that the variables
  we generate for dangling indices are different from bound variables

  -->

  we parametherise the function with existential and mu-depths.
  We decrease this depth in the recursive calls
  to ensure that the dangling variables get names consistently

  Drawback: we have to have a property that the nats given to the function
  are at least as big as the depth of the pattern
*)
Equations? translate_pattern (evs : EVarSet) (svs : SVarSet) (ed sd : nat) (ϕ : Pattern) : NamedPattern by wf (size' ϕ) lt :=
  translate_pattern _ _ ed sd patt_bott := npatt_bott;
  translate_pattern _ _ ed sd (patt_sym s) := npatt_sym s;
  translate_pattern evs _ ed sd (patt_bound_evar n):=
    match (last (evar_fresh_seq evs (S ed + n))) with
    | Some x => npatt_evar x
    | None => npatt_evar (evar_fresh (elements evs)) (* This can never occur due to S n *)
    end;
  translate_pattern _ _ ed sd (patt_free_evar x) := npatt_evar x;
  translate_pattern _ svs ed sd (patt_bound_svar N) :=
    match (last (svar_fresh_seq svs (S sd + N))) with
    | Some X => npatt_svar X
    | None => npatt_svar (svar_fresh (elements svs)) (* This can never occur due to S n *)
    end;
  translate_pattern _ _ ed sd (patt_free_svar X) := npatt_svar X;
  translate_pattern evs svs ed sd (patt_imp ϕ₁ ϕ₂) := 
    npatt_imp (translate_pattern evs svs ed sd ϕ₁) (translate_pattern evs svs ed sd ϕ₂);
  translate_pattern evs svs ed sd (patt_app ϕ₁ ϕ₂) :=
    npatt_app (translate_pattern evs svs ed sd ϕ₁) (translate_pattern evs svs ed sd ϕ₂);
  translate_pattern evs svs ed sd (patt_exists ϕ) :=
    let freshx := evar_fresh (elements evs) in
      npatt_exists freshx (translate_pattern ({[freshx]} ∪ evs) svs (pred ed) sd (evar_open freshx 0 ϕ));
  translate_pattern evs svs ed sd (patt_mu ϕ) :=
    let freshX := svar_fresh (elements svs) in
      npatt_mu freshX (translate_pattern evs ({[freshX]} ∪ svs) ed (pred sd) (svar_open freshX 0 ϕ)).
Proof.
  1-4: simpl; try lia.
  simpl. rewrite evar_open_size'. lia.
  simpl. rewrite svar_open_size'. lia.
Defined.

Lemma translate_pattern_avoids_evar_blacklist :
  forall ϕ evs svs ed sd,
    named_bound_evars (translate_pattern evs svs ed sd ϕ) ## evs.
Proof.
  intros ϕ. remember (size' ϕ) as s.
  assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
  induction s; intros ϕ Hsize evs svs ed sd; destruct ϕ; simpl in Hsize; try lia.
  all: simp translate_pattern; simpl.
  1-2, 5, 7: set_solver.
  * case_match. 2: { apply last_None in H. congruence. }
    simpl. set_solver.
  * case_match. 2: { apply last_None in H. congruence. }
    simpl. set_solver.
  * pose proof (IH1 := IHs ϕ1 ltac:(lia) evs svs).
    pose proof (IH2 := IHs ϕ2 ltac:(lia) evs svs).
    set_solver.
  * pose proof (IH1 := IHs ϕ1 ltac:(lia) evs svs).
    pose proof (IH2 := IHs ϕ2 ltac:(lia) evs svs).
    set_solver.
  * specialize (IHs (evar_open (evar_fresh (elements evs)) 0 ϕ)).
    rewrite evar_open_size' in IHs.
    specialize (IHs ltac:(lia) ({[evar_fresh (elements evs)]} ∪ evs) svs (pred ed) sd).
    remember (named_bound_evars _) as A. clear HeqA.
    pose proof (Hfresh := set_evar_fresh_is_fresh' evs). set_solver.
  * specialize (IHs (svar_open (svar_fresh (elements svs)) 0 ϕ)).
    rewrite svar_open_size' in IHs.
    specialize (IHs ltac:(lia) evs ({[svar_fresh (elements svs)]} ∪ svs) ed (pred sd)).
    set_solver.
Defined.

Lemma translate_pattern_avoids_svar_blacklist :
  forall ϕ evs svs ed sd,
    named_bound_svars (translate_pattern evs svs ed sd ϕ) ## svs.
Proof.
  intros ϕ. remember (size' ϕ) as s.
  assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
  induction s; intros ϕ Hsize evs svs ed sd; destruct ϕ; simpl in Hsize; try lia.
  all: simp translate_pattern; simpl.
  1-2, 5, 7: set_solver.
  * case_match. 2: { apply last_None in H. congruence. }
    simpl. set_solver.
  * case_match. 2: { apply last_None in H. congruence. }
    simpl. set_solver.
  * pose proof (IH1 := IHs ϕ1 ltac:(lia) evs svs).
    pose proof (IH2 := IHs ϕ2 ltac:(lia) evs svs).
    set_solver.
  * pose proof (IH1 := IHs ϕ1 ltac:(lia) evs svs).
    pose proof (IH2 := IHs ϕ2 ltac:(lia) evs svs).
    set_solver.
  * specialize (IHs (evar_open (evar_fresh (elements evs)) 0 ϕ)).
    rewrite evar_open_size' in IHs.
    specialize (IHs ltac:(lia) ({[evar_fresh (elements evs)]} ∪ evs) svs (pred ed) sd).
    set_solver.
  * specialize (IHs (svar_open (svar_fresh (elements svs)) 0 ϕ)).
    rewrite svar_open_size' in IHs.
    specialize (IHs ltac:(lia) evs ({[svar_fresh (elements svs)]} ∪ svs) ed (pred sd)).
    remember (named_bound_svars _) as A. clear HeqA.
    pose proof (Hfresh := set_svar_fresh_is_fresh' svs). set_solver.
Defined.

Lemma occurrences_to_named :
  forall ϕ n X evs svs ed sd,
    X ∈ svs ->
    X ∉ free_svars ϕ ->
    (no_negative_occurrence_db_b n ϕ = true ->
    named_no_negative_occurrence X (translate_pattern evs svs ed sd(svar_open X n ϕ)) = true)
    /\
    (no_positive_occurrence_db_b n ϕ = true ->
    named_no_positive_occurrence X (translate_pattern evs svs ed sd (svar_open X n ϕ)) = true).
Proof.
  intros ϕ. remember (size' ϕ) as s.
  assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
  induction s; intros ϕ Hsize m Y evs svs ed sd Hin Hin2; destruct ϕ; simpl in Hsize; try lia; split; cbn; intros Hwf; simp translate_pattern; simpl; auto.
  * cbn. case_match; auto. cbn in Hin. set_solver. 
  * case_match. 2: { by apply last_None in H. } reflexivity.
  * case_match. 2: { by apply last_None in H. } reflexivity.
  * case_match; simp translate_pattern; (case_match; [|by apply last_None in H0]); reflexivity.
  * case_match. congruence.
    case_match. 2: congruence.
    - simp translate_pattern. case_match. 2: by apply last_None in H1.
      cbn. case_match; auto.
      subst. pose proof (svar_fresh_seq_disj svs (S sd + n)).
      apply last_Some_elem_of in H1. clear -H3 H1 Hin. set_solver.
    - simp translate_pattern. case_match. 2: by apply last_None in H1.
      cbn. case_match; auto.
      subst. pose proof (svar_fresh_seq_disj svs (S sd + pred n)).
      apply last_Some_elem_of in H1. clear -H3 H1 Hin. set_solver.
  * cbn in *. rewrite (proj1 (IHs ϕ1 ltac:(lia) _ _ _ _ _ _ _ _)); auto. set_solver.
    rewrite (proj1 (IHs ϕ2 ltac:(lia) _ _ _ _ _ _ _ _)); auto. set_solver.
  * cbn in *. rewrite (proj2 (IHs ϕ1 ltac:(lia) _ _ _ _ _ _ _ _)); auto. set_solver.
    rewrite (proj2 (IHs ϕ2 ltac:(lia) _ _ _ _ _ _ _ _)); auto. set_solver.
  * cbn in *.
    rewrite (proj1 (IHs ϕ2 ltac:(lia) _ _ _ _ _ _ _ _)); auto. set_solver.
    rewrite andb_true_r.
    apply andb_true_iff in Hwf as [Hwf _].
    epose proof (H := proj2 (IHs ϕ1 ltac:(lia) m Y evs svs _ _ _ _) Hwf).
    unfold named_no_positive_occurrence in H. unfold svar_open in H.
    unfold named_no_positive_occurrence, named_no_negative_occurrence in H.
    apply H.
  * cbn in *.
    rewrite (proj2 (IHs ϕ2 ltac:(lia) _ _ _ _ _ _ _ _)); auto. set_solver.
    rewrite andb_true_r.
    apply andb_true_iff in Hwf as [Hwf _].
    epose proof (H := proj1 (IHs ϕ1 ltac:(lia) m Y evs svs _ _ _ _) Hwf).
    unfold named_no_positive_occurrence in H. unfold svar_open in H.
    unfold named_no_positive_occurrence, named_no_negative_occurrence in H.
    apply H.
  * cbn in *. rewrite evar_open_bsvar_subst. wf_auto2. unfold svar_open in IHs.
    rewrite (proj1 (IHs (evar_open (evar_fresh (elements evs)) 0 ϕ) _ m Y ({[evar_fresh (elements evs)]} ∪ evs) svs (pred ed) sd _ _) _); auto.
    - rewrite evar_open_size'. lia.
    - now rewrite free_svars_evar_open.
    - now apply no_negative_occurrence_evar_open.
  * cbn in *. rewrite evar_open_bsvar_subst. wf_auto2. unfold svar_open in IHs.
    rewrite (proj2 (IHs (evar_open (evar_fresh (elements evs)) 0 ϕ) _ m Y ({[evar_fresh (elements evs)]} ∪ evs) svs (pred ed) sd _ _) _); auto.
    - rewrite evar_open_size'. lia.
    - now rewrite free_svars_evar_open.
    - now apply no_positive_occurrence_evar_open.
  * cbn in *. case_match; auto.
    rewrite svar_open_bsvar_subst_higher. wf_auto2. lia.
    simpl. unfold svar_open in IHs.
    rewrite (proj1 (IHs (svar_open (svar_fresh (elements svs)) 0 ϕ) _ m Y evs _ ed (pred sd) _ _) _); auto.
    - rewrite svar_open_size'. lia.
    - clear -Hin. set_solver.
    - pose proof (free_svars_svar_open ϕ (svar_fresh (elements svs)) 0) as H0.
      clear -n Hin2 H0. set_solver.
    - apply negative_occ_svar_open. lia. assumption.
  * cbn in *. case_match; auto.
    rewrite svar_open_bsvar_subst_higher. wf_auto2. lia.
    simpl. unfold svar_open in IHs.
    rewrite (proj2 (IHs (svar_open (svar_fresh (elements svs)) 0 ϕ) _ m Y evs _ ed (pred sd) _ _) _); auto.
    - rewrite svar_open_size'. lia.
    - clear -Hin. set_solver.
    - pose proof (free_svars_svar_open ϕ (svar_fresh (elements svs)) 0) as H0.
      clear -n Hin2 H0. set_solver.
    - apply positive_occ_svar_open. lia. assumption.
  Unshelve.
    all: auto.
    all: clear - Hin2; set_solver.
Defined.


Lemma well_formed_translate :
  forall ϕ evs svs ed sd, well_formed_positive ϕ = true ->
  free_evars ϕ ⊆ evs ->
  free_svars ϕ ⊆ svs ->
  named_well_formed (translate_pattern evs svs ed sd ϕ) = true.
Proof.
  intros ϕ. remember (size' ϕ) as s.
  assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
  induction s; destruct ϕ; simpl; try lia; intros Hs evs svs ed sd Hwf Hevs Hsvs;
  simp translate_pattern; cbn; auto.
  * case_match; reflexivity.
  * case_match; reflexivity.
  * rewrite IHs. lia. wf_auto2. 1-2: set_solver.
    rewrite IHs. lia. wf_auto2. 1-2: set_solver.
    reflexivity.
  * rewrite IHs. lia. wf_auto2. 1-2: set_solver.
    rewrite IHs. lia. wf_auto2. 1-2: set_solver.
    reflexivity.
  * rewrite IHs.
    - rewrite evar_open_size'. lia.
    - wf_auto2.
    - pose proof (free_evars_evar_open). clear -H Hevs. set_solver.
    - by rewrite free_svars_evar_open.
    - reflexivity.
  * rewrite IHs.
    - rewrite svar_open_size'. lia.
    - wf_auto2.
    - by rewrite free_evars_svar_open.
    - pose proof (free_svars_svar_open). clear -H Hsvs. set_solver.
    - remember (svar_fresh _) as XX. apply andb_true_iff in Hwf as [Hwf _].
      (* apply andb_true_iff in Hwf as [Hwf _]. *)
      rewrite (proj1 (occurrences_to_named _ _ _ _ _ _ _ _ _)).
      + clear. set_solver.
      + subst XX. pose proof (set_svar_fresh_is_fresh' svs) as H. clear -Hsvs H.
        set_solver.
      + assumption.
      + reflexivity.
Defined.

Lemma last_evar_seq_equal :
  forall n n' evs,
    last (evar_fresh_seq evs n) = last (evar_fresh_seq evs n')
  ->
    n = n'.
Proof.
  induction n; intros n' evs H; destruct n'; auto.
  * cbn in H. symmetry in H. by apply last_None in H.
  * cbn in H. by apply last_None in H.
  * f_equal. eapply (IHn _ ({[evar_fresh_s evs]} ∪ evs)). simpl in H.
    destruct evar_fresh_seq eqn:EQ.
    - destruct (evar_fresh_seq _ n') eqn:EQ2.
      + by [].
      + simpl in H. destruct last eqn:EQ3 in H. 2: congruence.
        apply last_Some_elem_of in EQ3.
        pose proof (evar_fresh_seq_disj ({[evar_fresh_s evs]} ∪ evs) n').
        inversion H. subst. rewrite EQ2 in H0.
        clear -H0 EQ3. apply disjoint_union_r in H0 as [H0 _].
        set_solver.
    - destruct (evar_fresh_seq _ n') eqn:EQ2.
      + simpl in H. destruct last eqn:EQ3 in H. 2: congruence.
        apply last_Some_elem_of in EQ3.
        pose proof (evar_fresh_seq_disj ({[evar_fresh_s evs]} ∪ evs) n).
        inversion H. subst. rewrite EQ in H0.
        clear -H0 EQ3. apply disjoint_union_r in H0 as [H0 _].
        set_solver.
      + by simpl in H.
Defined.

Lemma last_svar_seq_equal :
  forall n n' svs,
    last (svar_fresh_seq svs n) = last (svar_fresh_seq svs n')
  ->
    n = n'.
Proof.
  induction n; intros n' svs H; destruct n'; auto.
  * cbn in H. symmetry in H. by apply last_None in H.
  * cbn in H. by apply last_None in H.
  * f_equal. eapply (IHn _ ({[svar_fresh_s svs]} ∪ svs)). simpl in H.
    destruct svar_fresh_seq eqn:EQ.
    - destruct (svar_fresh_seq _ n') eqn:EQ2.
      + by [].
      + simpl in H. destruct last eqn:EQ3 in H. 2: congruence.
        apply last_Some_elem_of in EQ3.
        pose proof (svar_fresh_seq_disj ({[svar_fresh_s svs]} ∪ svs) n').
        inversion H. subst. rewrite EQ2 in H0.
        clear -H0 EQ3. apply disjoint_union_r in H0 as [H0 _].
        set_solver.
    - destruct (svar_fresh_seq _ n') eqn:EQ2.
      + simpl in H. destruct last eqn:EQ3 in H. 2: congruence.
        apply last_Some_elem_of in EQ3.
        pose proof (svar_fresh_seq_disj ({[svar_fresh_s svs]} ∪ svs) n).
        inversion H. subst. rewrite EQ in H0.
        clear -H0 EQ3. apply disjoint_union_r in H0 as [H0 _].
        set_solver.
      + by simpl in H.
Defined.

Lemma last_evar_fresh_is_first :
  forall n evs,
    last (evar_fresh_seq evs n) = Some (evar_fresh (elements evs)) -> n = 1.
Proof.
  destruct n; intros evs H; simpl in H; try congruence.
  destruct n.
  * reflexivity.
  * destruct evar_fresh_seq eqn:EQ.
    - simpl in EQ. congruence.
    - simpl in H. apply last_Some_elem_of in H.
      pose proof (evar_fresh_seq_disj ({[evar_fresh_s evs]} ∪ evs) (S n)).
      rewrite EQ in H0. clear EQ.
      apply disjoint_union_r in H0 as [H0 _]. set_solver.
Defined.


(* TODO: use depth for more efficiency!
   Instead of depth, we could use size *)
Lemma translate_rename :
  forall ϕ evs svs y n x ed sd, 
  well_formed_closed_ex_aux ϕ (S n) = true -> 
  free_evars ϕ ⊆ evs ->
  free_svars ϕ ⊆ svs ->
  ed ≥ size' ϕ ->
  sd ≥ size' ϕ ->
  last (evar_fresh_seq evs (S ed + n)) = Some x ->
  (* y ∉ free_evars ϕ -> *)
  y ∈ evs ->
  rename_free_evar (translate_pattern evs svs ed sd ϕ) y x = 
  translate_pattern evs svs ed sd (evar_open y n ϕ).
Proof.
  intros ϕ. remember (size' ϕ) as s.
  assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
  induction s; destruct ϕ; try lia; intros Hs evs svs y0 n0 x0 ed sd
    Hwf Hsub1 Hsub2 Hs1 Hs2 Hlast Hin2; simpl; simp translate_pattern; auto; simpl in Hs; try now lia.
  * cbn. case_match; simp translate_pattern.
    - subst. apply last_Some_elem_of in Hlast.
      pose proof (evar_fresh_seq_disj evs (S ed + n0)) as H0.
      clear -Hlast H0 Hsub1. set_solver.
    - reflexivity.
  * destruct (last (evar_fresh_seq evs (S ed + n))) eqn:EQ.
    2: by apply last_None in EQ.
    simpl. case_match; subst.
    - cbn. case_match; subst; simp translate_pattern; auto.
      + case_match.
        ** inversion EQ. (* TODO: is this okay? *)
           subst. rewrite <- H1 in Hlast. apply last_evar_seq_equal in Hlast.
           lia.
        ** congruence.
      + simpl in Hwf. case_match; lia.
    - cbn. case_match; simp translate_pattern; auto.
      + by rewrite EQ.
      + subst. congruence.
      + simpl in Hwf. case_match; lia.
  * destruct (last (svar_fresh_seq svs (S sd + n))) eqn:EQ.
    2: by apply last_None in EQ.
    cbn. simp translate_pattern. by rewrite EQ.
  * cbn. simp translate_pattern.
    erewrite IHs, IHs. reflexivity.
    all: auto; try lia; wf_auto2; set_solver.
  * cbn. simp translate_pattern.
    erewrite IHs, IHs. reflexivity.
    all: auto; try lia; wf_auto2; set_solver.
  * cbn. case_match; simp translate_pattern; cbn.
    - subst.
      assert (ed = 0). { 
        clear -Hlast.
        apply last_evar_fresh_is_first in Hlast. lia.
      }
      lia.
    - f_equal. rewrite evar_open_bevar_subst_higher. wf_auto2. lia.
      apply IHs.
      + rewrite evar_open_size'. lia.
      + simpl.
        apply wfc_ex_aux_bsvar_subst_le. lia. wf_auto2. wf_auto2.
      + pose proof (free_evars_evar_open ϕ (evar_fresh (elements evs)) 0).
        clear -H0 Hsub1. set_solver.
      + by rewrite free_svars_evar_open.
      + lia.
      + lia.
      + replace (S (pred ed) + pred (S n0)) with (ed + n0) by lia.
        clear -Hlast Hs1. destruct ed. lia. simpl in Hlast.
        assumption.
      + clear -Hin2. set_solver.
  * cbn. simp translate_pattern. cbn.
    rewrite svar_open_bevar_subst. wf_auto2.
    erewrite IHs. reflexivity. (* NOTE: for some reason, apply does not work *)
    - rewrite svar_open_size'. lia.
    - apply wfc_ex_aux_body_mu_imp1. wf_auto2.
    - by rewrite free_evars_svar_open.
    - pose proof (free_svars_svar_open ϕ (svar_fresh (elements svs)) 0).
      clear -H Hsub2. set_solver.
    - lia.
    - lia.
    - assumption.
    - assumption.
Defined.

Import MatchingLogic.ProofSystem.Notations_private
       Notations.

Variable Elem_class : Elements Pattern Theory.
Variable Finite_class : FinSet Pattern Theory.

(* Definition evars_of_Γ (Γ : Theory) := set_fold (fun pat acc => free_evars pat ∪ acc) ∅ Γ.
Definition svars_of_Γ (Γ : Theory) := set_fold (fun pat acc => free_svars pat ∪ acc) ∅ Γ. *)

(* TODO: undefine AC_free_evars!! *)
Print AC_free_evars.
Print free_evars_ctx.
Search free_evars_ctx.
Search AC_free_evars.

Check Knaster_tarski.

Fixpoint free_svars_ctx (C : Application_context) : SVarSet :=
match C with
| box => ∅
| ctx_app_l cc p _ => free_svars_ctx cc ∪ free_svars p
| ctx_app_r p cc _ => free_svars p ∪ free_svars_ctx cc
end.

Print ML_proof_system.

(* TODO: use depth and max instead of size and +! *)
Fixpoint vars_of_proof {Γ : Theory} {φ : Pattern} (p : Γ ⊢H φ) : EVarSet * SVarSet * nat :=
match p with
 | hypothesis _ phi x x0 => (free_evars phi, free_svars phi, size' phi)

 | P1 _ phi psi x x0 =>
   (free_evars phi ∪ free_evars psi, free_svars phi ∪ free_svars psi,
    size' (patt_imp phi (patt_imp psi phi)))

 | P2 _ phi psi xi x x0 x1 =>
   (free_evars phi ∪ free_evars psi ∪ free_evars xi,
    free_svars phi ∪ free_svars psi ∪ free_svars xi,
    size' (patt_imp (patt_imp phi (patt_imp psi xi))
                      (patt_imp (patt_imp phi psi) (patt_imp phi xi))))

 | P3 _ phi x => (free_evars phi, free_svars phi, size' (patt_imp (patt_imp (patt_imp phi patt_bott) patt_bott) phi))

 | Modus_ponens _ phi1 phi2 pf1 pf2 =>
   match vars_of_proof pf1, vars_of_proof pf2 with
   | (evs1, svs1, size1), (evs2, svs2, size2) =>
   (free_evars phi1 ∪ free_evars phi2 ∪ evs1 ∪ evs2,
    free_svars phi1 ∪ free_svars phi2 ∪ svs1 ∪ svs2,
    size' (patt_imp phi1 phi2) + size1 + size2)
   end

 | Ex_quan _ phi y x => ({[y]} ∪ free_evars phi, free_svars phi, size' (patt_imp (instantiate (patt_exists phi) (patt_free_evar y))
                       (patt_exists phi)))

 | Ex_gen _ phi1 phi2 x x0 x1 pf x3 =>
   match vars_of_proof pf with
   | (evs, svs, size1) =>
   ({[x]} ∪ free_evars phi1 ∪ free_evars phi2 ∪ evs, 
    free_svars phi1 ∪ free_svars phi2 ∪ svs,
    size' (patt_imp (exists_quantify x phi1) phi2) + size1)
   end

 | Prop_bott_left _ phi x => (free_evars phi, free_svars phi, size' (patt_imp (patt_app patt_bott phi) patt_bott))

 | Prop_bott_right _ phi x => (free_evars phi, free_svars phi, size' (patt_imp (patt_app phi patt_bott) patt_bott))

 | Prop_disj_left _ phi1 phi2 psi x x0 x1 =>
    (free_evars phi1 ∪ free_evars phi2 ∪ free_evars psi,
     free_svars phi1 ∪ free_svars phi2 ∪ free_svars psi,
     size' (patt_imp
                                  (patt_app
                                     (DerivedOperators_Syntax.patt_or phi1 phi2)
                                     psi)
                                  (DerivedOperators_Syntax.patt_or
                                     (patt_app phi1 psi) 
                                     (patt_app phi2 psi))))

 | Prop_disj_right _ phi1 phi2 psi x x0 x1 =>
    (free_evars phi1 ∪ free_evars phi2 ∪ free_evars psi,
     free_svars phi1 ∪ free_svars phi2 ∪ free_svars psi,
     size' (patt_imp
                                   (patt_app psi
                                      (DerivedOperators_Syntax.patt_or phi1 phi2))
                                   (DerivedOperators_Syntax.patt_or
                                      (patt_app psi phi1) 
                                      (patt_app psi phi2))))

 | Prop_ex_left _ phi psi x x0 =>
   (free_evars phi ∪ free_evars psi, free_svars phi ∪ free_svars psi,
   size' (patt_imp (patt_app (patt_exists phi) psi)
                              (patt_exists (patt_app phi psi))))

 | Prop_ex_right _ phi psi x x0 =>
   (free_evars phi ∪ free_evars psi, free_svars phi ∪ free_svars psi,
    size' (patt_imp (patt_app psi (patt_exists phi))
                               (patt_exists (patt_app psi phi))))

 | Framing_left _ phi1 phi2 psi x pf =>
   match vars_of_proof pf with
   | (evs, svs, size1) =>
   (free_evars phi1 ∪ free_evars phi2 ∪ free_evars psi ∪ evs,
    free_svars phi1 ∪ free_svars phi2 ∪ free_svars psi ∪ svs,
    size' (patt_imp (patt_app phi1 psi) (patt_app phi2 psi)) + size1)
   end

 | Framing_right _ phi1 phi2 psi x pf =>
   match vars_of_proof pf with
   | (evs, svs, size1) =>
   (free_evars phi1 ∪ free_evars phi2 ∪ free_evars psi ∪ evs,
    free_svars phi1 ∪ free_svars phi2 ∪ free_svars psi ∪ svs,
    size' (patt_imp (patt_app psi phi1) (patt_app psi phi2)) + size1)
   end

 | Svar_subst _ phi psi X x x0 pf =>
   match vars_of_proof pf with
   | (evs, svs, size1) =>
   (free_evars phi ∪ free_evars psi ∪ evs,
    {[X]} ∪ free_svars phi ∪ free_svars psi ∪ svs,
    size' psi + size' (free_svar_subst psi X phi) + size1)
   end

 | Pre_fixp _ phi x =>
   (free_evars phi, free_svars phi, 
    size' (patt_imp (instantiate (patt_mu phi) (patt_mu phi)) (patt_mu phi)))

 | Knaster_tarski _ phi psi x pf =>
   match vars_of_proof pf with
   | (evs, svs, size1) =>
   (free_evars phi ∪ free_evars psi ∪ evs,
    free_svars phi ∪ free_svars psi ∪ svs,
    size' (patt_imp (instantiate (patt_mu phi) psi) psi) + size1)
   end

 | Existence _ => (empty, empty, 2)

 | Singleton_ctx _ C1 C2 phi x x0 =>
   ({[x]} ∪ free_evars phi ∪ free_evars_ctx C1 ∪ free_evars_ctx C2,
    free_svars phi ∪ free_svars_ctx C1 ∪ free_svars_ctx C2,
    size' (DerivedOperators_Syntax.patt_not
                             (DerivedOperators_Syntax.patt_and
                                (subst_ctx C1
                                   (DerivedOperators_Syntax.patt_and
                                      (patt_free_evar x) phi))
                                (subst_ctx C2
                                   (DerivedOperators_Syntax.patt_and
                                      (patt_free_evar x)
                                      (DerivedOperators_Syntax.patt_not phi))))))
end.
(* 
Lemma last_exists :
  forall (n : nat) (evs : EVarSet),
  last (evar_fresh_seq evs (S n)) = Some (evar_fresh (elements (iterate (fun x:EVarSet => {[evar_fresh (elements x)]} ∪ x) n evs))).
Proof.
  induction n; intros evs; simpl.
  * reflexivity.
  * rewrite IHn.
    
Defined. *)

Lemma last_exists :
  forall (n : nat) (evs : EVarSet),
  last (evar_fresh_seq evs (S n)) = Some (nth n (evar_fresh_seq evs (S n)) (evar_fresh [])).
Proof.
  induction n; intros evs.
  * simpl. reflexivity.
  * destruct n; simpl.
    - reflexivity.
    - rewrite -IHn. reflexivity.
Defined.

Theorem named_free_evars_translate :
  forall φ n ed sd evs svs,
    well_formed_closed_ex_aux φ n = true ->
    ed ≥ size' φ ->
    named_free_evars (translate_pattern evs svs ed sd φ) ⊆
    free_evars φ ∪ (list_to_set (evar_fresh_seq evs (ed + n)) ∖ list_to_set (evar_fresh_seq evs ed)).
Proof.
  intros φ. remember (size' φ) as s.
  assert (size' φ <= s) by lia. clear Heqs. revert φ H.
  induction s; destruct φ; try lia; intros Hs level ed sd evs svs Hwf Hsize; cbn; simp translate_pattern; auto; simpl in Hs; try now lia.
  * cbn. set_solver.
  * cbn. set_solver.
  * case_match. 2: by apply last_None in H.
    cbn. simpl in Hwf. case_match. 2: congruence.
    clear IHs Hs H0 Hwf Hsize svs. revert n level evs l H.
    induction ed; intros; simpl.
    - pose proof (inclusion_evar_seq (1 + n) (level) evs ltac:(lia)).
      apply last_Some_elem_of in H. set_solver.
    - replace (last (evar_fresh_seq evs (S (S ed) + n))) with
              (last (evar_fresh_seq ({[evar_fresh (elements evs)]} ∪ evs) ((S ed) + n))) in H by reflexivity.
      eapply (IHed _ level) in H. 2: lia.
      pose proof (evar_fresh_seq_disj ({[evar_fresh (elements evs)]} ∪ evs) (ed + level)).
      set_solver.
  * case_match. 2: by apply last_None in H.
    cbn. set_solver.
  * cbn. set_solver.
  * cbn.
    specialize (IHs φ1 ltac:(lia) level ed sd evs svs ltac:(wf_auto2) ltac:(lia)) as Hp1.
    specialize (IHs φ2 ltac:(lia) level ed sd evs svs ltac:(wf_auto2) ltac:(lia)) as Hp2.
    clear -Hp1 Hp2. set_solver.
  * cbn. set_solver.
  * cbn.
    specialize (IHs φ1 ltac:(lia) level ed sd evs svs ltac:(wf_auto2) ltac:(lia)) as Hp1.
    specialize (IHs φ2 ltac:(lia) level ed sd evs svs ltac:(wf_auto2) ltac:(lia)) as Hp2.
    clear -Hp1 Hp2. set_solver.
  * cbn.
    epose proof (IHs (evar_open (evar_fresh (elements evs)) 0 φ) _ level (pred ed) sd ({[evar_fresh (elements evs)]} ∪ evs) svs ltac:(wf_auto2) ltac:(lia)) as Hp.
    remember (named_free_evars _) as NF.
    pose proof (free_evars_evar_open φ (evar_fresh (elements evs)) 0).
    destruct ed. lia. simpl in *.
    clear -Hp H.
    assert (NF ⊆ {[evar_fresh (elements evs)]} ∪ free_evars φ ∪
      list_to_set
           (evar_fresh_seq ({[evar_fresh (elements evs)]} ∪ evs) (ed + level))
         ∖ list_to_set (evar_fresh_seq ({[evar_fresh (elements evs)]} ∪ evs) ed)) by set_solver.
    clear Hp H. set_solver.
  Unshelve.
    rewrite evar_open_size'. lia.
    apply wfc_ex_aux_bsvar_subst_le; auto. lia.
  * cbn.
    epose proof (IHs (svar_open (svar_fresh (elements svs)) 0 φ) _ level ed (pred sd) evs ({[svar_fresh (elements svs)]} ∪ svs) ltac:(wf_auto2) ltac:(lia)) as Hp.
    remember (named_free_evars _) as NF.
    now rewrite (free_evars_svar_open φ 0 (svar_fresh (elements svs))) in Hp.
  Unshelve.
    rewrite svar_open_size'. lia.
Defined.

Notation "A --->ₙ B" := (npatt_imp A B) (at level 75, right associativity).

Lemma n_A_impl_A Γ A :
  named_well_formed A = true ->
  Γ ⊢N (A --->ₙ A).
Proof. 
  intros WFA.
  epose proof (_1 := N_P2 Γ A (A --->ₙ A) A _ _ _).
  epose proof (_2 := N_P1 Γ A (A --->ₙ A) _ _).
  epose proof (_3 := N_Modus_ponens _ _ _ _ _ _2 _1).
  epose proof (_4 := N_P1 Γ A A _ _).
  epose proof (_5 := N_Modus_ponens _ _ _ _ _ _4 _3).
  exact _5.
  Unshelve.
  all: simpl; by rewrite WFA.
Defined.

Lemma n_reorder Γ A B C :
  named_well_formed A = true ->
  named_well_formed B = true ->
  named_well_formed C = true ->
  Γ ⊢N ((A --->ₙ B --->ₙ C) --->ₙ ( B --->ₙ A --->ₙ C)).
Proof.
  intros Hwf1 Hwf2 Hwf3.
  epose (t1 := (N_Modus_ponens _ _ _ _ _
                  (N_P1 Γ ((A --->ₙ B) --->ₙ A --->ₙ C) B _ _)
                  (N_P1 Γ (((A --->ₙ B) --->ₙ A --->ₙ C) --->ₙ B --->ₙ (A --->ₙ B) --->ₙ A --->ₙ C) (A --->ₙ B --->ₙ C) _ _))).

  pose(ABC := (A --->ₙ B --->ₙ C)).

  eapply N_Modus_ponens. 1-2: shelve.
  - eapply N_Modus_ponens. 1-2: shelve.
    + apply(N_P1 _ B A). 1-2: shelve.
    + apply(N_P1 _ (B --->ₙ A --->ₙ B) (A --->ₙ B --->ₙ C)). 1-2: shelve.
  - eapply N_Modus_ponens. 1-2: shelve.
    + eapply N_Modus_ponens. 1-2: shelve.
      * eapply N_Modus_ponens. 1-2: shelve.
        -- eapply N_Modus_ponens. 1-2: shelve.
           ++ apply (n_A_impl_A _ ABC). 1: shelve.
           ++ eapply N_Modus_ponens. 1-2: shelve.
              ** eapply N_Modus_ponens. 1-2: shelve.
                 --- apply(N_P2 _ A B C). 1-3: shelve.
                 --- eapply(N_P1 _ _ (A --->ₙ B --->ₙ C) _ _).
              ** apply N_P2. 1-3: shelve.
        -- eapply N_Modus_ponens. 1-2: shelve.
           ++ apply t1.
           ++ apply (N_P2). 1-3: shelve.
      * eapply N_Modus_ponens. 1-2: shelve.
        -- eapply N_Modus_ponens. 1-2: shelve.
           ++ apply(N_P2). 1-3: shelve.
           ++ apply(N_P1). 1-2: shelve.
        -- apply N_P2. 1-3: shelve.
    + apply N_P2. 1-3: shelve.
  Unshelve.
    all: simpl; try rewrite Hwf1; try rewrite Hwf2; try rewrite Hwf3; reflexivity.
Defined.

Lemma n_reorder_meta{Γ A B C} :
  named_well_formed A = true ->
  named_well_formed B = true ->
  named_well_formed C = true ->
  Γ ⊢N (A --->ₙ B --->ₙ C) ->
  Γ ⊢N (B --->ₙ A --->ₙ C).
Proof.
  intros Hwf1 Hwf2 Hwf3 H2.
  eapply N_Modus_ponens. 1-2: shelve. apply H2.
  apply n_reorder.
  Unshelve.
  all: simpl; try rewrite Hwf1; try rewrite Hwf2; try rewrite Hwf3; reflexivity.
Defined.

Lemma n_syllogism A B C Γ :
  named_well_formed A = true ->
  named_well_formed B = true ->
  named_well_formed C = true ->
  Γ ⊢N (A --->ₙ B) --->ₙ (B --->ₙ C) --->ₙ(A --->ₙ C).
Proof.
  intros Hwf1 Hwf2 Hwf3.
  apply n_reorder_meta. 1-3: shelve.
  eapply N_Modus_ponens. 1-2: shelve.
  - apply(N_P1 _ (B --->ₙ C) A). 1-2: shelve.
  - eapply N_Modus_ponens. 1-2: shelve.
    + eapply N_Modus_ponens. 1-2: shelve.
      * apply (N_P2 _ A B C). 1-3: shelve.
      * apply (N_P1 _ ((A --->ₙ B --->ₙ C) --->ₙ (A --->ₙ B) --->ₙ A --->ₙ C) (B --->ₙ C)). 1-2: shelve.
    + apply N_P2.
  Unshelve.
  all: simpl; try rewrite Hwf1; try rewrite Hwf2; try rewrite Hwf3; reflexivity.
Defined.

Lemma n_syllogism_meta :
  forall A B C Γ,
    named_well_formed A = true ->
    named_well_formed B = true ->
    named_well_formed C = true ->
    Γ ⊢N (npatt_imp A B) ->
    Γ ⊢N (npatt_imp B C) ->
    Γ ⊢N (npatt_imp A C).
Proof.
  intros A B C Γ Hwf1 Hwf2 Hwf3 H2 H3.
  eapply N_Modus_ponens. 1-2: shelve.
  - exact H2.
  - eapply N_Modus_ponens. 1-2: shelve.
    + exact H3.
    + apply n_reorder_meta. 1-3: shelve.
      apply n_syllogism.
  Unshelve.
  all: simpl; try rewrite Hwf1; try rewrite Hwf2; try rewrite Hwf3; reflexivity.
Defined.

Lemma translate_pred :
  forall phi ed sd evs svs,
  (translate_pattern evs svs ed sd phi) =
  (translate_pattern ({[evar_fresh (elements evs)]} ∪ evs) svs (pred ed) sd phi).
Proof.

Admitted.

Theorem proof_translation :
  forall Γ ϕ (H : Γ ⊢H ϕ) (evs : EVarSet) (svs : SVarSet) (ed sd : nat),
    match vars_of_proof H with
    | (free_evs, free_svs, minsize) =>
      free_evs ⊆ evs ->
      free_svs ⊆ svs ->
      ed ≥ minsize ->
      sd ≥ minsize ->
      set_map (translate_pattern evs svs ed sd) Γ ⊢N translate_pattern evs svs ed sd ϕ
    end.
Proof.
  intros Γ ϕ H. induction H; simpl; intros.
  * apply N_hypothesis.
    - apply well_formed_translate. wf_auto2.
      all: set_solver.
    - apply elem_of_map_2. assumption.
  * simp translate_pattern.
    apply N_P1; apply well_formed_translate; try assumption; wf_auto2.
    all: clear -H H0; set_solver.
  * simp translate_pattern.
    apply N_P2; apply well_formed_translate; try assumption; wf_auto2.
    all: clear -H H0; set_solver.
  * simp translate_pattern.
    apply N_P3; apply well_formed_translate; try assumption.
    wf_auto2.
  * repeat case_match. intros Hin1 Hin2 Hs1 Hs2.
    eapply N_Modus_ponens. 3: apply IHML_proof_system1.
    - apply well_formed_translate. clear H3. apply proved_impl_wf in H. wf_auto2.
      1-2: clear -Hin1 Hin2; set_solver.
    - apply proved_impl_wf in H0 as H0'. clear -H0' Hin1 Hin2.
      epose proof (well_formed_translate (patt_imp phi1 phi2) evs svs ed sd ltac:(wf_auto2) ltac:(set_solver) ltac:(set_solver)).
      by simp translate_pattern in H.
    - set_solver.
    - set_solver.
    - lia.
    - lia.
    - specialize (IHML_proof_system2 evs svs ed sd
           ltac:(set_solver) ltac:(set_solver)) as IH2.
      simp translate_pattern in IH2. apply IH2; lia.
  * simp translate_pattern. cbn.
    pose proof (N_Ex_quan (set_map (translate_pattern evs svs ed sd) Γ)).
    fold (evar_open y 0 phi).
    remember (nth (ed + 0) (evar_fresh_seq evs (S ed + 0)) (evar_fresh [])) as oldX.
    erewrite <- (translate_rename) with (x := oldX).
    2: wf_auto2.
    2-3: set_solver.
    2-3: lia.
    2: subst oldX; apply last_exists.
    2: set_solver.
    remember (evar_fresh (elements evs)) as freshX.
    assert (freshX ∉ named_evars (translate_pattern evs svs ed sd phi)). {
      unfold named_evars.
      destruct ed. lia.
      pose proof (translate_pattern_avoids_evar_blacklist phi ({[evar_fresh_s evs]} ∪ evs) svs ed sd).
      pose proof (named_free_evars_translate phi 1 ed sd evs svs ltac:(wf_auto2)
      ltac:(lia)).
      assert (freshX ∉ evs). { subst. apply set_evar_fresh_is_fresh'. }
      simpl in H5. clear HeqoldX H1 H2 H3 H0. subst freshX.
      admit. (* DOABLE *)
    }
    rewrite <-translate_rename with (x := oldX).
    all: auto; try lia. 2: wf_auto2. 2, 4: set_solver.
    2: { destruct ed. lia. simpl. subst oldX. rewrite last_exists.
         subst freshX. by simpl.
       }
    (* alpha renaming needed *)
    eapply n_syllogism_meta.
    1: apply N_Ex_quan.
    subst freshX. rewrite <-translate_pred.
    apply alpha_exists.
    - apply well_formed_translate; auto. wf_auto2. set_solver.
    - assumption.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
Defined.

End translation.
