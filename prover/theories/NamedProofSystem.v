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


  Equations? translate_pattern (evs : EVarSet) (svs : SVarSet) (ϕ : Pattern) : NamedPattern by wf (size' ϕ) lt :=
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
      npatt_imp (translate_pattern evs svs ϕ₁) (translate_pattern evs svs ϕ₁);
    translate_pattern evs svs (patt_app ϕ₁ ϕ₂) :=
      npatt_app (translate_pattern evs svs ϕ₁) (translate_pattern evs svs ϕ₁);
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
  Defined.

  Lemma translate_pattern_avoids_evar_blacklist :
    forall ϕ evs svs,
      named_bound_evars (translate_pattern evs svs ϕ) ## evs.
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; intros ϕ Hsize evs svs; destruct ϕ; simpl in Hsize; try lia.
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
      specialize (IHs ltac:(lia) ({[evar_fresh (elements evs)]} ∪ evs) svs).
      remember (named_bound_evars _) as A. clear HeqA.
      pose proof (Hfresh := set_evar_fresh_is_fresh' evs). set_solver.
    * specialize (IHs (svar_open (svar_fresh (elements svs)) 0 ϕ)).
      rewrite svar_open_size' in IHs.
      specialize (IHs ltac:(lia) evs ({[svar_fresh (elements svs)]} ∪ svs)).
      set_solver.
  Defined.

  Lemma translate_pattern_avoids_svar_blacklist :
    forall ϕ evs svs,
      named_bound_svars (translate_pattern evs svs ϕ) ## svs.
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; intros ϕ Hsize evs svs; destruct ϕ; simpl in Hsize; try lia.
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
      specialize (IHs ltac:(lia) ({[evar_fresh (elements evs)]} ∪ evs) svs).
      set_solver.
    * specialize (IHs (svar_open (svar_fresh (elements svs)) 0 ϕ)).
      rewrite svar_open_size' in IHs.
      specialize (IHs ltac:(lia) evs ({[svar_fresh (elements svs)]} ∪ svs)).
      remember (named_bound_svars _) as A. clear HeqA.
      pose proof (Hfresh := set_svar_fresh_is_fresh' svs). set_solver.
  Defined.


End named_proof_system.
