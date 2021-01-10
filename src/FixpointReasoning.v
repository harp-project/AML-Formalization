From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
From Coq Require Import Ensembles.
From Coq.Logic Require Import FunctionalExtensionality.

From stdpp Require Import base list.

From MatchingLogic Require Import Syntax Semantics DerivedOperators Helpers.monotonic Utils.Lattice.

Section with_signature.
  Context {Σ : Signature}.
  Existing Instance variables.

  Lemma pattern_interpretation_mu_lfp_fixpoint M ρₑ ρₛ ϕ :
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X in
    let Sfix := @pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ) in
    F Sfix = Sfix.
  Proof.
    simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X) as F.
    remember (@pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ)) as Sfix.
    pose (OS := EnsembleOrderedSet (Domain M)).
    pose (L := PowersetLattice (Domain M)).
    intros Hwfp.

    assert (HFmono: MonotonicFunction F).
    { rewrite HeqF. rewrite /Fassoc. apply is_monotonic. apply Hwfp.
      rewrite HeqX. apply set_svar_fresh_is_fresh.
    }

    assert (Ffix : Lattice.isFixpoint F (Lattice.LeastFixpointOf F)).
    { apply Lattice.LeastFixpoint_fixpoint. apply HFmono.
    }

    unfold isFixpoint in Ffix.
    rewrite pattern_interpretation_mu_simpl in HeqSfix.
    simpl in HeqSfix.
    unfold Fassoc in HeqF.
    rewrite HeqX in HeqF.
    rewrite -HeqF in HeqSfix.
    rewrite -HeqSfix in Ffix.
    apply Ffix.
  Qed.


  Lemma pattern_interpretation_mu_lfp_least M ρₑ ρₛ ϕ S:
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X in
    let Sfix := @pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ) in
    Included _ (F S) S ->
    Included _ Sfix S.
  Proof.
    simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X) as F.
    remember (@pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ)) as Sfix.
    pose (OS := EnsembleOrderedSet (Domain M)).
    pose (L := PowersetLattice (Domain M)).
    intros Hwfp.

    assert (HFmono: MonotonicFunction F).
    { rewrite HeqF. rewrite /Fassoc. apply is_monotonic. apply Hwfp.
      rewrite HeqX. apply set_svar_fresh_is_fresh.
    }

    assert (Hlfp: LeastFixpointOf F = Sfix).
    { subst. rewrite pattern_interpretation_mu_simpl. simpl. unfold Fassoc. reflexivity. }

    intros Hincl.

    pose proof (Hleast := LeastFixpoint_LesserThanPrefixpoint _ _ _ F S).
    simpl in Hleast. specialize (Hleast Hincl).
    rewrite Hlfp in Hleast. apply Hleast.
  Qed.

  Lemma pattern_interpretation_mu_if_lfp M ρₑ ρₛ ϕ Sfix :
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X in
    F Sfix = Sfix ->
    (∀ S, Included _ (F S) S -> Included _ Sfix S) ->
    Sfix = @pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ).
  Proof.
    intros Hwfp. simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X) as F.
    intros Hfix Hleast.
    rewrite pattern_interpretation_mu_simpl. simpl.
    unfold Fassoc in HeqF. unfold Power in HeqF. rewrite HeqX in HeqF. rewrite -HeqF.
    apply LeastFixpoint_unique. { apply Hfix. } apply Hleast.
  Qed.

  Lemma pattern_interpretation_mu_lfp_iff M ρₑ ρₛ ϕ Sfix :
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X in
    (
    F Sfix = Sfix /\
    (∀ S, Included _ (F S) S -> Included _ Sfix S)
    ) <-> Sfix = @pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ).
  Proof.
    intros Hwfp. simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X) as F.
    remember (@pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ)) as Sfix'.
    split.
    - intros [H1 H2]. subst.
      auto using pattern_interpretation_mu_if_lfp.
    - intros H. split.
      + subst. apply pattern_interpretation_mu_lfp_fixpoint. apply Hwfp.
      + intros S. subst. apply pattern_interpretation_mu_lfp_least. apply Hwfp.
  Qed.
  
  Section inductive_generation.
    Context (base step : Pattern).

    Let patt_ind_gen_body := (patt_or (nest_mu base) (patt_app (nest_mu step) (patt_bound_svar 0))).
    
    Definition patt_ind_gen := patt_mu patt_ind_gen_body.

    Search evar_open nest_ex.
    (*Search svar_open nest_mu.*)

    Hypothesis (Hwfpbase : well_formed_positive base).
    Hypothesis (Hwfpstep : well_formed_positive step).

    Lemma patt_ind_gen_wfp:
      well_formed_positive patt_ind_gen.
    Proof.
      unfold patt_ind_gen. simpl.
      rewrite !(right_id True and).
      rewrite !well_formed_positive_nest_mu_aux.
      split.
      2: { auto. }
      
      rewrite (reflect_iff _ _ (no_negative_occurrence_P _ _)).
      cbn. fold no_negative_occurrence_db_b.

      rewrite !no_negative_occurrence_db_nest_mu_aux. simpl.
      auto.
    Qed.


    
    Section with_interpretation.
      Context (M : @Model Σ).
      Context (ρₑ : @EVarVal Σ M).
      Context (ρₛ : @SVarVal Σ M).

      Definition is_witnessing_sequence (m : Domain M) (l : list (Domain M)) :=
        (last l = Some m) /\
        (match l with
         | [] => False
         | m₀::ms => (@pattern_interpretation Σ M ρₑ ρₛ base) m₀
                     /\ fst (foldl (λ (Acc : Prop * (Domain M)) new,
                                    let (P, old) := Acc in
                                    (app_ext
                                       (@pattern_interpretation Σ M ρₑ ρₛ step)
                                       (Ensembles.Singleton _ old)
                                       new,
                                     new)
                                   ) (True, m₀) ms)
         end).

      Definition witnessed_elements : Ensemble (Domain M) :=
        λ m, ∃ l, is_witnessing_sequence m l.
      
      Lemma patt_ind_gen_simpl:
        @pattern_interpretation Σ M ρₑ ρₛ patt_ind_gen = witnessed_elements.
      Proof.
      Abort.

    End with_interpretation.
  End inductive_generation.
  
  
End with_signature.
