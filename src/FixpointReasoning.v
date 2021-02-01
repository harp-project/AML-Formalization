From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
From Coq Require Import Ensembles.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import PropExtensionality ClassicalFacts.

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
    Included _ (F Sfix) Sfix ->
    (∀ S, Included _ (F S) S -> Included _ Sfix S) ->
    Sfix = @pattern_interpretation Σ M ρₑ ρₛ (patt_mu ϕ).
  Proof.
    intros Hwfp. simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X) as F.
    intros Hprefix Hleast.
    rewrite pattern_interpretation_mu_simpl. simpl.
    unfold Fassoc in HeqF. unfold Power in HeqF. rewrite HeqX in HeqF. rewrite -HeqF.
    apply LeastFixpoint_unique. { apply Hprefix. } apply Hleast.
  Qed.

  Lemma pattern_interpretation_mu_lfp_iff M ρₑ ρₛ ϕ Sfix :
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρₑ ρₛ (svar_open 0 X ϕ) X in
    (
    Included _ (F Sfix) Sfix /\
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
      + subst. apply Ensembles_Ext.Included_refl_eq.
        apply pattern_interpretation_mu_lfp_fixpoint. apply Hwfp.
      + intros S. subst. apply pattern_interpretation_mu_lfp_least. apply Hwfp.
  Qed.
  
  Section inductive_generation.
    Context (base step : Pattern).

    Let patt_ind_gen_body := (patt_or (nest_mu base) (patt_app (nest_mu step) (patt_bound_svar 0))).
    Let patt_ind_gen_simple_body := (patt_or base (patt_app step (patt_free_svar (fresh_svar patt_ind_gen_body)))).
    
    
    Definition patt_ind_gen := patt_mu patt_ind_gen_body.

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


    Lemma svar_open_patt_ind_gen_body_simpl M ρₑ ρₛ X:
      svar_is_fresh_in X patt_ind_gen_body ->
      @pattern_interpretation Σ M ρₑ ρₛ (svar_open 0 X patt_ind_gen_body)
      = @pattern_interpretation Σ M ρₑ ρₛ (patt_or base (patt_app step (patt_free_svar X))).
    Proof.
      intros Hfr.
      unfold svar_is_fresh_in in Hfr. simpl in Hfr.
      rewrite !simpl_free_svars in Hfr.
      apply sets.not_elem_of_union in Hfr.
      destruct Hfr as [Hfr1 Hfr2].

      rewrite /patt_ind_gen_body.
      rewrite !simpl_svar_open. simpl.
      rewrite 2!pattern_interpretation_or_simpl.
      rewrite pattern_interpretation_svar_open_nest_mu'.
      { assumption.  }
      apply f_equal.

      rewrite 2!pattern_interpretation_app_simpl.
      rewrite pattern_interpretation_svar_open_nest_mu'.
      { assumption. }
      apply f_equal.

      reflexivity.
    Qed.
    
    
    Section with_interpretation.
      Context (M : @Model Σ).
      Context (ρₑ : @EVarVal Σ M).
      Context (ρₛ : @SVarVal Σ M).


      Let F := let X := fresh_svar patt_ind_gen_body in
               @Fassoc Σ M ρₑ ρₛ (svar_open 0 X patt_ind_gen_body) X.
      (*
      Lemma svar_open_patt_ind_gen_body_assoc S:
        let X := fresh_svar patt_ind_gen_body in
        pattern_interpretation ρₑ (update_svar_val X S ρₛ) (svar_open 0 X patt_ind_gen_body)
        = F S.
      Proof. reflexivity.
             (*
        cbv zeta.
        rewrite svar_open_patt_ind_gen_body_simpl.
        { apply set_svar_fresh_is_fresh. }
        subst F. unfold Fassoc.
        rewrite svar_open_patt_ind_gen_body_simpl.
        { apply set_svar_fresh_is_fresh.  }
        reflexivity.*)
      Qed.
*)
      Definition is_witnessing_sequence (m : Domain M) (l : list (Domain M)) :=
        (last l = Some m) /\
        (match l with
         | [] => False
         | m₀::ms => (@pattern_interpretation Σ M ρₑ ρₛ base) m₀
(*                     /\ forall (n : nat), n <= length ms ->*)
                                                             
                     /\  (@Forall _
                                  (λ (x : (Domain M) * (Domain M)),
                                   let (old, new) := x in
                                  app_ext
                                    (@pattern_interpretation Σ M ρₑ ρₛ step)
                                    (Ensembles.Singleton _ old)
                                    new
                                 )
                                 (zip (m₀::ms) ms)
                         )
                           
         end).

      Lemma witnessing_sequence_extend
            (m x step' m' : Domain M) (l : list (Domain M)):
        is_witnessing_sequence m (x::l) ->
        pattern_interpretation ρₑ ρₛ step step' ->
        app_interp step' m m' ->
        is_witnessing_sequence m' ((x::l) ++ [m']).
      Proof.
        intros Hwit Hstep' Hm'.
        destruct Hwit as [Hwit1 [Hwit2 Hwit3]].
        split.
        { apply last_snoc. }
        simpl.
        split.
        { apply Hwit2. }
        
        destruct l.
        { simpl. apply Forall_cons. split. 2: { apply Forall_nil. exact I. }
          exists step'. exists x. split.
          { apply Hstep'. }
          split.
          { constructor. }
          simpl in Hwit1. inversion Hwit1. subst. apply Hm'.
        }
        simpl.
        apply Forall_cons.
        simpl in Hwit3. inversion Hwit3. subst. clear Hwit3.
        rename H1 into Hd. rename H2 into Hwit.
        split.
        { apply Hd. } clear Hd.

        move: d Hwit1 Hwit.
        induction l.
        - intros D Hm _.
          simpl. simpl in Hm. inversion Hm. subst.
          clear Hm.
          apply Forall_cons.
          split.
          2: { apply Forall_nil. exact I. }
          exists step'. exists m. split.
          { apply Hstep'. }
          split.
          { constructor. }
          apply Hm'.
        - intros d Hlast Hwit. simpl.
          inversion Hwit. subst.
          apply Forall_cons.
          split.
          { apply H1. }
          apply IHl. simpl in Hlast. simpl. apply Hlast.
          apply H2.
      Qed.
      
      

      Definition witnessed_elements : Ensemble (Domain M) :=
        λ m, ∃ l, is_witnessing_sequence m l.

      Lemma witnessed_elements_prefixpoint : Included _ (F witnessed_elements) witnessed_elements.
      Proof.
        unfold Included. unfold Ensembles.In.
        intros x Hx.
        unfold F in Hx. unfold Fassoc in Hx.
        rewrite pattern_interpretation_or_simpl in Hx. fold svar_open in Hx. simpl in Hx.
        destruct Hx.
        - unfold Ensembles.In in H.
          unfold witnessed_elements.
          exists [x]. unfold is_witnessing_sequence.
          simpl.
          split.
          { reflexivity. }
          split.
          2: { constructor. }
          rewrite pattern_interpretation_free_svar_independent in H.
          {
            eapply svar_is_fresh_in_richer. 2: { subst. auto. }
            solve_free_svars_inclusion 5.
          }
          simpl.
          rewrite pattern_interpretation_svar_open_nest_mu' in H.
          { 
            eapply svar_is_fresh_in_richer.
            2: { apply set_svar_fresh_is_fresh. }
            simpl.
            solve_free_svars_inclusion 2.
          }
          assumption.
        - unfold Ensembles.In in H.
          rewrite pattern_interpretation_app_simpl in H.
          rewrite pattern_interpretation_free_svar_simpl in H.
          rewrite update_svar_val_same in H.
          unfold app_ext in H.
          destruct H as [step' [m [H1 [H2 Happ]]]].
          unfold witnessed_elements in H2.
          destruct H2 as [l Hl].

          unfold witnessed_elements.
          exists (l ++ [x]).

          (* `l` is not empty *)
          destruct l as [|m₀ l'] eqn:Heql.
          { unfold is_witnessing_sequence in Hl. destruct Hl. simpl in H. inversion H. }

          rewrite pattern_interpretation_svar_open_nest_mu in H1.
          {
            eapply svar_is_fresh_in_richer.
            2: { apply set_svar_fresh_is_fresh. }
            solve_free_svars_inclusion 2.
          }
          
          exact (@witnessing_sequence_extend _ _ _ _ _ Hl H1 Happ).
      Qed.
      
      
      Lemma patt_ind_gen_simpl:
        @pattern_interpretation Σ M ρₑ ρₛ patt_ind_gen = witnessed_elements.
      Proof.
      Abort.

    End with_interpretation.
  End inductive_generation.
  
  
End with_signature.
