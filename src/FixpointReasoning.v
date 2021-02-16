From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Setoid.
From Coq Require Import Ensembles.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import PropExtensionality ClassicalFacts.

From stdpp Require Import base list.

From MatchingLogic Require Import Syntax Semantics DerivedOperators Helpers.monotonic Utils.Lattice Utils.stdpp_ext.

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

  (* mu X. base \/ step X *)
  (* [Nats] = mu X. 0 \/ succ X *)
  (* [Nats] = \{ x | \ex x0,x1,..x_n . x0 \in 0 /\ x(i+1) \in succ xi }*)
  (*  0, 1, 2,... x*)
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
      rewrite !andb_true_r.
      rewrite !well_formed_positive_nest_mu_aux.
      rewrite Hwfpbase.
      rewrite Hwfpstep.
      rewrite !andb_true_r.

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

      (* I can imagine this lemma to be proven automatically. *)
      Lemma F_interp: F = λ A, Ensembles.Union _ (pattern_interpretation ρₑ ρₛ base)
                                               (app_ext (pattern_interpretation ρₑ ρₛ step) A).
      Proof.
        unfold F. unfold Fassoc. apply functional_extensionality.
        intros A. rewrite svar_open_patt_ind_gen_body_simpl.
        { apply set_svar_fresh_is_fresh. }

        rewrite pattern_interpretation_or_simpl.
        rewrite pattern_interpretation_app_simpl.
        rewrite pattern_interpretation_free_svar_simpl.
        rewrite update_svar_val_same.
        rewrite pattern_interpretation_free_svar_independent.
        {
          eapply svar_is_fresh_in_richer.
          2: { apply set_svar_fresh_is_fresh. }
          solve_free_svars_inclusion 5.
        }
        rewrite pattern_interpretation_free_svar_independent.
        {
          eapply svar_is_fresh_in_richer.
          2: { apply set_svar_fresh_is_fresh. }
          solve_free_svars_inclusion 5.
        }
        reflexivity.
      Qed.
      
      
      Definition is_witnessing_sequence_old (m : Domain M) (l : list (Domain M)) :=
        (last l = Some m) /\
        (match l with
         | [] => False
         | m₀::ms => (@pattern_interpretation Σ M ρₑ ρₛ base) m₀
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

      Definition is_witnessing_sequence (m : Domain M) (l : list (Domain M)) :=
        (∃ lst, last l = Some lst /\ @pattern_interpretation Σ M ρₑ ρₛ base lst)
          /\
          hd_error l = Some m
          /\
          ((@Forall _ (curry (λ new old,
                     app_ext
                       (@pattern_interpretation Σ M ρₑ ρₛ step)
                       (Ensembles.Singleton _ old)
                       new
                    ))
                    (zip l (tail l))
          )).

      Lemma is_witnessing_sequence_iff_is_witnessing_sequence_old_reverse (m : Domain M) (l : list (Domain M)) :
        is_witnessing_sequence m l <-> is_witnessing_sequence_old m (reverse l).
      Proof.
        assert (Feq: (curry (flip (λ new old : Domain M, app_ext (pattern_interpretation ρₑ ρₛ step) (Ensembles.Singleton (Domain M) old) new)))
                     =  (λ x : Domain M * Domain M, let (old, new) := x in app_ext (pattern_interpretation ρₑ ρₛ step) (Ensembles.Singleton (Domain M) old) new) ).
        { apply functional_extensionality. intros [x₁ x₂].
          reflexivity.
        }
        
        split.
        - intros [[m' [Hlast Hbase]] [Hhd Hfa]].
          destruct l as [|x l].
          { simpl in Hhd. inversion Hhd. }
          simpl in Hhd. inversion Hhd. subst. clear Hhd.
          split.
          { rewrite reverse_cons. rewrite last_app_singleton.
            reflexivity.
          }

          (* reverse (m::l) <> nil *)
          destruct (reverse (m::l)) eqn:Heq.
          { assert ( length (reverse (m::l)) = @length (Domain M) []).
            { rewrite Heq. reflexivity. }
            rewrite reverse_length in H.
            simpl in H. inversion H.
          }

          assert (Hm'd: m' = d).
          {
            rewrite reverse_cons in Heq.
            pose proof (H := @last_reverse_head _ l m).
            rewrite Hlast in H.
            unfold reverse in Heq.
            rewrite Heq in H.
            simpl in H.
            inversion H. subst.
            reflexivity.
          }
          subst.
          split.
          { apply Hbase. }
          clear Hbase.

          pose proof (Heq' := f_equal reverse Heq).
          rewrite reverse_involutive in Heq'.
          assert (Heq'' : l0 = tail (d::l0)).
          { reflexivity. }
          rewrite -> Heq'' at 2. clear Heq''.
          rewrite -Heq.
          clear Heq' Heq l0.
          apply Forall_zip_flip_reverse in Hfa.
          clear Hlast.

          rewrite Feq in Hfa.
          apply Hfa.
        - intros H.
          destruct H as [Hlast H2].
          destruct l as [|x l].
          { simpl in Hlast. inversion Hlast. }

          destruct (reverse (x::l)) as [|y ys] eqn:Heq.
          { inversion H2. }
          destruct H2 as [Hbase Hfa].

          rewrite -(reverse_involutive (y::ys)) in Heq.
          apply (@inj _ _ (=) _ reverse) in Heq.
          2: typeclasses eauto.
          
          split.
          { exists y.
            split.
            rewrite Heq.
            rewrite last_reverse.
            reflexivity.
            apply Hbase.
          }

          split.
          {
            rewrite Heq.
            rewrite head_reverse.
            apply Hlast.
          }

          assert (Hfeq': (λ new old : Domain M, app_ext (pattern_interpretation ρₑ ρₛ step) (Ensembles.Singleton (Domain M) old) new) = flip (flip (λ new old : Domain M, app_ext (pattern_interpretation ρₑ ρₛ step) (Ensembles.Singleton (Domain M) old) new))).
          { apply functional_extensionality. intros x0.
            apply functional_extensionality. intros x1.
            reflexivity.
          }
          rewrite Hfeq'.
          rewrite Heq.
          rewrite -Forall_zip_flip_reverse.
          rewrite Feq.
          apply Hfa.
      Qed.

      Lemma witnessing_sequence_extend (m m' : Domain M) (l : list (Domain M)) :
        (is_witnessing_sequence m l
         /\ (∃ step', pattern_interpretation ρₑ ρₛ step step' /\ app_interp step' m m')
        ) <-> (is_witnessing_sequence m' (m'::l) /\ l ≠ []).
      Proof.
        split.
        - intros [[[lst [Hlst Hbase]] [Hhd Hwit]] [step' [Hstep' Hm']]].
          split.
          2: { destruct l. simpl in Hhd. inversion Hhd. discriminate. }
          move: m Hhd m' step' Hm' Hstep'.
          induction l; intros m Hhd m' step' Hm' Hstep'.
          + simpl in Hhd. inversion Hhd.
          + simpl in Hhd. inversion Hhd. subst a. clear Hhd.
            unfold is_witnessing_sequence.
            destruct l.
            { simpl in Hlst. inversion Hlst. subst m. clear Hlst.
              split.
              { exists lst. simpl. split. reflexivity. apply Hbase. }
              simpl. split. reflexivity. apply Forall_cons.
              split. exists step'. exists lst. split.
              apply Hstep'. split. constructor. apply Hm'.
              apply Forall_nil. exact I.
            }
            split.
            { exists lst. split. simpl. simpl in Hlst. apply Hlst. apply Hbase. }
            split.
            { reflexivity. }
            simpl in Hwit. simpl.
            apply Forall_cons.
            simpl in IHl. simpl in Hlst.
            specialize (IHl Hlst).
            inversion Hwit. subst. clear Hwit.
            specialize (IHl H2). clear Hlst H2.
            split.
            { exists step'. exists m. split. apply Hstep'. split. constructor. apply Hm'. }
            apply Forall_cons.
            split.
            { apply H1. }
            specialize (IHl d).
            specialize (IHl (eq_refl (Some d))).
            destruct H1 as [step'' [d'' [Hstep'' [Hd'' Hstep''d'']]]].
            inversion Hd''. subst d''. clear Hd''.
            specialize (IHl m step'' Hstep''d'' Hstep'').
            unfold is_witnessing_sequence in IHl.
            simpl in IHl.
            destruct IHl as [_ [_ Hforall]].
            inversion Hforall. subst. apply H2.
        -            
      Abort.
            
          


      Lemma witnessing_sequence_old_extend
            (m x m' : Domain M) (l : list (Domain M)):
        (is_witnessing_sequence_old m (x::l) /\
        ∃ step', (pattern_interpretation ρₑ ρₛ step step' /\
        app_interp step' m m')) <->
        (last (x::l) = Some m /\ is_witnessing_sequence_old m' ((x::l) ++ [m'])).
      Proof.
        split.
        -
          intros [Hwit [step' [Hstep' Hm']]].
          destruct Hwit as [Hwit1 [Hwit2 Hwit3]].
          split.
          { apply Hwit1. }
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
          + intros D Hm _.
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
          + intros d Hlast Hwit. simpl.
            inversion Hwit. subst.
            apply Forall_cons.
            split.
            { apply H1. }
            apply IHl. simpl in Hlast. simpl. apply Hlast.
            apply H2.
        - intros [Hlast H].
          unfold is_witnessing_sequence in H.
          destruct H as [_ H].
          remember (length l) as len.
          assert (Hlen: length l <= len).
          { lia. }
          clear Heqlen. simpl in H.
          destruct H as [Hbase Hall].
          unfold is_witnessing_sequence.
          apply and_assoc.
          split.
          { apply Hlast. }
          apply and_assoc.
          split.
          { apply Hbase. }
          clear Hbase.
          
          move: x l Hlast Hall Hlen.
          induction len.
          + intros x l Hlast Hall Hlen.
            destruct l.
            2: { simpl in Hlen. lia.  }
            simpl. simpl in Hall.
            split.
            { apply Forall_nil. exact I. }
            inversion Hall. subst. clear Hall. clear H2.
            destruct H1 as [step' [m'' [Hstep' [Hm'm'' Hstep'm'']]]].
            inversion Hm'm''. subst. clear Hm'm''.
            exists step'. split. apply Hstep'.
            simpl in Hlast. inversion Hlast. subst.
            apply Hstep'm''.
          + intros x l Hlast Hall Hlen.
            destruct l as [|x' l'].
            { simpl in Hlast. inversion Hlast. clear Hlast. subst.
              simpl in Hall.
              inversion Hall. subst. clear Hall.
              clear H2.
              simpl.
              split.
              { apply Forall_nil. exact I. }
              destruct H1 as [step' Hstep'].
              exists step'.
              destruct Hstep' as [m'' [Hstep' [Hmm'' Hm'']]].
              split.
              { apply Hstep'. }
              inversion Hmm''. subst.
              apply Hm''.
            }
            simpl in Hall. simpl in IHlen. simpl in Hlast.
            inversion Hall. subst. clear Hall.
            specialize (IHlen x' l' Hlast H2).
            simpl.
            rewrite Forall_cons.
            apply and_assoc.
            split.
            { apply H1. }
            apply IHlen.
            simpl in Hlen. lia.
      Qed.
      
      

      Definition witnessed_elements_old : Ensemble (Domain M) :=
        λ m, ∃ l, is_witnessing_sequence_old m l.

      Lemma witnessed_elements_old_prefixpoint : Included _ (F witnessed_elements_old) witnessed_elements_old.
      Proof.
        unfold Included. unfold Ensembles.In.
        intros x Hx.
        unfold F in Hx. unfold Fassoc in Hx.
        rewrite pattern_interpretation_or_simpl in Hx. fold svar_open in Hx. simpl in Hx.
        destruct Hx.
        - unfold Ensembles.In in H.
          unfold witnessed_elements_old.
          exists [x]. unfold is_witnessing_sequence_old.
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
          unfold witnessed_elements_old in H2.
          destruct H2 as [l Hl].

          unfold witnessed_elements_old.
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

          epose proof (P := @witnessing_sequence_old_extend _ _ _ _).
          destruct P as [P _].
          specialize (P (conj Hl (@ex_intro _ _ step' (conj H1 Happ)))).
          apply P.
      Qed.

      Lemma interp_included_in_witnessed_elements_old:
        Included _ (@pattern_interpretation Σ M ρₑ ρₛ patt_ind_gen) witnessed_elements_old.
      Proof.
        apply pattern_interpretation_mu_lfp_least.
        { apply patt_ind_gen_wfp. }
        apply witnessed_elements_old_prefixpoint.
      Qed.

      Lemma pattern_interpretation_patt_ind_gen_fix :
        let Sfix := pattern_interpretation ρₑ ρₛ patt_ind_gen in
        F Sfix = Sfix.
      Proof.
        apply pattern_interpretation_mu_lfp_fixpoint.
        apply patt_ind_gen_wfp.
      Qed.
      
      
      Definition witnessed_elements_old_of_max_len len : Ensemble (Domain M) :=
        λ m, ∃ l, is_witnessing_sequence_old m l /\ length l <= len.

      Lemma witnessed_elements_old_of_max_len_included_in_interp len:
        Included _ (witnessed_elements_old_of_max_len (S len)) (@pattern_interpretation Σ M ρₑ ρₛ patt_ind_gen).
      Proof.
        induction len.
        - unfold Included. intros m.
          rewrite -pattern_interpretation_patt_ind_gen_fix.
          unfold Ensembles.In.
          intros H.
          unfold witnessed_elements_old_of_max_len.
          rewrite F_interp.
          destruct H as [l [Hwit Hlen]].
          unfold is_witnessing_sequence in Hwit.
          destruct Hwit as [Hlast Hm].
          destruct l.
          { simpl in Hlast. inversion Hlast. }
          destruct l.
          2: { simpl in Hlen. lia. }
          simpl in Hlast. inversion Hlast. clear Hlast. subst.
          destruct Hm as [Hm _].
          left. unfold Ensembles.In. apply Hm.
        - unfold Included. intros m.
          rewrite -pattern_interpretation_patt_ind_gen_fix.
          unfold Ensembles.In. intros H.
          destruct H as [l [Hwit Hlen]].
          unfold Included in IHlen. unfold Ensembles.In in IHlen.
          rewrite F_interp.
          pose proof (Hwit' := Hwit).
          unfold is_witnessing_sequence in Hwit.
          destruct Hwit as [Hlast Hl].
          destruct l.
          { contradiction. }
          
          simpl in Hlen.
          destruct Hl as [Hd Hl].
          destruct l.
          + simpl in Hlast. inversion Hlast. clear Hlast. subst.
            left. unfold Ensembles.In. apply Hd.
          + right. unfold Ensembles.In.
            pose proof (P := witnessing_sequence_old_extend).
            destruct l as [|x' l'].
            { simpl in Hlast. inversion Hlast. subst.
              specialize (P d d m []).
              destruct P as [_ P]. simpl in P.
              simpl in Hl.
              inversion Hl. subst. clear Hl.
              assert (Hsomed: Some d = Some d).
              { reflexivity. }
              specialize (P (conj Hsomed Hwit')).
              destruct P as [Hwitd [step' Hstep']].
              exists step'. exists d.
              destruct Hstep' as [Hstep' Hm].
              split.
              { apply Hstep'. }
              split.
              { apply IHlen. unfold witnessed_elements_old_of_max_len.
                exists [d].
                split.
                2: { simpl. lia. }
                unfold is_witnessing_sequence. simpl.
                split.
                { reflexivity. }
                split.
                { apply Hd. }
                apply Forall_nil.
                exact I.
              }
              apply Hm.
            }
            simpl in P.
            simpl in Hlast.
            simpl in Hl.
            inversion Hl. subst. clear Hl.
            inversion H2. subst. clear H2.
            pose (mp := (rev (d0 :: x' :: l')) !! 1).
            simpl in mp.
            epose proof (Htot := (@list_lookup_lookup_total_lt (Domain M) _ (rev (d0 :: x' :: l')) 1 _)).
            Unshelve. 2: { constructor. exact d0. }
            2: { simpl. rewrite app_length. rewrite app_length. simpl.  lia.  }

            remember (@lookup_total nat (@Domain Σ M) (list (@Domain Σ M))
                 (@list_lookup_total (@Domain Σ M) {| inhabitant := d0 |}) (S O)
                 (@rev (@Domain Σ M) (@cons (@Domain Σ M) d0 (@cons (@Domain Σ M) x' l')))) as mprev.

            specialize (IHlen mprev).
            unfold witnessed_elements_old_of_max_len in IHlen.
            specialize (P mprev d m  (rev (tl (rev (d0::x'::l'))))).

            assert (Heq1: d::d0::x'::l' = d::(rev (tail (rev (d0::x'::l')))) ++ [m]).
            {
              apply f_equal.
              simpl.
              assert (Hx'r: [x'] = rev [x']).
              { reflexivity. }
              rewrite Hx'r.
              rewrite -rev_app_distr.
              assert (Hd0r: [d0] = rev [d0]).
              { reflexivity. }
              rewrite Hd0r.
              rewrite -rev_app_distr.
              rewrite rev_tail_rev_app_last.
              simpl.
              apply Hlast.
              reflexivity.
            }
            destruct P as [_ P].
            

            destruct (rev (tail (rev (d0 :: x' :: l')))) eqn:Heqrev.
            {
              apply length_zero_iff_nil in Heqrev.
              rewrite rev_length in Heqrev.
              apply length_tail_zero in Heqrev.
              rewrite rev_length in Heqrev.
              simpl in Heqrev. lia.
            }

            simpl in Heq1. inversion Heq1. subst d0. clear Heq1.
            simpl in P.
            rewrite -H2 in P.
            
            assert (Hm : (match l with [] => Some d1 | _ :: _ => last l end ) = Some mprev).
            {
              clear P Heqrev H1 H3 H4 mp.
              destruct l.
              { simpl in H2. inversion H2. subst. reflexivity. }
              simpl.
              simpl in H2.
              inversion H2. subst x' l'. clear H2.
              simpl in Htot.
              destruct (l ++ [m]) eqn:Hcontra.
              { pose proof (Hcontra' := @app_length _ l [m]).
                rewrite Hcontra in Hcontra'.
                simpl in Hcontra'. lia.
              }
              rewrite -Hcontra in Htot.
              rewrite rev_app_distr in Htot. simpl in Htot.

              destruct l.
              { simpl in Htot. apply Htot. }
              simpl in Htot.
              rewrite -Htot.
              rewrite hd_error_lookup.
              rewrite hd_error_app. rewrite hd_error_app.
              apply last_rev_head.
            }
            specialize (P (@conj _ _ Hm Hwit')). clear Hm Hwit'.
            destruct P as [Hwitmprev [step' [Hstep' Hm]]].
            exists step'. exists mprev.
            split.
            { apply Hstep'. }
            split.
            2: { apply Hm. }
            apply IHlen.
            exists (d::d1::l).
            split.
            { apply Hwitmprev. }
            simpl. simpl in Hlen.
            assert (Hlen': S (length l') <= len).
            { lia. }
            assert (length (l') = length (l)).
            { apply (@list_len_slice _ _ _ _ _ H2). }
            rewrite -H. lia.
      Qed.
      
          
      Lemma witnessed_elements_old_included_in_interp:
        Included _ witnessed_elements_old (@pattern_interpretation Σ M ρₑ ρₛ patt_ind_gen).
      Proof.
        intros x H.
        unfold Ensembles.In in H. unfold witnessed_elements_old in H.
        destruct H as [wit Hwit].
        assert (H': Ensembles.In (Domain M) (witnessed_elements_old_of_max_len (length wit)) x).
        { unfold Ensembles.In. exists wit. split. apply Hwit. lia. }
        destruct wit as [|y l'] eqn:Hl.
        { unfold is_witnessing_sequence in Hwit. destruct Hwit. contradiction. }
        eapply witnessed_elements_old_of_max_len_included_in_interp.
        simpl in H'.
        apply H'.
      Qed.

      Definition witnessed_elements : Ensemble (Domain M) :=
        λ m, ∃ l, is_witnessing_sequence m l.

      Lemma witnessed_elements_old_eq_witnessed_elements :
        witnessed_elements_old = witnessed_elements.
      Proof.
        apply (@Extensionality_Ensembles _).
        split; unfold Included; unfold Ensembles.In;
          unfold witnessed_elements_old; unfold witnessed_elements; intros m; intros [l H].
        + exists (reverse l).
          apply is_witnessing_sequence_iff_is_witnessing_sequence_old_reverse.
          rewrite reverse_involutive.
          exact H.
        + exists (reverse l).
          apply is_witnessing_sequence_iff_is_witnessing_sequence_old_reverse.
          apply H.
      Qed.
      
      Lemma patt_ind_gen_simpl:
        @pattern_interpretation Σ M ρₑ ρₛ patt_ind_gen = witnessed_elements.
      Proof.
        rewrite -witnessed_elements_old_eq_witnessed_elements.
        apply Ensembles_Ext.eq_iff_Same_set.
        split.
        + apply interp_included_in_witnessed_elements_old.
        + apply witnessed_elements_old_included_in_interp.
      Qed.

      
      Section injective.
        (* `base` is functional, and `step` is an injective function on witnessed_elements. *)
        Hypothesis (Hbase_functional : @is_functional_pattern _ base M ρₑ ρₛ).
        Hypothesis (Hstep_total_function : @is_total_function _ M step witnessed_elements witnessed_elements ρₑ ρₛ).
        (* TODO we need a hypothesis for injectivity *)

        Lemma witnessed_elements_unique_seq :
          ∀ m l₁ l₂, is_witnessing_sequence m l₁ -> is_witnessing_sequence m l₂ -> l₁ = l₂.
        Proof.
          intros m l₁ l₂.
          wlog: l₁ l₂ / (length l₂ <= length l₁).
          { intros H Hw₁ Hw₂.
            destruct (decide (length l₁ <= length l₂)).
            - symmetry. apply H; auto.
            - apply H. lia. auto. auto.
          }
          intros Hlen12 Hw₁ Hw₂.

          assert (Hlcom:  ( @common_length _ (@Domain_eq_dec _ M) l₁ l₂ = length l₂)).
          {
            destruct Hw₁ as [[lst₁ [Hlst₁ Hbase₁]] [Hhd₁ Hfa₁]].
            destruct l₁ as [|m₁ l₁].
            { simpl in Hlst₁. inversion Hlst₁. }
            simpl in Hhd₁. inversion Hhd₁. subst. clear Hhd₁.

            destruct Hw₂ as [[lst₂ [Hlst₂ Hbase₂]] [Hhd₂ Hfa₂]].
            destruct l₂ as [|m₂ l₂].
            { simpl in Hlst₂. inversion Hlst₂. }
            simpl in Hhd₂. inversion Hhd₂. subst. clear Hhd₂.
            
            simpl.
            destruct (decide (m=m)).
            2: { contradiction. }
            clear e.
            apply f_equal.
        Abort.
        (*
              destruct Hw₁ as [_ Hcontra]. contradiction.
            - destruct Hw₂ as [_ Hcontra]. contradiction.
            - simpl in Hlen₂. lia.
            - simpl in Hlen12. lia.
            - simpl in Hlen12. lia.
            - destruct Hw₂ as [_ Hcontra]. contradiction.
            - rewrite 2!reverse_cons.
              rename d into d₁. rename d0 into d₂.
              simpl in Hlen₂.
              assert (Hlen₂': length l₂ <= len₂).
              { lia. }
              simpl in Hlen12.
              assert (Hlen12': len₂ <= length l₁).
              { lia. }
              specialize (IHlen₂ l₁ l₂ Hlen₂' Hlen12').
              (* Problem: l₁ and l₂ are not witnessing sequences. 
                 We probably want to weaken the condition, because
                 we only need to know that they are `step`-sequences *)
          
        Abort.
        *)
        
        
      End injective.
      
    End with_interpretation.

    

    
  End inductive_generation.
  
  
End with_signature.
