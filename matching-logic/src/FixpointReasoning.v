From MatchingLogic Require Export monotonic
                                  DerivedOperators_Semantics.
Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Substitution.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.


Section with_signature.
  Context {Σ : Signature}.
  Open Scope ml_scope.

  Lemma eval_mu_lfp_fixpoint M ρ ϕ :
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρ (ϕ^{svar: 0 ↦ X}) X in
    let Sfix := @eval Σ M ρ (patt_mu ϕ) in
    F Sfix = Sfix.
  Proof.
    simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρ (ϕ^{svar: 0 ↦ X}) X) as F.
    remember (@eval _ M ρ (patt_mu ϕ)) as Sfix.
    pose (OS := PropsetOrderedSet (Domain M)).
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
    rewrite eval_mu_simpl in HeqSfix.
    simpl in HeqSfix.
    unfold Fassoc in HeqF.
    rewrite HeqX in HeqF.
    rewrite -HeqF in HeqSfix.
    rewrite -HeqSfix in Ffix.
    apply Ffix.
  Qed.


  Lemma eval_mu_lfp_least M ρ ϕ S:
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρ (ϕ^{svar: 0 ↦ X}) X in
    let Sfix := @eval Σ M ρ (patt_mu ϕ) in
    (F S) ⊆ S ->
    Sfix ⊆ S.
  Proof.
    simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρ (ϕ^{svar: 0 ↦ X}) X) as F.
    remember (@eval _ M ρ (patt_mu ϕ)) as Sfix.
    pose (OS := PropsetOrderedSet (Domain M)).
    pose (L := PowersetLattice (Domain M)).
    intros Hwfp.

    assert (HFmono: MonotonicFunction F).
    { rewrite HeqF. rewrite /Fassoc. apply is_monotonic. apply Hwfp.
      rewrite HeqX. apply set_svar_fresh_is_fresh.
    }

    assert (Hlfp: LeastFixpointOf F = Sfix).
    { subst. rewrite eval_mu_simpl. simpl. unfold Fassoc. reflexivity. }

    intros Hincl.

    pose proof (Hleast := LeastFixpoint_LesserThanPrefixpoint _ _ _ F S).
    simpl in Hleast. specialize (Hleast Hincl).
    rewrite Hlfp in Hleast. apply Hleast.
  Qed.

  Lemma eval_mu_if_lfp M ρ ϕ Sfix :
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρ (ϕ^{svar: 0 ↦ X}) X in
    (F Sfix) ⊆ Sfix ->
    (∀ S, (F S) ⊆ S -> Sfix ⊆ S) ->
    Sfix = @eval Σ M ρ (patt_mu ϕ).
  Proof.
    intros Hwfp. simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρ (ϕ^{svar: 0 ↦ X}) X) as F.
    intros Hprefix Hleast.
    rewrite eval_mu_simpl. simpl.
    unfold Fassoc in HeqF. rewrite HeqX in HeqF. rewrite -HeqF.
    apply LeastFixpoint_unique. { apply Hprefix. } apply Hleast.
  Qed.

  Lemma eval_mu_lfp_iff M ρ ϕ Sfix :
    well_formed_positive (patt_mu ϕ) ->
    let X := fresh_svar ϕ in
    let F := Fassoc ρ (ϕ^{svar: 0 ↦ X}) X in
    (
    (F Sfix) ⊆ Sfix /\
    (∀ S, (F S) ⊆ S -> Sfix ⊆ S)
    ) <-> Sfix = @eval Σ M ρ (patt_mu ϕ).
  Proof.
    intros Hwfp. simpl.
    remember (fresh_svar ϕ) as X.
    remember (Fassoc ρ (ϕ^{svar: 0 ↦ X}) X) as F.
    remember (@eval Σ M ρ (patt_mu ϕ)) as Sfix'.
    split.
    - intros [H1 H2]. subst.
      auto using eval_mu_if_lfp.
    - intros H. split.
      + subst.
        match goal with
        | |- ?L ⊆ ?R => assert (H: L = R)
        end.
        apply eval_mu_lfp_fixpoint. apply Hwfp.
        rewrite H. apply reflexivity.
      + intros S. subst. apply eval_mu_lfp_least. apply Hwfp.
  Qed.

  (* mu X. base \/ step X *)
  (* [Nats] = mu X. 0 \/ succ X *)
  (* [Nats] = { x | \ex x_0,x_1,..x_n . x_0 \in 0 /\ x_{i+1} \in succ x_i /\ x = x_n } *)
  (*  0, 1, 2,... x*)
  Section inductive_generation.
    Context (base step : Pattern).

    Let patt_ind_gen_body := (patt_or (nest_mu base) (patt_app (nest_mu step) (patt_bound_svar 0))).
    (* Let patt_ind_gen_simple_body := (patt_or base (patt_app step (patt_free_svar (fresh_svar patt_ind_gen_body)))). *)

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

    Lemma svar_open_patt_ind_gen_body_simpl M ρ X:
      svar_is_fresh_in X patt_ind_gen_body ->
      @eval Σ M ρ (patt_ind_gen_body^{svar: 0 ↦ X})
      = @eval Σ M ρ (patt_or base (patt_app step (patt_free_svar X))).
    Proof.
      intros Hfr.
      unfold svar_is_fresh_in in Hfr. simpl in Hfr.
      rewrite !simpl_free_svars in Hfr.
      apply sets.not_elem_of_union in Hfr.
      destruct Hfr as [Hfr1 Hfr2].

      rewrite /patt_ind_gen_body.
      unfold svar_open.
      mlSimpl. simpl.
      rewrite 2!eval_or_simpl.
      unfold nest_mu. rewrite 2!nest_mu_same.
      reflexivity.
    Qed.
    
    
    Section with_eval.
      Context (M : @Model Σ).
      Context (ρ : @Valuation Σ M).


      Let F := let X := fresh_svar patt_ind_gen_body in
               @Fassoc Σ M ρ (patt_ind_gen_body^{svar: 0 ↦ X}) X.
      (*
      Lemma svar_open_patt_ind_gen_body_assoc S:
        let X := fresh_svar patt_ind_gen_body in
        eval ρₑ (update_svar_val X S ρₛ) (svar_open 0 X patt_ind_gen_body)
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
      Lemma F_interp: F = λ A, (eval ρ base)
                                 ∪ (app_ext (eval ρ step) A).
      Proof.
        unfold F. unfold Fassoc. apply functional_extensionality.
        intros A. rewrite svar_open_patt_ind_gen_body_simpl.
        { apply set_svar_fresh_is_fresh. }

        rewrite eval_or_simpl.
        rewrite eval_app_simpl.
        rewrite eval_free_svar_simpl.
        rewrite update_svar_val_same.
        rewrite eval_free_svar_independent.
        {
          eapply svar_is_fresh_in_richer.
          2: { apply set_svar_fresh_is_fresh. }
          solve_free_svars_inclusion 5.
        }
        rewrite eval_free_svar_independent.
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
         | m₀::ms => (m₀ ∈ @eval Σ M ρ base)
                     /\  (@Forall _
                                  (λ (x : (Domain M) * (Domain M)),
                                   let (old, new) := x in
                                   new ∈ 
                                  app_ext
                                    (@eval Σ M ρ step)
                                    {[ old ]}
                                 )
                                 (zip (m₀::ms) ms)
                         )

         end).

      (* This sequence is the reversed version from the informal introduction in line 139 
         For example, for Nat model elements, the witnessing sequence for 5 is [5,4,3,2,1,0] *)
      Definition is_witnessing_sequence (m : Domain M) (l : list (Domain M)) :=
        (∃ lst, last l = Some lst /\ lst ∈ @eval Σ M ρ base)
          /\
          hd_error l = Some m
          /\
          ((@Forall _ (uncurry (λ new old,
                              new ∈
                     app_ext
                       (@eval Σ M ρ step)
                       {[old]}
                    ))
                    (zip l (tail l))
          )).

      (* If we have a witnessing sequence x₁ x₂ ... xₙ xₙ₊₁ ... xlast
         and xₙ matches `base`, then xₙ xₙ₊₁ is a witnessing sequence, too.
       *)
      Lemma witnessing_sequence_middle (m : Domain M) (l : list (Domain M)) (n : nat) (m' : Domain M) :
        is_witnessing_sequence m l ->
        l !! n = Some m' ->
        is_witnessing_sequence m' (drop n l).
      Proof.
        intros [[lst [Hlst Hbase] ] [Hhd Hfa] ] Hm'.
        split.
        { exists lst. split.
          rewrite -> last_drop with (x := lst).
          { reflexivity. }
          { apply Hlst. }
          { apply lookup_lt_is_Some_1.
            rewrite Hm'. exists m'. reflexivity.
          }
          apply Hbase.
        }
        split.
        { apply hd_drop_lookup. apply Hm'. }
        { rewrite tail_drop_comm.
          rewrite -zip_with_drop.
          apply Forall_drop.
          apply Hfa.
        }
      Qed.

      (* TODO: refactor, because this is a corollary of 'witnessing_sequence_middle'
         by using n = 1 *)
      Lemma witnessing_sequence_tail (m : Domain M) (l : list (Domain M)) (m' : Domain M) :
        is_witnessing_sequence m l ->
        head (tail l) = Some m' ->
        is_witnessing_sequence m' (tail l).
      Proof.
        intros Hw Hhead.
        unfold is_witnessing_sequence in Hw.
        destruct Hw as [[lst [Hlst1 Hlst2] ] Hw].
        unfold is_witnessing_sequence.
        split.
        { exists lst.
          split. 2: apply Hlst2.
          eapply last_tail. 2: apply Hhead. apply Hlst1.
        }
        split.
        { apply Hhead. }
        rewrite -tail_zip.
        apply Forall_tail.
        destruct Hw as [Hw1 Hw2].
        apply Hw2.
      Qed.

      Lemma is_witnessing_sequence_iff_is_witnessing_sequence_old_reverse (m : Domain M) (l : list (Domain M)) :
        is_witnessing_sequence m l <-> is_witnessing_sequence_old m (reverse l).
      Proof.
        assert (Feq: (uncurry
                        (flip
                           (λ new old : Domain M,
                                        new ∈
                                        app_ext
                                          (eval ρ step)
                                          {[old]})
                     ))
                     =  (λ x : Domain M * Domain M,
                               let (old, new) := x in
                               new ∈
                               app_ext
                                 (eval ρ step)
                                 {[old]})).

        { apply functional_extensionality. intros [x₁ x₂].
          reflexivity.
        }

        split.
        - intros [[m' [Hlast Hbase] ] [Hhd Hfa] ].
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
            rewrite length_reverse in H.
            simpl in H. inversion H.
          }

          assert (Hm'd: m' = d).
          {
            rewrite reverse_cons in Heq.
            pose proof (H := last_reverse_head _ l m).
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

          assert (Hfeq': (λ new old : Domain M, new ∈ app_ext (eval ρ step) {[old]}) = flip (flip (λ new old : Domain M, new ∈ app_ext (eval ρ step) {[old]}))).
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
         /\ (∃ step', step' ∈ eval ρ step /\ m' ∈ app_interp _ step' m)
              (* TODO: would this be easier to use/prove/understand to
                have `m' ∈ app_ext (eval ρ step) {[m]}` instead? *)
        ) <-> (is_witnessing_sequence m' (m'::l) /\ l ≠ []).
      Proof.
        split.
        - intros [[[lst [Hlst Hbase] ] [Hhd Hwit] ] [step' [Hstep' Hm'] ] ].
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
            specialize (IHl d erefl).
            destruct H1 as [step'' [d'' [Hstep'' [Hd'' Hstep''d''] ] ] ].
            inversion Hd''. subst d''. clear Hd''.
            specialize (IHl m step'' Hstep''d'' Hstep'').
            unfold is_witnessing_sequence in IHl.
            simpl in IHl.
            destruct IHl as [_ [_ Hforall] ].
            inversion Hforall. subst. apply H2.
        -
      Abort.


      Lemma witnessing_sequence_old_extend
            (m x m' : Domain M) (l : list (Domain M)):
        (is_witnessing_sequence_old m (x::l) /\
        ∃ step', (step' ∈ eval ρ step /\
        m' ∈ app_interp _ step' m)) <->
        (last (x::l) = Some m /\ is_witnessing_sequence_old m' ((x::l) ++ [m'])).
      Proof.
        split.
        -
          intros [Hwit [step' [Hstep' Hm'] ] ].
          destruct Hwit as [Hwit1 [Hwit2 Hwit3] ].
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
            destruct H1 as [step' [m'' [Hstep' [Hm'm'' Hstep'm''] ] ] ].
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
              destruct Hstep' as [m'' [Hstep' [Hmm'' Hm''] ] ].
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

      Definition witnessed_elements_old : propset (Domain M) :=
        PropSet (λ m, ∃ l, is_witnessing_sequence_old m l).

      Lemma witnessed_elements_old_prefixpoint : (F witnessed_elements_old) ⊆ witnessed_elements_old.
      Proof.
        rewrite elem_of_subseteq. intros x Hx.
        unfold F in Hx. unfold Fassoc in Hx. unfold svar_open in Hx. simpl in Hx.
        rewrite eval_or_simpl in Hx.
        fold ((nest_mu base)^{svar: 0 ↦ (fresh_svar patt_ind_gen_body)}) in Hx.
        fold ((nest_mu step)^{svar: 0 ↦ (fresh_svar patt_ind_gen_body)}) in Hx.
        destruct Hx.
        - unfold witnessed_elements_old.
          exists [x]. unfold is_witnessing_sequence_old.
          simpl.
          split.
          { reflexivity. }
          split.
          2: { constructor. }
          rewrite eval_free_svar_independent in H.
          {
            eapply svar_is_fresh_in_richer. 2: { subst. auto. }
            unfold svar_open.
            solve_free_svars_inclusion 5.
          }
          simpl. unfold svar_open in H.
          rewrite nest_mu_same in H. auto.
        - rewrite eval_app_simpl in H.
          rewrite eval_free_svar_simpl in H.
          rewrite update_svar_val_same in H.
          unfold app_ext in H.
          destruct H as [step' [m [H1 [H2 Happ] ] ] ].
          unfold witnessed_elements_old in H2.
          destruct H2 as [l Hl].

          unfold witnessed_elements_old.
          exists (l ++ [x]).

          (* `l` is not empty *)
          destruct l as [|m₀ l'] eqn:Heql.
          { unfold is_witnessing_sequence in Hl. destruct Hl. simpl in H. inversion H. }

          unfold svar_open in H1. rewrite nest_mu_same in H1.
          rewrite eval_free_svar_independent in H1.
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
        (@eval Σ M ρ patt_ind_gen) ⊆ witnessed_elements_old.
      Proof.
        apply eval_mu_lfp_least.
        { apply patt_ind_gen_wfp. }
        apply witnessed_elements_old_prefixpoint.
      Qed.

      Lemma eval_patt_ind_gen_fix :
        let Sfix := eval ρ patt_ind_gen in
        F Sfix = Sfix.
      Proof.
        apply eval_mu_lfp_fixpoint.
        apply patt_ind_gen_wfp.
      Qed.


      Definition witnessed_elements_old_of_max_len len : propset (Domain M) :=
        PropSet (λ m, ∃ l, is_witnessing_sequence_old m l /\ length l <= len).

      (* TODO: S len is needed? There is no elements that have an empty
               witnessing sequence. *)
      Lemma witnessed_elements_old_of_max_len_included_in_interp len:
        (witnessed_elements_old_of_max_len (S len)) ⊆ (@eval Σ M ρ patt_ind_gen).
      Proof.
        induction len.
        - intros m.
          rewrite -eval_patt_ind_gen_fix.
          intros H.
          unfold witnessed_elements_old_of_max_len.
          rewrite F_interp.
          destruct H as [l [Hwit Hlen] ].
          unfold is_witnessing_sequence in Hwit.
          destruct Hwit as [Hlast Hm].
          destruct l.
          { simpl in Hlast. inversion Hlast. }
          destruct l.
          2: { simpl in Hlen. lia. }
          simpl in Hlast. inversion Hlast. clear Hlast. subst.
          destruct Hm as [Hm _].
          left. apply Hm.
        - intros m.
          rewrite -eval_patt_ind_gen_fix.
          intros H.
          destruct H as [l [Hwit Hlen] ].
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
            left. apply Hd.
          + right.
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
              destruct P as [Hwitd [step' Hstep'] ].
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
            epose proof (Htot := (list_lookup_lookup_total_lt (rev (d0 :: x' :: l')) 1 _)).
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
              simpl.
              apply last_rev_head.
            }
            specialize (P (@conj _ _ Hm Hwit')). clear Hm Hwit'.
            destruct P as [Hwitmprev [step' [Hstep' Hm] ] ].
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
        witnessed_elements_old ⊆ (@eval Σ M ρ patt_ind_gen).
      Proof.
        intros x H.
        unfold witnessed_elements_old in H.
        destruct H as [wit Hwit].
        assert (H': x ∈ (witnessed_elements_old_of_max_len (length wit))).
        { exists wit. split. apply Hwit. lia. }
        destruct wit as [|y l'] eqn:Hl.
        { unfold is_witnessing_sequence in Hwit. destruct Hwit. contradiction. }
        eapply witnessed_elements_old_of_max_len_included_in_interp.
        simpl in H'.
        apply H'.
      Qed.

      Definition witnessed_elements : propset (Domain M) :=
        PropSet (λ m, ∃ l, is_witnessing_sequence m l).

      Lemma witnessed_elements_old_eq_witnessed_elements :
        witnessed_elements_old = witnessed_elements.
      Proof.
        rewrite -> set_eq_subseteq.
        repeat rewrite -> elem_of_subseteq.
        split;
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
        @eval Σ M ρ patt_ind_gen = witnessed_elements.
      Proof.
        rewrite -witnessed_elements_old_eq_witnessed_elements.
        rewrite -> set_eq_subseteq.
        split.
        + apply interp_included_in_witnessed_elements_old.
        + apply witnessed_elements_old_included_in_interp.
      Qed.

      Section injective.
        Hypothesis (Domain_eq_dec : EqDecision (Domain M)).
        Hypothesis (Hstep_total_function : @is_total_function _ M step witnessed_elements witnessed_elements ρ).
        Hypothesis (Hstep_injective : @total_function_is_injective _ M step witnessed_elements ρ).

        Hypothesis (Hbase_step_no_confusion
                    : (eval ρ base)
                        ∩ (app_ext (eval ρ step) witnessed_elements) = ∅).

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

          assert (Hmwit: m ∈ witnessed_elements).
          { exists l₁. apply Hw₁. }

          assert (Hlcom:  (common_length l₁ l₂ = length l₂)).
          {
            destruct Hw₁ as [[lst₁ [Hlst₁ Hbase₁] ] [Hhd₁ Hfa₁] ].
            destruct l₁ as [|m₁ l₁].
            { simpl in Hlst₁. inversion Hlst₁. }
            simpl in Hhd₁. inversion Hhd₁. subst. clear Hhd₁.

            destruct Hw₂ as [[lst₂ [Hlst₂ Hbase₂] ] [Hhd₂ Hfa₂] ].
            destruct l₂ as [|m₂ l₂].
            { simpl in Hlst₂. inversion Hlst₂. }
            simpl in Hhd₂. inversion Hhd₂. subst. clear Hhd₂.

            simpl.
            destruct (decide (m=m)).
            2: { contradiction. }
            clear e.
            apply f_equal.

            simpl in Hlen12. rename Hlen12 into Hlen12'.
            assert (Hlen12: length l₂ <= length l₁).
            { lia. }
            clear Hlen12'.

            remember (length l₁) as len₁.
            rewrite Heqlen₁ in Hlen12.
            assert (Hlen₁ : length l₁ <= len₁).
            { lia. }
            clear Heqlen₁.

            move: m l₁ l₂ Hlen12 Hlen₁ Hlst₁ Hlst₂ Hfa₁ Hfa₂ Hmwit.
            induction len₁; intros m l₁ l₂ Hlen12 Hlen₁ Hlst₁ Hlst₂ Hfa₁ Hfa₂ Hmwit.
            - destruct l₁.
              2: { simpl in Hlen₁. lia. }
              destruct l₂.
              + reflexivity.
              + assert (length (d::l₂) = 0).
                { simpl in Hlen12. lia. }
                rewrite H. reflexivity.
            - destruct l₂ as [|b l₂].
              { rewrite common_length_l_nil. reflexivity. }

              destruct l₁ as [|a l'₁] eqn:Heq.
              { simpl in Hlen12. lia. }


              simpl in Hfa₁. inversion Hfa₁. subst. clear Hfa₁.
              rename H1 into Hma. rename H2 into Hfa₁.
              simpl in Hfa₂. inversion Hfa₂. subst. clear Hfa₂.
              rename H1 into Hmb. rename H2 into Hfa₂.

              assert (Hwita: a ∈ witnessed_elements).
              { exists (a::l'₁).
                split.
                { exists lst₁. split.
                  { simpl in Hlst₁. simpl. apply Hlst₁. }
                  apply Hbase₁.
                }
                split.
                { reflexivity. }
                simpl. apply Hfa₁.
              }

              assert (Hwitb: b ∈ witnessed_elements).
              { exists (b::l₂).
                split.
                { exists lst₂. split.
                  { simpl in Hlst₂. simpl. apply Hlst₂. }
                  apply Hbase₂.
                }
                split.
                { reflexivity. }
                simpl. apply Hfa₂.
              }

              simpl in Hma. simpl in Hmb.

              assert (Ham: app_ext (eval ρ step) {[a]} = {[m]}).
              {
                unfold is_total_function in Hstep_total_function.
                pose proof (Hstep_total_function _ Hwita).
                destruct H as [a' [_ Ha'] ].
                rewrite Ha' in Hma.
                inversion Hma. subst.
                apply Ha'.
              }

              assert (Hbm: app_ext (eval ρ step) {[b]} = {[m]}).
              {
                unfold is_total_function in Hstep_total_function.
                pose proof (Hstep_total_function _ Hwitb).
                destruct H as [b' [_ Hb'] ].
                rewrite Hb' in Hmb.
                inversion Hmb. subst.
                apply Hb'.
              }

              assert (Haeqb: a = b).
              { apply Hstep_injective.
                apply Hwita. apply Hwitb.
                unfold rel_of.
                rewrite Ham.
                rewrite Hbm.
                reflexivity.
              }
              subst.
              clear Ham Hbm Hwita Hma.

              simpl.
              destruct (decide (b=b)).
              2: { contradiction. }
              apply f_equal.

              apply IHlen₁ with (m := b).
              { simpl in Hlen12.  lia. }
              { simpl in Hlen₁. lia. }
              simpl in Hlst₁. simpl. apply Hlst₁.
              simpl in Hlst₂. simpl. apply Hlst₂.

              simpl. apply Hfa₁.
              simpl. apply Hfa₂.
              apply Hwitb.
          }

          assert (Hlast12: l₁ !! (length l₂ - 1) = l₂ !! (length l₂ - 1)).
          {
            eapply equal_up_to_common_length.
            erewrite Hlcom.
            assert (length l₂ > 0).
            {
              destruct l₂.
              { unfold is_witnessing_sequence in Hw₂.
                simpl in Hw₂. destruct Hw₂ as [_ [Contra _] ].
                inversion Contra.
              }
              simpl. lia.
            }
            lia.
          }

          (*assert (Hbasem': eval ρ base lst).*)

          assert (~ (length l₁ > length l₂)).
          {
            intros Hcontra.
            assert (Hlt : length l₂ - 1 < length l₁).
            { lia. }
            pose proof (Hexm := list_ex_elem l₁ (length l₂ - 1) Hlt). clear Hlt.
            destruct Hexm as [m' Hm'].
            pose proof (Hwsm := witnessing_sequence_middle _ _ _ _ Hw₁ Hm').
            pose proof (Hw₂' := Hw₂).
            unfold is_witnessing_sequence in Hw₂'.
            destruct Hw₂' as [[lst [Hlst1 Hlst2] ] _].
            rewrite list_last_length in Hlst1.
            assert (Hlsteqm' : m' = lst).
            {
              assert (Some m' = Some lst).
              { rewrite -Hm'. rewrite -Hlst1. apply Hlast12.  }
              inversion H. reflexivity.
            }
            subst lst.
            specialize (Hwsm).
            clear Hm' Hlst1.

            destruct (drop (length l₂ - 1) l₁) eqn:Heq.
            {
              destruct Hwsm as [_ [Contra _] ].
              inversion Contra.
            }
            (* if `l` is empty, then length l₁ = length l₂ -> Contradiction *)
            destruct l.
            {
              assert (Hlendrop: length (drop (length l₂ - 1) l₁) = 1).
              { rewrite Heq. reflexivity. }
              rewrite length_drop in Hlendrop.
              assert (length l₂ <> 0).
              { intros Hcontra'.
                apply nil_length_inv in Hcontra'.
                subst l₂.
                destruct Hw₂ as [_ [HContra'' _] ].
                inversion HContra''.
              }
              lia.
            }
            (* `d0` is a member of `witnessed_elements` *)
            epose proof (Hwd0 := witnessing_sequence_tail _ _ _ Hwsm).
            simpl in Hwd0.
            assert (Htmp: Some d0 = Some d0).
            { reflexivity. }
            specialize (Hwd0 Htmp). clear Htmp.

            assert (Hd0we : d0 ∈ witnessed_elements).
            { exists (d0::l). apply Hwd0. }

            assert (Heqm'd : m' = d).
            { unfold is_witnessing_sequence in Hwsm.
              destruct Hwsm as [_ [H _] ].
              simpl in H. inversion H.
              reflexivity.
            }
            subst m'.

            (* `m'=d` matches `app_ext (eval ρ step) d0` *)
            assert (d ∈ app_ext
                      (eval ρ step)
                      {[d0]}).
            {
              unfold is_witnessing_sequence in Hwsm.
              simpl in Hwsm.
              destruct Hwsm as [_ [_ Hwsm] ].
              inversion Hwsm. subst.
              simpl in H1.
              apply H1.
            }
            rewrite -> set_eq_subseteq in Hbase_step_no_confusion.
            destruct Hbase_step_no_confusion as [H1 _].
            rewrite -> elem_of_subseteq in H1.
            specialize (H1 d).
            apply not_elem_of_empty in H1.
            { exact H1. }
            clear H1.
            split.
            - apply Hlst2.
            - unfold app_ext.
              destruct H as [le' [re' [H1 [H2 H3] ] ] ].
              exists le'. exists d0.
              split.
              { apply H1. }
              split.
              { apply Hd0we. }
              inversion H2. subst. apply H3.
          }
          assert (Hlength12: length l₁ = length l₂).
          { lia. }
          clear Hlen12 H.

          apply (common_length_impl_eq _ _ Hlength12 Hlcom).
        Qed.

      End injective.

    End with_eval.

  End inductive_generation.

End with_signature.
