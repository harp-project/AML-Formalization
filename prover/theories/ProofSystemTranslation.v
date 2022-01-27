From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Strings.String.
From Equations Require Import Equations.

From stdpp Require Export base.
From MatchingLogic Require Import Syntax Semantics SignatureHelper ProofSystem ProofMode.
From MatchingLogicProver Require Import Named NamedProofSystem NMatchers.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset list.

Import ProofSystem.Notations.

(* TODO: move this near to the definition of Pattern *)
Derive NoConfusion for Pattern.
Derive Subterm for Pattern.


Section proof_system_translation.

  Context
    {signature : Signature}
    {countable_symbols : Countable symbols}
  .

  Definition theory_translation (Gamma : Theory) : NamedTheory :=
    fmap to_NamedPattern2 Gamma.

  Definition well_formed_translation (phi : Pattern) (wfphi : is_true (well_formed phi))
    : (named_well_formed (to_NamedPattern2 phi)).
  Admitted.
   
  (*
  Print ML_proof_system. Check @hypothesis. Check N_hypothesis.
 Program Fixpoint translation (Gamma : Theory) (phi : Pattern) (prf : Gamma ⊢ phi)
   : (NP_ML_proof_system (theory_translation Gamma) (to_NamedPattern2 phi)) :=
   match prf with
   | @hypothesis _ _ a wfa inGamma
     => N_hypothesis (theory_translation Gamma) (to_NamedPattern2 a) _ _
   | _ => _
   end      
  .
   *)

  Definition Cache := gmap Pattern NamedPattern.

   (* If ϕ is in cache, then to_NamedPattern2' just returns the cached value
     and does not update anything.
   *)
  Lemma to_NamedPattern2'_lookup (ϕ : Pattern) (C : Cache) (evs : EVarSet) (svs : SVarSet):
    forall (nϕ : NamedPattern),
      C !! ϕ = Some nϕ ->
      to_NamedPattern2' ϕ C evs svs = (nϕ, C, evs, svs).
  Proof.
    intros nϕ H.
    destruct ϕ; simpl; case_match; rewrite H in Heqo; inversion Heqo; reflexivity.
  Qed.

  (* `to_NamedPattern2' ensures that the resulting cache is contains the given pattern *)
  Lemma to_NamedPattern2'_ensures_present (ϕ : Pattern) (C : Cache) (evs : EVarSet) (svs : SVarSet):
    (to_NamedPattern2' ϕ C evs svs).1.1.2 !! ϕ = Some ((to_NamedPattern2' ϕ C evs svs).1.1.1).
  Proof.
    destruct ϕ; simpl; repeat case_match; simpl;
      try (rewrite Heqo; reflexivity);
      try (rewrite lookup_insert; reflexivity).
  Qed.

  Instance incr_one_evar_inj : Inj eq eq incr_one_evar.
  Proof.
    unfold Inj. intros x y H.
    induction x,y; simpl in *; congruence.
  Qed.

  Instance incr_one_svar_inj : Inj eq eq incr_one_svar.
  Proof.
    unfold Inj. intros x y H.
    induction x,y; simpl in *; congruence.
  Qed.
  
  Lemma cache_incr_evar_lookup_None (ϕ : Pattern) (C : Cache):
    (forall b, ϕ <> patt_bound_evar b) ->
    cache_incr_evar C !! ϕ = None ->
    C !! ϕ = None.
  Proof.
    intros Hbv H.
    unfold cache_incr_evar in *.
    pose proof (H' := H).
    rewrite lookup_kmap_None in H.
    apply H.
    unfold incr_one_evar. case_match; auto.
    exfalso.
    subst. eapply Hbv. reflexivity.
  Qed.

  Lemma cache_incr_evar_lookup_Some (ϕ : Pattern) (nϕ : NamedPattern) (C : Cache):
    ~ is_bound_evar ϕ ->
    C !! ϕ = Some nϕ ->
    cache_incr_evar C !! ϕ = Some nϕ.
  Proof.
    intros Hbv H.
    unfold cache_incr_evar in *.
    rewrite lookup_kmap_Some.
    exists ϕ. split.
    - unfold incr_one_evar. case_match; auto.
      exfalso. apply Hbv. exists n. reflexivity.
    - assumption.
  Qed.

  Lemma cache_incr_svar_lookup_Some (ϕ : Pattern) (nϕ : NamedPattern) (C : Cache):
    ~ is_bound_svar ϕ ->
    C !! ϕ = Some nϕ ->
    cache_incr_svar C !! ϕ = Some nϕ.
  Proof.
    intros Hbv H.
    unfold cache_incr_svar in *.
    rewrite lookup_kmap_Some.
    exists ϕ. split.
    - unfold incr_one_svar. case_match; auto.
      exfalso. apply Hbv. exists n. reflexivity.
    - assumption.
  Qed.

  
  (* TODO: rename [bevar_occur] to [bevar_dangling] *)
  Definition evar_is_dangling (ϕ : Pattern) (b : db_index) :=
    bevar_occur ϕ b.

  Definition svar_is_dangling (ϕ : Pattern) (b : db_index) :=
    bsvar_occur ϕ b.

  Definition dangling_evars_cached (C : Cache) (ϕ : Pattern) : Prop :=
    forall (b : db_index),
      evar_is_dangling ϕ b ->
      exists nϕ,
        C !! (patt_bound_evar b) = Some nϕ.

  Definition dangling_svars_cached (C : Cache) (ϕ : Pattern) : Prop :=
    forall (b : db_index),
      svar_is_dangling ϕ b ->
      exists nϕ,
        C !! (patt_bound_svar b) = Some nϕ.

  Definition dangling_vars_cached (C : Cache) (ϕ : Pattern) : Prop :=
    dangling_evars_cached C ϕ /\ dangling_svars_cached C ϕ.

  Lemma dangling_vars_subcache (C C' : Cache) (ϕ : Pattern) :
    dangling_vars_cached C ϕ -> C ⊆ C' ->
    dangling_vars_cached C' ϕ.
  Proof.
    intros Hcached Hsub.
    unfold dangling_vars_cached, dangling_evars_cached,dangling_svars_cached in *.
    destruct Hcached as [Hecached Hscached].
    split; intros b Hb.
    - specialize (Hecached b Hb) as [nϕ Hnϕ].
      exists nϕ. eapply lookup_weaken. apply Hnϕ. assumption.
    - specialize (Hscached b Hb) as [nϕ Hnϕ].
      exists nϕ. eapply lookup_weaken. apply Hnϕ. assumption.
  Qed.

  Lemma to_NamedPattern2'_extends_cache (C : Cache) ϕ evs svs:
    C ⊆ (to_NamedPattern2' ϕ C evs svs).1.1.2.
  Proof.
    move: C evs svs.
    induction ϕ; intros C evs svs; simpl; case_match; simpl; auto; repeat case_match; simpl;
      apply insert_subseteq_r; try apply reflexivity; try assumption; subst.
    - inversion Heqp; subst; clear Heqp.
      specialize (IHϕ2 g e s0).
      rewrite Heqp3 in IHϕ2. simpl in IHϕ2. eapply transitivity;[|eassumption].
      specialize (IHϕ1 C evs svs).
      rewrite Heqp0 in IHϕ1. simpl in IHϕ1. assumption.
    - inversion Heqp; subst; clear Heqp.
      specialize (IHϕ2 g e s0).
      rewrite Heqp3 in IHϕ2. simpl in IHϕ2. eapply transitivity;[|eassumption].
      specialize (IHϕ1 C evs svs).
      rewrite Heqp0 in IHϕ1. simpl in IHϕ1. assumption.
    - inversion Heqp; subst; clear Heqp.
      replace g with (n, g, e0, s0).1.1.2 by reflexivity.
      rewrite -Heqp0. clear Heqp0.
      rewrite map_subseteq_spec.
      intros ψ nψ Hψ.
      destruct (decide (is_bound_evar ψ)).
      + rewrite lookup_union_r.
        { unfold remove_bound_evars. Search filter lookup None.
          apply map_filter_lookup_None_2.
          right. intros nψ'. intros _.
          unfold is_bound_evar_entry. simpl. intros HCC. apply HCC. assumption.
        }
        unfold keep_bound_evars.
        apply map_filter_lookup_Some_2.
        { exact Hψ. }
        { unfold is_bound_evar_entry. simpl. assumption. }
      + rewrite lookup_union_l.
        { unfold remove_bound_evars.
          unfold is_Some. exists nψ.
          apply map_filter_lookup_Some_2.
          { setoid_rewrite map_subseteq_spec in IHϕ.
            apply IHϕ.
            apply lookup_insert_Some.
            right.
            split.
            * intros Hcontra. apply n0. exists 0. subst. reflexivity.
            * apply cache_incr_evar_lookup_Some; assumption.
          }
          { intros Hcontra. apply n0. destruct Hcontra. simpl in H. subst ψ. exists x. reflexivity. }
        }
        unfold remove_bound_evars.
        apply map_filter_lookup_Some_2.
        { setoid_rewrite map_subseteq_spec in IHϕ.
          apply IHϕ.
          apply lookup_insert_Some.
          right.
          split.
          * intros Hcontra. apply n0. exists 0. subst. reflexivity.
          * apply cache_incr_evar_lookup_Some; assumption.
        }
        { intros Hcontra. apply n0. destruct Hcontra. simpl in H. subst ψ. exists x. reflexivity. }
    - inversion Heqp; subst; clear Heqp.
      replace g with (n, g, e0, s0).1.1.2 by reflexivity.
      rewrite -Heqp0. clear Heqp0.
      rewrite map_subseteq_spec.
      intros ψ nψ Hψ.
      destruct (decide (is_bound_svar ψ)).
      + rewrite lookup_union_r.
        { unfold remove_bound_evars. Search filter lookup None.
          apply map_filter_lookup_None_2.
          right. intros nψ'. intros _.
          unfold is_bound_evar_entry. simpl. intros HCC. apply HCC. assumption.
        }
        unfold keep_bound_svars.
        apply map_filter_lookup_Some_2.
        { exact Hψ. }
        { unfold is_bound_svar_entry. simpl. assumption. }
      + rewrite lookup_union_l.
        { unfold remove_bound_svars.
          unfold is_Some. exists nψ.
          apply map_filter_lookup_Some_2.
          { setoid_rewrite map_subseteq_spec in IHϕ.
            apply IHϕ.
            apply lookup_insert_Some.
            right.
            split.
            * intros Hcontra. apply n0. exists 0. subst. reflexivity.
            * apply cache_incr_svar_lookup_Some; assumption.
          }
          { intros Hcontra. apply n0. destruct Hcontra. simpl in H. subst ψ. exists x. reflexivity. }
        }
        unfold remove_bound_svars.
        apply map_filter_lookup_Some_2.
        { setoid_rewrite map_subseteq_spec in IHϕ.
          apply IHϕ.
          apply lookup_insert_Some.
          right.
          split.
          * intros Hcontra. apply n0. exists 0. subst. reflexivity.
          * apply cache_incr_svar_lookup_Some; assumption.
        }
        { intros Hcontra. apply n0. destruct Hcontra. simpl in H. subst ψ. exists x. reflexivity. }
  Qed. 

  (* A subpattern property of the cache: with any pattern it contains its direct subpatterns. *)
  Definition sub_prop (C : Cache) :=
    forall (p : Pattern) (np : NamedPattern),
      C !! p = Some np ->
      match p with
      | patt_free_evar _ => True
      | patt_free_svar _ => True
      | patt_bound_evar _ => True
      | patt_bound_svar _ => True
      | patt_bott => True
      | patt_sym _ => True
      | patt_imp p' q' => exists np' nq', C !! p' = Some np' /\ C !! q' = Some nq'
      | patt_app p' q' => exists np' nq', C !! p' = Some np' /\ C !! q' = Some nq'
      | patt_exists p' => exists np', C !! p' = Some np'
      | patt_mu p' => exists np', C !! p' = Some np'
      end.

  Lemma sub_prop_empty: sub_prop ∅.
  Proof.
    unfold sub_prop; intros; inversion H.
  Qed.

  Print to_NamedPattern2'.

  Lemma app_neq1 : forall x y, patt_app x y <> x.
  Proof.
    intros x y Hcontra.
    induction x; try discriminate.
    inversion Hcontra; subst. apply IHx1; assumption.
  Qed.

  Lemma app_neq2 : forall x y, patt_app x y <> y.
  Proof.
    intros x y Hcontra.
    induction y; try discriminate.
    inversion Hcontra; subst. apply IHy2; assumption.
  Qed.

  Lemma imp_neq1 : forall x y, patt_imp x y <> x.
  Proof.
    intros x y Hcontra.
    induction x; try discriminate.
    inversion Hcontra; subst. apply IHx1; assumption.
  Qed.

  Lemma imp_neq2 : forall x y, patt_imp x y <> y.
  Proof.
    intros x y Hcontra.
    induction y; try discriminate.
    inversion Hcontra; subst. apply IHy2; assumption.
  Qed.

  Lemma onlyAddsSubpatterns (C : Cache) (p : Pattern) (evs : EVarSet) (svs: SVarSet):
    forall (p' : Pattern),
      C !! p' = None ->
      (exists (np' : NamedPattern),
          (to_NamedPattern2' p C evs svs).1.1.2 !! p' = Some np') ->
      is_subformula_of_ind p' p.
  Proof. Admitted.

  Ltac invert_tuples :=
    repeat (match goal with
            | [H: (?x1,?y1)=(?x2,?y2) |- _] => inversion H; clear H; subst
            end).

        (* likely need invariant that caches are continuous for bound variables;
           that is, \exists k. \forall k'. patt_bound_evar k' \in C iff k' < k
           (and the same for bound_svar)
         *)
  Check npatt_evar.
  Definition cache_continuous_prop (C : Cache) : Prop :=
    (∃ (k : nat), ∀ (k' : nat),
        (k' < k)
        <->
          (∃ (e : evar), C !! (patt_bound_evar k') = Some (npatt_evar e))
    ) /\
      (∃ (k : nat), ∀ (k' : nat),
          (k' < k)
          <->          
            (∃ (s : svar), C !! (patt_bound_svar k') = Some (npatt_svar s))).

  Lemma cache_continuous_empty: cache_continuous_prop ∅.
  Proof.
    split; exists 0; intros; split; intros H.
    - lia.
    - destruct H as [e Hcontra]. inversion Hcontra.
    - lia.
    - destruct H as [e Hcontra]. inversion Hcontra.
  Qed.

  Definition is_bound_var (p : Pattern) :=
    match p with
    | patt_bound_evar _ => True
    | patt_bound_svar _ => True
    | _ => False
    end.
  
  Lemma cache_continuous_add_not_bound (C : Cache) (p : Pattern) (np : NamedPattern) :
    ~ is_bound_var p ->
    cache_continuous_prop C ->
    cache_continuous_prop (<[p := np]> C).
  Proof.
    intros Hneg Hcache.
    destruct Hcache as [Hcachee Hcaches].
    split.
    - destruct Hcachee as [k Hcachee].
      exists k; intros.
      specialize (Hcachee k').
      destruct Hcachee as [Hl Hr].
      split; intros.
      + specialize (Hl H).
        destruct Hl as [e Hl].
        exists e.
        rewrite <- Hl. eapply lookup_insert_ne.
        unfold not; destruct p; intros; try inversion H0.
        simpl in Hneg. apply Hneg. exact I.
      + apply Hr.
        destruct H as [e H].
        exists e.
        rewrite <- H. symmetry. eapply lookup_insert_ne.
        unfold not; destruct p; intros; try inversion H0.
        simpl in Hneg. apply Hneg. exact I.
    - destruct Hcaches as [k Hcaches].
      exists k; intros.
      specialize (Hcaches k').
      destruct Hcaches as [Hl Hr].
      split; intros.
      + specialize (Hl H).
        destruct Hl as [e Hl].
        exists e.
        rewrite <- Hl. eapply lookup_insert_ne.
        unfold not; destruct p; intros; try inversion H0.
        simpl in Hneg. apply Hneg. exact I.
      + apply Hr.
        destruct H as [e H].
        exists e.
        rewrite <- H. symmetry. eapply lookup_insert_ne.
        unfold not; destruct p; intros; try inversion H0.
        simpl in Hneg. apply Hneg. exact I.
  Qed.        
  
  Lemma cache_continuous_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet):
    dangling_vars_cached C p ->
    cache_continuous_prop C ->
    cache_continuous_prop (to_NamedPattern2' p C evs svs).1.1.2.
  Proof.
    intros Hcached Hsub.
    move: C Hcached Hsub evs svs.
    induction p; intros C Hcached Hsub evs svs; simpl; case_match; simpl; try apply Hsub.
    - admit.
    - admit.
    - destruct Hcached as [Hcachede Hcacheds].
      unfold dangling_evars_cached in Hcachede.
      specialize (Hcachede n). simpl in Hcachede.
      case_match;[|contradiction].
      specialize (Hcachede erefl).
      destruct Hcachede as [nϕ Hnϕ].
      rewrite Hnϕ in Heqo. inversion Heqo.
    - destruct Hcached as [Hcachede Hcacheds].
      unfold dangling_svars_cached in Hcacheds.
      specialize (Hcacheds n). simpl in Hcacheds.
      case_match;[|contradiction].
      specialize (Hcacheds erefl).
      destruct Hcacheds as [nϕ Hnϕ].
      rewrite Hnϕ in Heqo. inversion Heqo.
    - admit.
    - admit.
    - admit.
    - repeat case_match. subst. invert_tuples. simpl.
      unfold dangling_vars_cached in Hcached.
      destruct Hcached as [Hcachede Hcacheds].
      unfold dangling_evars_cached in Hcachede.
      unfold dangling_svars_cached in Hcacheds.
      
      specialize (IHp1 C).
      feed specialize IHp1.
      {
        split; unfold dangling_evars_cached; unfold dangling_svars_cached; intros.
        + apply Hcachede. simpl.
          rewrite H. reflexivity.
        + apply Hcacheds. simpl. rewrite H. reflexivity.
      }
      { apply Hsub. }
      specialize (IHp1 evs svs).
      rewrite Heqp0 in IHp1. simpl in IHp1.

      specialize (IHp2 g).
      feed specialize IHp2.
      {
        split; unfold dangling_evars_cached; unfold dangling_svars_cached; intros.
        + pose proof (Hextends := to_NamedPattern2'_extends_cache C p1 evs svs).
          rewrite Heqp0 in Hextends. simpl in Hextends.
          specialize (Hcachede b).
          feed specialize Hcachede.
          {
            simpl. rewrite H. apply orb_comm.
          }
          destruct Hcachede as [nϕ Hnϕ].
          exists nϕ.
          eapply lookup_weaken; eassumption.

        + pose proof (Hextends := to_NamedPattern2'_extends_cache C p1 evs svs).
          rewrite Heqp0 in Hextends. simpl in Hextends.
          specialize (Hcacheds b).
          feed specialize Hcacheds.
          {
            simpl. rewrite H. apply orb_comm.
          }
          destruct Hcacheds as [nϕ Hnϕ].
          exists nϕ.
          eapply lookup_weaken; eassumption.
      }
      { apply IHp1. }

      specialize (IHp2 e s0).
      rewrite Heqp1 in IHp2. simpl in IHp2.

      destruct IHp2 as [H1g H2g].
      split.
      + destruct H1g as [
      
      
      
      simpl
      simpl in Hcached.

      
  Lemma sub_prop_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet):
    sub_prop C ->
    sub_prop (to_NamedPattern2' p C evs svs).1.1.2.
  Proof.
    intros Hsub.
    move: C Hsub evs svs.
    induction p; intros C Hsub evs svs;
    lazymatch goal with
    | [|- (sub_prop (to_NamedPattern2' ?P _ _ _).1.1.2) ]
      => destruct (lookup P C) eqn:Hcache;
         [(unfold to_NamedPattern2'; simpl in *; rewrite Hcache; auto)
         |(simpl in *; rewrite Hcache; simpl)]
    end;
        unfold sub_prop; intros;
        try rename p0 into p00;
        rename p into p0;
      try lazymatch type of H with
      | <[?P := ?NP]> _ !! _ = _ =>
      destruct p0; auto;
      try (rewrite lookup_insert_Some in H;
        destruct H as [[H1 H2] | [H3 H4]]; subst; auto; try inversion H1;
        apply Hsub in H4;
        destruct H4 as [np' [nq' [H4 H5]]];
        destruct (decide (P = p0_1)), (decide (P = p0_2)); subst;
        [(exists NP, NP;
          split; apply lookup_insert)
        |(exists NP, nq';
          split; [(apply lookup_insert)|(
          rewrite <- H5;
          apply lookup_insert_ne; assumption)])
        |(exists np', NP;
          split; [(rewrite <- H4; apply lookup_insert_ne; assumption)
          |apply lookup_insert])
        |(exists np', nq';
          split; [(rewrite <- H4; apply lookup_insert_ne; assumption)|
                      (rewrite <- H5; apply lookup_insert_ne; assumption)])
      ]);
      try (rewrite lookup_insert_Some in H;
      destruct H as [[H1 H2] | [H3 H4]]; subst; auto; try inversion H1;
      apply Hsub in H4;
      destruct H4 as [np' H4];
      destruct (decide (P = p0)); subst;
      [(exists NP; apply lookup_insert)
      |(exists np'; rewrite <- H4; apply lookup_insert_ne; assumption)])
          end;

      repeat case_match; subst; auto; simpl in *; invert_tuples;
      rewrite lookup_insert_Some in H;

      try (pose proof (Hsub' := IHp1 C Hsub evs svs);
      rewrite Heqp0 in Hsub'; simpl in Hsub';
      pose proof (Hsub'' := IHp2 g0 Hsub' e0 s0);
      rewrite Heqp1 in Hsub''; simpl in Hsub'');

      destruct H as [[H H']|[H H']]; try inversion H; subst; clear H.
    
      * exists n0,n1.
        pose proof (Htmp := to_NamedPattern2'_ensures_present p8_1 C evs svs).
        rewrite Heqp0 in Htmp. simpl in Htmp.
        pose proof (Hec := to_NamedPattern2'_extends_cache g0 p8_2 e0 s0).
        rewrite Heqp1 in Hec. simpl in Hec.
        pose proof (Htmp2 := to_NamedPattern2'_ensures_present p8_2 g0 e0 s0).
        rewrite Heqp1 in Htmp2. simpl in Htmp2.
        eapply lookup_weaken with (m2 := g) in Htmp;[|assumption].
        rewrite -Htmp -Htmp2.
        split; apply lookup_insert_ne. apply app_neq1. apply app_neq2.

      * unfold sub_prop in Hsub''.
        pose proof (Htmp := Hsub'' (patt_app p8_1 p8_2) np H').
        simpl in Htmp. destruct Htmp as [np8_1 [np8_2 [Hp8_1 Hp8_2]]].
        destruct (decide (patt_app p1 p2 = p8_1)), (decide (patt_app p1 p2 = p8_2)); subst.
        -- exists (npatt_app n0 n1), (npatt_app n0 n1).
           split; apply lookup_insert.
        -- exists (npatt_app n0 n1), np8_2.
           split. apply lookup_insert.
           rewrite <- Hp8_2. apply lookup_insert_ne. assumption.
        -- exists np8_1, (npatt_app n0 n1).
           split. rewrite <- Hp8_1. apply lookup_insert_ne. assumption.
           apply lookup_insert.
        -- exists np8_1, np8_2.
           split. rewrite <- Hp8_1. apply lookup_insert_ne. assumption.
           rewrite <- Hp8_2. apply lookup_insert_ne. assumption.

      * unfold sub_prop in Hsub''.
        pose proof (Htmp := Hsub'' (patt_imp p8_1 p8_2) np H').
        simpl in Htmp. destruct Htmp as [np8_1 [np8_2 [Hp8_1 Hp8_2]]].
        destruct (decide (patt_app p1 p2 = p8_1)), (decide (patt_app p1 p2 = p8_2)); subst.
        -- exists (npatt_app n0 n1), (npatt_app n0 n1).
           split; apply lookup_insert.
        -- exists (npatt_app n0 n1), np8_2.
           split. apply lookup_insert.
           rewrite <- Hp8_2. apply lookup_insert_ne. assumption.
        -- exists np8_1, (npatt_app n0 n1).
           split. rewrite <- Hp8_1. apply lookup_insert_ne. assumption.
           apply lookup_insert.
        -- exists np8_1, np8_2.
           split. rewrite <- Hp8_1. apply lookup_insert_ne. assumption.
           rewrite <- Hp8_2. apply lookup_insert_ne. assumption.

      * unfold sub_prop in Hsub''.
        pose proof (Htmp := Hsub'' (patt_exists p8) np H').
        simpl in Htmp. destruct Htmp as [np8 Hp8].
        destruct (decide (patt_app p1 p2 = p8)); subst.
        -- exists (npatt_app n0 n1).
           apply lookup_insert.
        -- exists np8.
           rewrite <- Hp8. apply lookup_insert_ne. assumption.

      * unfold sub_prop in Hsub''.
        pose proof (Htmp := Hsub'' (patt_mu p8) np H').
        simpl in Htmp. destruct Htmp as [np8 Hp8].
        destruct (decide (patt_app p1 p2 = p8)); subst.
        -- exists (npatt_app n0 n1).
           apply lookup_insert.
        -- exists np8.
           rewrite <- Hp8. apply lookup_insert_ne. assumption.

      * unfold sub_prop in Hsub''.
        pose proof (Htmp := Hsub'' (patt_app p8_1 p8_2) np H').
        simpl in Htmp. destruct Htmp as [np8_1 [np8_2 [Hp8_1 Hp8_2]]].
        destruct (decide (patt_imp p1 p2 = p8_1)), (decide (patt_imp p1 p2 = p8_2)); subst.
        -- exists (npatt_imp n0 n1), (npatt_imp n0 n1).
           split; apply lookup_insert.
        -- exists (npatt_imp n0 n1), np8_2.
           split. apply lookup_insert.
           rewrite <- Hp8_2. apply lookup_insert_ne. assumption.
        -- exists np8_1, (npatt_imp n0 n1).
           split. rewrite <- Hp8_1. apply lookup_insert_ne. assumption.
           apply lookup_insert.
        -- exists np8_1, np8_2.
           split. rewrite <- Hp8_1. apply lookup_insert_ne. assumption.
           rewrite <- Hp8_2. apply lookup_insert_ne. assumption.

      * exists n0,n1.
        pose proof (Htmp := to_NamedPattern2'_ensures_present p8_1 C evs svs).
        rewrite Heqp0 in Htmp. simpl in Htmp.
        pose proof (Hec := to_NamedPattern2'_extends_cache g0 p8_2 e0 s0).
        rewrite Heqp1 in Hec. simpl in Hec.
        pose proof (Htmp2 := to_NamedPattern2'_ensures_present p8_2 g0 e0 s0).
        rewrite Heqp1 in Htmp2. simpl in Htmp2.
        eapply lookup_weaken with (m2 := g) in Htmp;[|assumption].
        rewrite -Htmp -Htmp2.
        split; apply lookup_insert_ne. apply imp_neq1. apply imp_neq2.

      * admit.
      * admit.
      * admit.

      * remember (evs ∪ {[evs_fresh evs p0]}) as evs'.
        remember (<[BoundVarSugar.b0:=npatt_evar (evs_fresh evs p0)]> (cache_incr_evar C)) as C'.
        (* need to show sub_prop C' holds *)
        (* likely need invariant that caches are continuous for bound variables;
           that is, \exists k. patt_bound_evar k' \in C iff k' < k
           (and the same for bound_svar)
         *)
        Print cache_incr_evar. Print incr_one_evar.
        Print to_NamedPattern2'.
        (* b0 ---> b0 *)
        pose proof (Hsub' := IHp C' Hsub evs' s).
        rewrite Heqp0 in Hsub'; simpl in Hsub'.
      pose proof (Hsub'' := IHp2 g0 Hsub' e0 s0);
      rewrite Heqp1 in Hsub''; simpl in Hsub'');


      * inversion Heqp; subst; clear Heqp.

          destruct Hsub as [np' [nq' Hsub]].
          exists np', nq'.
          pose proof (Hec := to_NamedPattern2'_extends_cache g0 p2 e0 s0).
          rewrite H1 in Hec. simpl in Hec.
          destruct Hsub as [Hp81 Hp82].
          split. eapply lookup_weaken. eassumption.

          destruct (g !! patt_app p1 p2) eqn:Hgapp.
          -- (* we want to show that patt_app p1 p2 is not in g *)
             (* from H1 and onlyAddsSubpatterns: g = g0 U p2 U subpatterns(p2) *)
             (* from Heqp0 and onlyAddsSubpatterns: g0 = C U p1 U subpatterns(p1) *)
             (* Hcache: patt_app p1 p2 is not in C *)
             (* therefore g = C U p1 U p2 U subpatterns(p1) U subpatterns(p2) *)
             (* thus patt_app p1 p2 cannot be in g *)
             pose proof (Hsp := onlyAddsSubpatterns C p1 evs svs (patt_app p1 p2) Hcache).
             pose proof (Hsp2 := onlyAddsSubpatterns g0 p2 e0 s0 (patt_app p1 p2)).
             rewrite Heqp0 in Hsp. simpl in Hsp.
             assert (~ is_subformula_of_ind (patt_app p1 p2) p1) by admit.
             exfalso. apply H0. apply Hsp. exists n.
  Admitted.

  (*
  Lemma sub_prop_subcache (C C' : Cache) :
    sub_prop C' -> map_subseteq C C' -> sub_prop C.
  Proof.
    intros. induction C.
    - unfold sub_prop. intros. destruct p; auto.
      unfold sub_prop in H. specialize (H (patt_imp p1 p2) np).
      destruct H as [np' [nq' [Hp1 Hp2]]]. eapply subcache_prop; eauto.
      exists np', nq'. split.
      (* need induction hypothesis *)
      admit. admit.
  Admitted.
   *)

  About to_NamedPattern2'.
  (* A correspondence property of the cache: any named pattern it contains is a translation
     of the locally nameless pattern that is its key, under some unspecified parameters.
     This should ensure that the named pattern has the same structure as the key. *)

  Print ex.

  Search last.

  (* s_1 $ s_2
     C0 = ∅
     1. to_namedPattern2'  (s_1 $ s_2) ∅
     1.1. to_namedPattern2' s_1  ∅  ==> {(s₁, ns₁)}. hist(_) => {[(s₁, (ns₁, ∅))] &  }
   *)
  Definition hist_entry := (@Pattern signature * ((@NamedPattern signature) * Cache * (@EVarSet signature) * (@SVarSet signature)))%type.
  
  Definition evs_of (h : hist_entry) : (@EVarSet signature) := h.2.1.2.
  Definition svs_of (h : hist_entry) : (@SVarSet signature) := h.2.2.
  
  Definition hist_prop (C : Cache) (history : list hist_entry) : Prop :=
    match history with
    | [] => False
    | (x::xs) =>
        x.2.1.1.2 = C /\
          (match (last (x::xs)) with
           | None => False
           | Some (p_l, x_l) => x_l = (to_NamedPattern2' p_l ∅ ∅ ∅)
           end) /\
          forall (i:nat),
            match xs!!i with
            | None => True
            (* p_i came from the result of the cache c_Si and everything before it *)
            | Some (p_Si, (np_Si, c_Si, evs_Si, svs_Si)) =>
                exists p_i,
                c_Si !! p_i = None /\
                  ((x::xs)!!i) = Some (p_i,(to_NamedPattern2' p_i c_Si evs_Si svs_Si))
            end
    end.

  Record History_generator (C : Cache) :=
    mkHistory {
        Hst_history : list hist_entry ;
        Hst_prop : hist_prop C Hst_history ;
    }.

  (*
  Lemma history_generator_subseteq (C₁ C₂ : Cache) :
    C₁ ⊆ C₂ ->
    history_generator C₂ ->
    history_generator C₁.
  Proof.
    intros Hsub Hc.
    unfold history_generator in *.
    destruct Hc as [history Hhistory].
    induction history.
    contradiction.
  Abort.
*)

  Lemma history_generator_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet)
    (hC : History_generator C) :
    fmap evs_of (head (Hst_history C hC)) = Some evs ->
    fmap svs_of (head (Hst_history C hC)) = Some svs ->
    History_generator (to_NamedPattern2' p C evs svs).1.1.2.
  Proof.
    intros Hevs Hsvs.
    destruct (C !! p) eqn:Hin.
    - exists (Hst_history C hC).
      unfold to_NamedPattern2'.
      destruct p; simpl; rewrite Hin; simpl;  destruct hC; simpl; assumption.
    - exists ((p, to_NamedPattern2' p C evs svs) :: (Hst_history C hC)).
      simpl.
      split;[reflexivity|].
      destruct hC. simpl in *.
      unfold hist_prop in Hst_prop0.
      destruct Hst_history0; [contradiction|].
      destruct Hst_prop0 as [Hcache [HhistoryC Hinner]].
      split; auto.
      destruct i; simpl.
      unfold evs_of, svs_of in *. simpl in *.
      inversion Hevs; inversion Hsvs; subst.
      repeat case_match; simpl in *; subst.
      + exists p. split. assumption. reflexivity.
      + exists p. split. assumption. reflexivity.
      + apply Hinner.
  Defined.

  Lemma consistency_pqp
        (p q : Pattern)
        (np' nq' np'' : NamedPattern)
        (cache : Cache)
        (evs : EVarSet)
        (svs : SVarSet):
    History_generator cache ->
    (to_NamedPattern2' (patt_imp p (patt_imp q p)) cache evs svs).1.1.1
    = npatt_imp np' (npatt_imp nq' np'') ->
    np'' = np'.
  Proof.

  (*
    (to_NamedPattern2' (p ---> (q ---> p)) cache used_evars used_svars).1.1.1
    (1) cache !! (p ---> (q ---> p)) = Some pqp'
        ===> = Some (p' ---> (q' ---> p'')), and p' = p''.
        we know that [exists cache1 used_evars' used_svars', (to_NamedPattern2' (p ---> (q ---> p)) cache1 used_evars' used_svars').1.1.1 = pqp'
       and cache1 !! (p ---> (q ---> p)) = None ].
       let (np, cache2) := to_NamedPattern2' p cache1 _ _.
       (* now, by to_NamedPattern2'_ensures_present, we have: [cache2 !! p = Some np] *)
       let (nqp, cache3) := to_NamedPattern2' (q ---> p) cache2 _ _.
       [
         let (nq, cache4) := to_NamedPattern2' q cache2 in
         (* by monotonicity lemma (TODO), cache2 \subseteq cache4 and therefore cache4 !! p = Some np *)
         let (np', cache5) := to_NamedPattern2' p cache4. (* now p is in cache4 *)
         By to_NamedPattern2'_lookup, np' = cache4 !! p = Some np.
         Q? (np' == np?)
       ]
   *)

  (*
     Non-Addition lemma. phi <= psi -> psi \not \in C -> psi \not \in (toNamedPattern2' phi C).2
   *)
  Equations? translation' (G : Theory) (phi : Pattern) (prf : G ⊢ phi)
           (cache : Cache) (pfsub : sub_prop cache) (pfcorr : History_generator cache)
           (used_evars : EVarSet) (used_svars : SVarSet)
    : (NP_ML_proof_system (theory_translation G)
                          (to_NamedPattern2' phi (cache)
                                             used_evars used_svars).1.1.1
       * Cache * EVarSet * SVarSet)%type by struct prf :=
    translation' G phi (hypothesis wfa inG) _ _ _ _ _
      := let: tn := to_NamedPattern2' phi cache used_evars used_svars in
         let: (_, cache', used_evars', used_svars') := tn in
         let: named_prf := N_hypothesis (theory_translation G) tn.1.1.1 _ _ in
         (named_prf, cache', used_evars', used_svars') ;

    translation' G phi (@P1 _ _ p q wfp wfq) _ _ _ _ _
      with (cache !! (patt_imp p (patt_imp q p))) => {
(*      | Some (npatt_imp p' (npatt_imp q' p'')) := (_, cache, used_evars, used_svars) ;*)
      | Some x with (nmatch_a_impl_b_impl_c x) => {
          | inl HisImp := (_, cache, used_evars, used_svars) ;
          | inr HisNotImp := (_, cache, used_evars, used_svars) ;
        }
      | None with (cache !! (patt_imp q p)) => {
        | None :=
          let: tn_p := to_NamedPattern2' p cache used_evars used_svars in
          let: (_, cache', used_evars', used_svars') := tn_p in
          let: tn_q := to_NamedPattern2' q cache' used_evars' used_svars' in
          let: (_, cache'', used_evars'', used_svars'') := tn_q in
          let: named_prf :=
            eq_rect _ _
                    (N_P1 (theory_translation G) tn_p.1.1.1 tn_q.1.1.1 _ _)
                    _ _ in
          (named_prf, cache'', used_evars'', used_svars'') ;
        | Some qp_named with qp_named => {
            | npatt_imp q' p' :=
              if (cache !! p) is Some p' then
                if (cache !! q) is Some q' then
                  let: named_prf :=
                     eq_rect _ _
                             (N_P1 (theory_translation G) p' q' _ _)
                             _ _ in
                  (named_prf, cache, used_evars, used_svars)
                else _
              else _
            | _ := _
          }
        } ;
      };
    (*
    translation' G phi (@P1 _ _ p q wfp wfq) _ _ _ _ _
      with (cache !! (patt_imp p (patt_imp q p))) => {
      | None with (cache !! (patt_imp q p)) => {
        | None :=
          let: tn_p := to_NamedPattern2' p cache used_evars used_svars in
          let: (_, cache', used_evars', used_svars') := tn_p in
          let: tn_q := to_NamedPattern2' q cache' used_evars' used_svars' in
          let: (_, cache'', used_evars'', used_svars'') := tn_q in
          let: named_prf :=
            eq_rect _ _
                    (N_P1 (theory_translation G) tn_p.1.1.1 tn_q.1.1.1 _ _)
                    _ _ in
          (named_prf, cache'', used_evars'', used_svars'') ;
        | Some qp_named := _ (* TODO *)
        } ;
      | Some pqp_named := _ (* TODO *)
      };
    *)
(*
      with ((cache !! (patt_imp p (patt_imp q p))), (cache !! (patt_imp q p)), (cache !! p), (cache !! q)) => {
      | ((Some pqp_named), None, _, _) := False_rect _ _ ;
      | (_, (Some qp_named), None, _) := False_rect _ _ ;
      | (_, (Some qp_named), _, None) := False_rect _ _;
      | ((Some pqp_named), (Some qp_named), (Some p_named), (Some q_named))
        := _ (* TODO *) ;
      | (None, (Some qp_named), (Some p_named), (Some q_named))
        := _ (* TODO *) ;
      | (None, None, _, _)
        := (* TODO *)
         let: tn_p := to_NamedPattern2' p cache used_evars used_svars in
         let: (_, cache', used_evars', used_svars') := tn_p in
         let: tn_q := to_NamedPattern2' q cache' used_evars' used_svars' in
         let: (_, cache'', used_evars'', used_svars'') := tn_q in
         let: named_prf :=
           eq_rect _ _
                   (N_P1 (theory_translation G) tn_p.1.1.1 tn_q.1.1.1 _ _)
                   _ _ in
         (named_prf, cache'', used_evars'', used_svars'') ;

      } ;
    *)
                                               
                 (*
      := if (pfcache !! phi) is Some (existT _ named_prf) then
           (named_prf, pfcache, used_evar, used_svars)
         else if (pfcache !! (psi ---> phi)) is Some (existT (named_imp)  _) then
           let: tn_phi := to_NamedPattern2' phi0 (to_NPCache _ pfcache) used_evars used_svars in
         let: (_, cache_phi, used_evars_phi, used_svars_phi) := tn_phi in
         let: tn_psi := to_NamedPattern2' psi cache used_evars_phi used_svars_phi in
         let: (_, cache_psi, used_evars_psi, used_svars_psi) := tn_psi in
         let: named_prf :=
           eq_rect _ _
                   (N_P1 (theory_translation G) tn_phi.1.1.1 tn_psi.1.1.1 _ _)
                   _ _ in
         (named_prf, cache_psi, used_evars_psi, used_svars_psi) ;
*)
    (*
    translation G phi (P2 psi xi wfphi wfpsi wfxi)
      := eq_rect _ _
                 (N_P2 (theory_translation G)
                       (to_NamedPattern2 phi1)
                       (to_NamedPattern2 psi)
                       (to_NamedPattern2 xi)
                       (well_formed_translation phi1 wfphi)
                       (well_formed_translation psi wfpsi)
                       (well_formed_translation xi wfxi))
                 _ _ ;
    translation G phi (P3 wfphi)
      := eq_rect _ _
                 (N_P3 (theory_translation G)
                       (to_NamedPattern2 phi2)
                       (well_formed_translation phi2 wfphi))
                 _ _ ;
    translation G phi (Modus_ponens phi wfphi3 wfphi3phi pfphi3 c)
      := N_Modus_ponens (theory_translation G)
                        (to_NamedPattern2 phi3)
                        (to_NamedPattern2 phi)
                        (well_formed_translation phi3 wfphi3)
                        _
                        (translation G phi3 pfphi3)
                        _ ;
    translation G phi (Ex_quan _ phi y)
      := eq_rect _ _
                 (N_Ex_quan (theory_translation G)
                            (to_NamedPattern2 phi)
                            (named_fresh_evar (to_NamedPattern2 phi))
                            y)
                 _ _ ;
*)
    translation' _ _ _ _ _ _ _ _ := _.

  Proof.
    all: try(
      lazymatch goal with
      | [ |- (Is_true (named_well_formed _)) ] => admit
      | _ => idtac
      end).
(*    - admit.*)
    - admit.
    - repeat case_match; simpl.
      + remember pfcorr as pfcorr'; clear Heqpfcorr'.
         Print history_generator.
        inversion pfcorr as [ | cache1 cache2 evs1 svs1 (patt_imp p (patt_imp q p)) ].
        { subst. inversion Heqo. }
        
        specialize (pfcorr' (patt_imp p (patt_imp q p)) n Heqo).
        destruct pfcorr' as [[[cache' evs'] svs'] [Hnone [H Hsub]]]. simpl in Hnone.
        simpl in H. rewrite Hnone in H. repeat case_match; subst.
        { inversion Heqp0; clear Heqp0; subst.
          inversion Heqp6; clear Heqp6; subst.
          (* Heqo: p --> q --> p ===> n1 --> n2 *)
          (* Heqo0: q --> p ===> n2 *)
          (* Heqp3: p ===> n1 *)
          simpl in *.
          Search to_NamedPattern2' Cache.
          (*  cache' ⊆ cache; cache' ⊆ g *)
          admit.
        }
        { inversion Heqp0; clear Heqp0; subst.
          inversion Heqp6; clear Heqp6; subst.
          inversion Heqp9; clear Heqp9; subst. simpl in *.
          (* This is the case we want *)
        }
        assert ({ pq | n = npatt_imp pq.1 (npatt_imp pq.2 pq.1) }). admit.
        destruct H0 as [[p' q'] Hpq].
        simpl (cache', evs', svs').1.1 in H. simpl (cache', evs', svs').1.2 in H.
        simpl (cache', evs', svs').2 in H. subst.
        repeat split. rewrite Hpq. simpl.
        apply N_P1. admit. admit.
        (* cache, evar_map, svar_map *)
        exact cache. apply used_evars. apply used_svars.
      + subst. inversion Heqp0; subst. clear Heqp0. inversion Heqp4; subst. clear Heqp4.
        admit.
      + admit.
    - repeat case_match; simpl.
      + remember pfcorr as pfcorr'; clear Heqpfcorr'.
        unfold history_generator in pfcorr'.
        specialize (pfcorr' (patt_imp p (patt_imp q p)) n Heqo).
        destruct pfcorr' as [[[cache' evs'] svs'] [Hnone [H Hsub]]]. simpl in Hnone.
        assert ({ pq | n = npatt_imp pq.1 (npatt_imp pq.2 pq.1) }) by admit.
        simpl (cache', evs', svs').1.1 in H. simpl (cache', evs', svs').1.2 in H.
        simpl (cache', evs', svs').2 in H. subst.
        apply translation'. apply P1; assumption.
        exact (sub_prop_subcache cache' cache pfsub Hsub).
        exact (history_generator_subcache cache' cache pfcorr Hsub).
      + admit.
      + admit.
    - case_match.
      + simpl.
        pose proof (pfcorr _ _ Heqo) as [cache0 [evs0 [svs0 [Hnone H]]]].
        simpl in H.
        rewrite Hnone in H. simpl in H.
        repeat case_match.
        * simpl in H. subst n1. inversion Heqp4. subst. clear Heqp4.
          inversion Heqp1. subst. clear Heqp1.
          (* We have just called [to_NamedPattern2'] with [p], and the resulting cache contains [q ---> p].
             Since [p] is a subpattern of [q ---> p], by lemma ??? we already had [q ---> p] before the call.
             (and with the same value.) That is, [cache0 !! q ---> p = Some n4].
           *)
          f_equal.
          -- 
          (*  *)
        * 
        rewrite H. simpl. (* FIXME this maybe is not enough. Maybe the cache needs to contain
        exactly the arguments with which the entry was created. *)
    (* hypothesis *)
    - admit
    - admit.
    (* P1 *)
    - admit.
    - admit.
    - simpl. case_match.
      + admit.
      + repeat case_match; simpl.
        * inversion Heqp3. subst. clear Heqp3.
          f_equal.
          inversion Heqp0. subst. clear Heqp0.
          admit.
        * inversion Heqp3. subst. clear Heqp3.
          f_equal.
          inversion Heqp0. subst. clear Heqp0.
          inversion Heqp1. subst. clear Heqp1.
         

      Search to_NamedPattern2'.
      Print Table Search Blacklist. simpl.
  Abort.

End proof_system_translation.
