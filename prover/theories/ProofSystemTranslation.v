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
        { unfold remove_bound_evars.
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
        { unfold remove_bound_evars.
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

  Definition is_bound_var (p : Pattern) :=
    match p with
    | patt_bound_evar _ => True
    | patt_bound_svar _ => True
    | _ => False
    end.

  Definition bound_or_cached (C : Cache) (p : Pattern) : Prop
    := is_bound_var p \/ exists np, C !! p = Some np.

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
      | patt_imp p' q' => bound_or_cached C p' /\ bound_or_cached C q'
      | patt_app p' q' => bound_or_cached C p' /\ bound_or_cached C q'
      | patt_exists p' => bound_or_cached C p'
      | patt_mu p' => bound_or_cached C p'
      end.

  Lemma sub_prop_empty: sub_prop ∅.
  Proof.
    unfold sub_prop; intros; inversion H.
  Qed.

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


  Ltac invert_tuples :=
    repeat (match goal with
            | [H: (?x1,?y1)=(?x2,?y2) |- _] => inversion H; clear H; subst
            end).

            
  Lemma dangling_vars_cached_ex_proj C p:
    dangling_vars_cached C (patt_exists p) ->
    dangling_vars_cached C p.
  Proof.
    intros H.
    unfold dangling_vars_cached in *.
    unfold dangling_evars_cached in *.
    unfold dangling_svars_cached in *.
    simpl in H.
  Abort.

  Lemma dangling_vars_cached_app_proj1 C p1 p2:
    dangling_vars_cached C (patt_app p1 p2) ->
    dangling_vars_cached C p1.
  Proof.
    intros Hcached.
    unfold dangling_vars_cached in Hcached.
    destruct Hcached as [Hcachede Hcacheds].
    unfold dangling_evars_cached in Hcachede.
    unfold dangling_svars_cached in Hcacheds.
    split; unfold dangling_evars_cached; unfold dangling_svars_cached; intros.
    + apply Hcachede. simpl.
      rewrite H. reflexivity.
    + apply Hcacheds. simpl. rewrite H. reflexivity.
  Qed.

  Lemma dangling_vars_cached_app_proj2 C p1 p2:
    dangling_vars_cached C (patt_app p1 p2) ->
    dangling_vars_cached C p2.
  Proof.
    intros Hcached.
    unfold dangling_vars_cached in Hcached.
    destruct Hcached as [Hcachede Hcacheds].
    unfold dangling_evars_cached in Hcachede.
    unfold dangling_svars_cached in Hcacheds.
    split; unfold dangling_evars_cached; unfold dangling_svars_cached; intros.
    + apply Hcachede. simpl.
      rewrite H. apply orb_comm.
    + apply Hcacheds. simpl. rewrite H. apply orb_comm.
  Qed.

  Lemma dangling_vars_cached_imp_proj1 C p1 p2:
    dangling_vars_cached C (patt_imp p1 p2) ->
    dangling_vars_cached C p1.
  Proof.
    intros Hcached.
    unfold dangling_vars_cached in Hcached.
    destruct Hcached as [Hcachede Hcacheds].
    unfold dangling_evars_cached in Hcachede.
    unfold dangling_svars_cached in Hcacheds.
    split; unfold dangling_evars_cached; unfold dangling_svars_cached; intros.
    + apply Hcachede. simpl.
      rewrite H. reflexivity.
    + apply Hcacheds. simpl. rewrite H. reflexivity.
  Qed.

  Lemma dangling_vars_cached_imp_proj2 C p1 p2:
    dangling_vars_cached C (patt_imp p1 p2) ->
    dangling_vars_cached C p2.
  Proof.
    intros Hcached.
    unfold dangling_vars_cached in Hcached.
    destruct Hcached as [Hcachede Hcacheds].
    unfold dangling_evars_cached in Hcachede.
    unfold dangling_svars_cached in Hcacheds.
    split; unfold dangling_evars_cached; unfold dangling_svars_cached; intros.
    + apply Hcachede. simpl.
      rewrite H. apply orb_comm.
    + apply Hcacheds. simpl. rewrite H. apply orb_comm.
  Qed.

  Lemma remove_disjoint_keep_e C1 C2:
  remove_bound_evars C1 ##ₘ keep_bound_evars C2.
Proof.
  unfold remove_bound_evars.
  unfold keep_bound_evars.
  rewrite map_disjoint_spec.
  intros i x y H1 H2.
  rewrite map_filter_lookup_Some in H1.
  destruct H1 as [H11 H12].
  unfold is_bound_evar_entry in H12. simpl in H12.
  rewrite map_filter_lookup_Some in H2. destruct H2 as [H21 H22].
  unfold is_bound_evar_entry in H22. simpl in H22.
  contradiction.
Qed.

Lemma remove_disjoint_keep_s C1 C2:
remove_bound_svars C1 ##ₘ keep_bound_svars C2.
Proof.
unfold remove_bound_svars.
unfold keep_bound_svars.
rewrite map_disjoint_spec.
intros i x y H1 H2.
rewrite map_filter_lookup_Some in H1.
destruct H1 as [H11 H12].
unfold is_bound_svar_entry in H12. simpl in H12.
rewrite map_filter_lookup_Some in H2. destruct H2 as [H21 H22].
unfold is_bound_svar_entry in H22. simpl in H22.
contradiction.
Qed.



  Lemma onlyAddsSubpatterns (C : Cache) (p : Pattern) (evs : EVarSet) (svs: SVarSet):
    dangling_vars_cached C p ->
    forall (p' : Pattern),
      C !! p' = None ->
      (exists (np' : NamedPattern),
          (to_NamedPattern2' p C evs svs).1.1.2 !! p' = Some np') ->
      is_subformula_of_ind p' p /\ ~is_bound_evar p' /\ ~ is_bound_svar p'.
  Proof.
    intros HCached.
    move: C evs svs HCached.
    induction p; intros C evs svs HCached p' HCp' [np' Hcall]; simpl in Hcall; case_match;
      simpl in Hcall; try (rewrite HCp' in Hcall; inversion Hcall).
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        split.
        { constructor. reflexivity. }
        split; intros HContra; inversion HContra; inversion H.
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        split.
        { constructor. reflexivity. }
        split; intros HContra; inversion HContra; inversion H.
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - rewrite lookup_insert_Some in Hcall.
      destruct HCached as [HCachede HCacheds].
      unfold dangling_evars_cached in HCachede.
      specialize (HCachede n).
      feed specialize HCachede.
      { unfold evar_is_dangling. simpl. case_match; auto. }
      destruct HCachede as [nphi Hnphi].
      rewrite Hnphi in Heqo.
      inversion Heqo.
    - rewrite lookup_insert_Some in Hcall.
      destruct HCached as [HCachede HCacheds].
      unfold dangling_svars_cached in HCacheds.
      specialize (HCacheds n).
      feed specialize HCacheds.
      { unfold svar_is_dangling. simpl. case_match; auto. }
      destruct HCacheds as [nphi Hnphi].
      rewrite Hnphi in Heqo.
      inversion Heqo.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        split.
        { constructor. reflexivity. }
        split; intros HContra; inversion HContra; inversion H.
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - repeat case_match. invert_tuples.
      simpl in *.
      pose proof (IH1 := IHp1 C evs svs).
      feed specialize IH1.
      { eapply dangling_vars_cached_app_proj1. apply HCached. }
      specialize (IH1 p').
      rewrite Heqp1 in IH1. simpl in IH1.
      pose proof (IH2 := IHp2 g0 e0 s0).
      pose proof (Hextends := to_NamedPattern2'_extends_cache C p1 evs svs).
      rewrite Heqp1 in Hextends. simpl in Hextends.
      feed specialize IH2.
      { eapply dangling_vars_subcache;[|apply Hextends].
      eapply dangling_vars_cached_app_proj2. apply HCached.
      }
      specialize (IH2 p').
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      {
        destruct Hcall; subst p' np'.
        split.
        { constructor. reflexivity. }
        split; intros Hcontra; inversion Hcontra; inversion H.
      }
      destruct Hcall as [Hp' Hgp'].
      rewrite Heqp2 in IH2. simpl in IH2.
      specialize (IH1 HCp').
      destruct (g0 !! p') eqn:Hg0p'.
      {
        feed specialize IH1.
        {
          exists n. reflexivity.
        }
        destruct IH1 as [Hp'p1 [Hbep' Hbsp']].
        split.
        {
          apply sub_app_l. exact Hp'p1.
        }
        split. apply Hbep'. apply Hbsp'.
      }
      specialize (IH2 Hg0p').
      feed specialize IH2.
      {
        exists np'. exact Hgp'.
      }
      destruct IH2 as [Hp'p2 [Hbep' Hbsp']].
      split.
      {
        apply sub_app_r. exact Hp'p2.
      }
      split. exact Hbep'. exact Hbsp'.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        split.
        { constructor. reflexivity. }
        split; intros HContra; inversion HContra; inversion H.
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - repeat case_match. invert_tuples.
    simpl in *.
    pose proof (IH1 := IHp1 C evs svs).
    feed specialize IH1.
    { eapply dangling_vars_cached_app_proj1. apply HCached. }
    specialize (IH1 p').
    rewrite Heqp1 in IH1. simpl in IH1.
    pose proof (IH2 := IHp2 g0 e0 s0).
    pose proof (Hextends := to_NamedPattern2'_extends_cache C p1 evs svs).
    rewrite Heqp1 in Hextends. simpl in Hextends.
    feed specialize IH2.
    { eapply dangling_vars_subcache;[|apply Hextends].
    eapply dangling_vars_cached_app_proj2. apply HCached.
    }
    specialize (IH2 p').
    rewrite lookup_insert_Some in Hcall.
    destruct Hcall as [Hcall|Hcall].
    {
      destruct Hcall; subst p' np'.
      split.
      { constructor. reflexivity. }
      split; intros Hcontra; inversion Hcontra; inversion H.
    }
    destruct Hcall as [Hp' Hgp'].
    rewrite Heqp2 in IH2. simpl in IH2.
    specialize (IH1 HCp').
    destruct (g0 !! p') eqn:Hg0p'.
    {
      feed specialize IH1.
      {
        exists n. reflexivity.
      }
      destruct IH1 as [Hp'p1 [Hbep' Hbsp']].
      split.
      {
        apply sub_imp_l. exact Hp'p1.
      }
      split. apply Hbep'. apply Hbsp'.
    }
    specialize (IH2 Hg0p').
    feed specialize IH2.
    {
      exists np'. exact Hgp'.
    }
    destruct IH2 as [Hp'p2 [Hbep' Hbsp']].
    split.
    {
      apply sub_imp_r. exact Hp'p2.
    }
    split. exact Hbep'. exact Hbsp'.
    - repeat case_match. invert_tuples.
      simpl in *.
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      { destruct Hcall as [Hp' Hnp']. subst p' np'.
        split. constructor. reflexivity.
        split; intros Hcontra; inversion Hcontra; inversion H.
      }
      destruct Hcall as [Hp' Hnp'].
      rewrite lookup_union_Some in Hnp'.
      2: { apply remove_disjoint_keep_e. }
      destruct Hnp' as [Hnp'|Hnp'].
      {
        unfold remove_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hg0p' Hbep'].
        pose proof (IH := IHp (<[BoundVarSugar.b0:=npatt_evar (evs_fresh evs p)]>
        (cache_incr_evar C)) (evs ∪ {[evs_fresh evs p]}) s).
        rewrite Heqp3 in IH. simpl in IH.
        feed specialize IH.
        {
          unfold dangling_vars_cached. unfold dangling_vars_cached in HCached.
          destruct HCached as [HCachede HCacheds].
          split.
          + unfold dangling_evars_cached.
            intros b Hpb.
            destruct b.
            {
              exists (npatt_evar (evs_fresh evs p)).
              apply lookup_insert.
            }
            specialize (HCachede b).
            simpl in HCachede. specialize (HCachede Hpb).
            destruct HCachede as [nphi Hnphi].
            exists nphi.
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_evar.
            replace (patt_bound_evar (S b)) with (incr_one_evar (patt_bound_evar b)) by reflexivity.
            rewrite lookup_kmap_Some.
            exists (patt_bound_evar b).
            split;[reflexivity|].
            exact Hnphi.
          + unfold dangling_svars_cached.
            intros b Hpb.
            specialize (HCacheds b).
            simpl in HCacheds. specialize (HCacheds Hpb).
            destruct HCacheds as [nphi Hnphi].
            exists nphi.
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_evar.
            replace (patt_bound_svar b) with (incr_one_evar (patt_bound_svar b)) by reflexivity.
            rewrite lookup_kmap_Some.
            exists (patt_bound_svar b).
            split;[reflexivity|].
            exact Hnphi.
        }
        specialize (IH p').
        unfold is_bound_evar_entry in Hbep'. simpl in Hbep'.
        feed specialize IH.
        {
          destruct (decide (p' = BoundVarSugar.b0)).
          {
            subst p'. exfalso. apply Hbep'. exists 0. reflexivity.
          }
          rewrite lookup_insert_ne.
          { apply not_eq_sym. assumption. }
          unfold cache_incr_evar.
          replace p' with (incr_one_evar p').
          2: {
            destruct p'; simpl; try reflexivity.
            exfalso. apply Hbep'. exists n1. reflexivity.
          }
          rewrite lookup_kmap_None.
          intros p'' Hp''.
          apply (inj incr_one_evar) in Hp''.
          subst p''.
          exact HCp'.
        }
        {
          exists np'. exact Hg0p'.
        }
        destruct IH as [Hsub [Hbe Hbs]].
        split.
        { apply sub_exists. exact Hsub. }
        split. exact Hbe. exact Hbs.
      }
      {
        unfold keep_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hcontra _]. rewrite HCp' in Hcontra. inversion Hcontra.
      }
    - repeat case_match. invert_tuples.
      simpl in *.
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      { destruct Hcall as [Hp' Hnp']. subst p' np'.
       split. constructor. reflexivity.
       split; intros Hcontra; inversion Hcontra; inversion H.
      }
      destruct Hcall as [Hp' Hnp'].
      rewrite lookup_union_Some in Hnp'.
      2: { apply remove_disjoint_keep_s. }
      destruct Hnp' as [Hnp'|Hnp'].
      {
        unfold remove_bound_svars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hg0p' Hbep'].
        pose proof (IH := IHp (<[BoundVarSugar.B0:=npatt_svar (svs_fresh s p)]>
        (cache_incr_svar C)) evs (s ∪ {[svs_fresh s p]})).
        rewrite Heqp3 in IH. simpl in IH.
        feed specialize IH.
        {
          unfold dangling_vars_cached. unfold dangling_vars_cached in HCached.
          destruct HCached as [HCachede HCacheds].
          split.
          + unfold dangling_evars_cached.
            intros b Hpb.
            specialize (HCachede b).
            simpl in HCachede. specialize (HCachede Hpb).
            destruct HCachede as [nphi Hnphi].
            exists nphi.
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_svar.
            replace (patt_bound_evar b) with (incr_one_svar (patt_bound_evar b)) by reflexivity.
            rewrite lookup_kmap_Some.
            exists (patt_bound_evar b).
            split;[reflexivity|].
            exact Hnphi.
          + unfold dangling_svars_cached.
            intros b Hpb.
            destruct b.
            {
              exists (npatt_svar (svs_fresh s p)).
              apply lookup_insert.
            }
            specialize (HCacheds b).
            simpl in HCacheds. specialize (HCacheds Hpb).
            destruct HCacheds as [nphi Hnphi].
            exists nphi.
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_svar.
            replace (patt_bound_svar (S b)) with (incr_one_svar (patt_bound_svar b)) by reflexivity.
            rewrite lookup_kmap_Some.
            exists (patt_bound_svar b).
            split;[reflexivity|].
            exact Hnphi.
        }
        specialize (IH p').
        unfold is_bound_svar_entry in Hbep'. simpl in Hbep'.
        feed specialize IH.
        {
          destruct (decide (p' = BoundVarSugar.B0)).
          {
            subst p'. exfalso. apply Hbep'. exists 0. reflexivity.
          }
          rewrite lookup_insert_ne.
          { apply not_eq_sym. assumption. }
          unfold cache_incr_svar.
          replace p' with (incr_one_svar p').
          2: {
            destruct p'; simpl; try reflexivity.
            exfalso. apply Hbep'. exists n1. reflexivity.
          }
          rewrite lookup_kmap_None.
          intros p'' Hp''.
          apply (inj incr_one_svar) in Hp''.
          subst p''.
          exact HCp'.
        }
        {
          exists np'. exact Hg0p'.
        }
        destruct IH as [Hsub [Hbe Hbs]].
        split.
        { apply sub_mu. exact Hsub. }
        split. exact Hbe. exact Hbs.
      }
      {
        unfold keep_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hcontra _]. rewrite HCp' in Hcontra. inversion Hcontra.
      }
  Qed.

  Lemma onlyAddsSubpatterns2 (C : Cache) (p : Pattern) (evs : EVarSet) (svs: SVarSet):
    forall (p' : Pattern),
      C !! p' = None ->
      (exists (np' : NamedPattern),
          (to_NamedPattern2' p C evs svs).1.1.2 !! p' = Some np') ->
      is_subformula_of_ind p' p.
  Proof.
    move: C evs svs.
    induction p; intros C evs svs p' HCp' [np' Hcall]; simpl in Hcall; case_match;
      simpl in Hcall; try (rewrite HCp' in Hcall; inversion Hcall).
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        { constructor. reflexivity. }
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        { constructor. reflexivity. }
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      {
        destruct Hcall. subst. constructor. reflexivity.
      }
      {
        destruct Hcall as [_ HContra]. rewrite HCp' in HContra. inversion HContra.
      }
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      {
        destruct Hcall. subst. constructor. reflexivity.
      }
      {
        destruct Hcall as [_ HContra]. rewrite HCp' in HContra. inversion HContra.
      }
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        { constructor. reflexivity. }
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - repeat case_match. invert_tuples.
      simpl in *.
      pose proof (IH1 := IHp1 C evs svs).
      specialize (IH1 p').
      rewrite Heqp1 in IH1. simpl in IH1.
      pose proof (IH2 := IHp2 g0 e0 s0).
      pose proof (Hextends := to_NamedPattern2'_extends_cache C p1 evs svs).
      rewrite Heqp1 in Hextends. simpl in Hextends.
      specialize (IH2 p').
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      {
        destruct Hcall; subst p' np'.
        { constructor. reflexivity. }
      }
      destruct Hcall as [Hp' Hgp'].
      rewrite Heqp2 in IH2. simpl in IH2.
      specialize (IH1 HCp').
      destruct (g0 !! p') eqn:Hg0p'.
      {
        feed specialize IH1.
        {
          exists n. reflexivity.
        }
        apply sub_app_l. exact IH1.
      }
      specialize (IH2 Hg0p').
      feed specialize IH2.
      {
        exists np'. exact Hgp'.
      }
      apply sub_app_r. exact IH2.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        { constructor. reflexivity. }
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - repeat case_match. invert_tuples.
    simpl in *.
    pose proof (IH1 := IHp1 C evs svs).
    specialize (IH1 p').
    rewrite Heqp1 in IH1. simpl in IH1.
    pose proof (IH2 := IHp2 g0 e0 s0).
    pose proof (Hextends := to_NamedPattern2'_extends_cache C p1 evs svs).
    rewrite Heqp1 in Hextends. simpl in Hextends.
    specialize (IH2 p').
    rewrite lookup_insert_Some in Hcall.
    destruct Hcall as [Hcall|Hcall].
    {
      destruct Hcall; subst p' np'.
      { constructor. reflexivity. }
    }
    destruct Hcall as [Hp' Hgp'].
    rewrite Heqp2 in IH2. simpl in IH2.
    specialize (IH1 HCp').
    destruct (g0 !! p') eqn:Hg0p'.
    {
      feed specialize IH1.
      {
        exists n. reflexivity.
      }
      apply sub_imp_l. exact IH1.
    }
    specialize (IH2 Hg0p').
    feed specialize IH2.
    {
      exists np'. exact Hgp'.
    }
    apply sub_imp_r. exact IH2.
    - repeat case_match. invert_tuples.
      simpl in *.
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      { destruct Hcall as [Hp' Hnp']. subst p' np'.
        constructor. reflexivity.
      }
      destruct Hcall as [Hp' Hnp'].
      rewrite lookup_union_Some in Hnp'.
      2: { apply remove_disjoint_keep_e. }
      destruct Hnp' as [Hnp'|Hnp'].
      {
        unfold remove_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hg0p' Hbep'].
        pose proof (IH := IHp (<[BoundVarSugar.b0:=npatt_evar (evs_fresh evs p)]>
        (cache_incr_evar C)) (evs ∪ {[evs_fresh evs p]}) s).
        rewrite Heqp3 in IH. simpl in IH.
        specialize (IH p').
        unfold is_bound_evar_entry in Hbep'. simpl in Hbep'.
        feed specialize IH.
        {
          destruct (decide (p' = BoundVarSugar.b0)).
          {
            subst p'. exfalso. apply Hbep'. exists 0. reflexivity.
          }
          rewrite lookup_insert_ne.
          { apply not_eq_sym. assumption. }
          unfold cache_incr_evar.
          replace p' with (incr_one_evar p').
          2: {
            destruct p'; simpl; try reflexivity.
            exfalso. apply Hbep'. exists n1. reflexivity.
          }
          rewrite lookup_kmap_None.
          intros p'' Hp''.
          apply (inj incr_one_evar) in Hp''.
          subst p''.
          exact HCp'.
        }
        {
          exists np'. exact Hg0p'.
        }
        { apply sub_exists. exact IH. }
      }
      {
        unfold keep_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hcontra _]. rewrite HCp' in Hcontra. inversion Hcontra.
      }
    - repeat case_match. invert_tuples.
      simpl in *.
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      { destruct Hcall as [Hp' Hnp']. subst p' np'.
       constructor. reflexivity.
      }
      destruct Hcall as [Hp' Hnp'].
      rewrite lookup_union_Some in Hnp'.
      2: { apply remove_disjoint_keep_s. }
      destruct Hnp' as [Hnp'|Hnp'].
      {
        unfold remove_bound_svars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hg0p' Hbep'].
        pose proof (IH := IHp (<[BoundVarSugar.B0:=npatt_svar (svs_fresh s p)]>
        (cache_incr_svar C)) evs (s ∪ {[svs_fresh s p]})).
        rewrite Heqp3 in IH. simpl in IH.
        specialize (IH p').
        unfold is_bound_svar_entry in Hbep'. simpl in Hbep'.
        feed specialize IH.
        {
          destruct (decide (p' = BoundVarSugar.B0)).
          {
            subst p'. exfalso. apply Hbep'. exists 0. reflexivity.
          }
          rewrite lookup_insert_ne.
          { apply not_eq_sym. assumption. }
          unfold cache_incr_svar.
          replace p' with (incr_one_svar p').
          2: {
            destruct p'; simpl; try reflexivity.
            exfalso. apply Hbep'. exists n1. reflexivity.
          }
          rewrite lookup_kmap_None.
          intros p'' Hp''.
          apply (inj incr_one_svar) in Hp''.
          subst p''.
          exact HCp'.
        }
        {
          exists np'. exact Hg0p'.
        }
        { apply sub_mu. exact IH. }
      }
      {
        unfold keep_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hcontra _]. rewrite HCp' in Hcontra. inversion Hcontra.
      }
  Qed.

  Lemma doesNotAddBoundVars (C : Cache) (p : Pattern) (evs : EVarSet) (svs: SVarSet):
    dangling_vars_cached C p ->
    forall (p' : Pattern),
      C !! p' = None ->
      (exists (np' : NamedPattern),
          (to_NamedPattern2' p C evs svs).1.1.2 !! p' = Some np') ->
      ~is_bound_evar p' /\ ~ is_bound_svar p'.
  Proof.
    intros HCached.
    move: C evs svs HCached.
    induction p; intros C evs svs HCached p' HCp' [np' Hcall]; simpl in Hcall; case_match;
      simpl in Hcall; try (rewrite HCp' in Hcall; inversion Hcall).
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        split; intros HContra; inversion HContra; inversion H.
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        split; intros HContra; inversion HContra; inversion H.
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - rewrite lookup_insert_Some in Hcall.
      destruct HCached as [HCachede HCacheds].
      unfold dangling_evars_cached in HCachede.
      specialize (HCachede n).
      feed specialize HCachede.
      { unfold evar_is_dangling. simpl. case_match; auto. }
      destruct HCachede as [nphi Hnphi].
      rewrite Hnphi in Heqo.
      inversion Heqo.
    - rewrite lookup_insert_Some in Hcall.
      destruct HCached as [HCachede HCacheds].
      unfold dangling_svars_cached in HCacheds.
      specialize (HCacheds n).
      feed specialize HCacheds.
      { unfold svar_is_dangling. simpl. case_match; auto. }
      destruct HCacheds as [nphi Hnphi].
      rewrite Hnphi in Heqo.
      inversion Heqo.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        split; intros HContra; inversion HContra; inversion H.
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - repeat case_match. invert_tuples.
      simpl in *.
      pose proof (IH1 := IHp1 C evs svs).
      feed specialize IH1.
      { eapply dangling_vars_cached_app_proj1. apply HCached. }
      specialize (IH1 p').
      rewrite Heqp1 in IH1. simpl in IH1.
      pose proof (IH2 := IHp2 g0 e0 s0).
      pose proof (Hextends := to_NamedPattern2'_extends_cache C p1 evs svs).
      rewrite Heqp1 in Hextends. simpl in Hextends.
      feed specialize IH2.
      { eapply dangling_vars_subcache;[|apply Hextends].
      eapply dangling_vars_cached_app_proj2. apply HCached.
      }
      specialize (IH2 p').
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      {
        destruct Hcall; subst p' np'.
        split; intros Hcontra; inversion Hcontra; inversion H.
      }
      destruct Hcall as [Hp' Hgp'].
      rewrite Heqp2 in IH2. simpl in IH2.
      specialize (IH1 HCp').
      destruct (g0 !! p') eqn:Hg0p'.
      {
        feed specialize IH1.
        {
          exists n. reflexivity.
        }
        destruct IH1 as [Hbep' Hbsp'].
        split. apply Hbep'. apply Hbsp'.
      }
      specialize (IH2 Hg0p').
      feed specialize IH2.
      {
        exists np'. exact Hgp'.
      }
      destruct IH2 as [Hbep' Hbsp'].
      split. exact Hbep'. exact Hbsp'.
    - rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      + destruct Hcall as [Hp' Hnp'].
        subst.
        split; intros HContra; inversion HContra; inversion H.
      + destruct Hcall as [Hp' Hnp'].
        subst.
        rewrite HCp' in Hnp'.
        inversion Hnp'.
    - repeat case_match. invert_tuples.
    simpl in *.
    pose proof (IH1 := IHp1 C evs svs).
    feed specialize IH1.
    { eapply dangling_vars_cached_app_proj1. apply HCached. }
    specialize (IH1 p').
    rewrite Heqp1 in IH1. simpl in IH1.
    pose proof (IH2 := IHp2 g0 e0 s0).
    pose proof (Hextends := to_NamedPattern2'_extends_cache C p1 evs svs).
    rewrite Heqp1 in Hextends. simpl in Hextends.
    feed specialize IH2.
    { eapply dangling_vars_subcache;[|apply Hextends].
    eapply dangling_vars_cached_app_proj2. apply HCached.
    }
    specialize (IH2 p').
    rewrite lookup_insert_Some in Hcall.
    destruct Hcall as [Hcall|Hcall].
    {
      destruct Hcall; subst p' np'.
      split; intros Hcontra; inversion Hcontra; inversion H.
    }
    destruct Hcall as [Hp' Hgp'].
    rewrite Heqp2 in IH2. simpl in IH2.
    specialize (IH1 HCp').
    destruct (g0 !! p') eqn:Hg0p'.
    {
      feed specialize IH1.
      {
        exists n. reflexivity.
      }
      destruct IH1 as [Hbep' Hbsp'].
      split. apply Hbep'. apply Hbsp'.
    }
    specialize (IH2 Hg0p').
    feed specialize IH2.
    {
      exists np'. exact Hgp'.
    }
    destruct IH2 as [Hbep' Hbsp'].
    
    split. exact Hbep'. exact Hbsp'.
    - repeat case_match. invert_tuples.
      simpl in *.
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      { destruct Hcall as [Hp' Hnp']. subst p' np'.
        split; intros Hcontra; inversion Hcontra; inversion H.
      }
      destruct Hcall as [Hp' Hnp'].
      rewrite lookup_union_Some in Hnp'.
      2: { apply remove_disjoint_keep_e. }
      destruct Hnp' as [Hnp'|Hnp'].
      {
        unfold remove_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hg0p' Hbep'].
        pose proof (IH := IHp (<[BoundVarSugar.b0:=npatt_evar (evs_fresh evs p)]>
        (cache_incr_evar C)) (evs ∪ {[evs_fresh evs p]}) s).
        rewrite Heqp3 in IH. simpl in IH.
        feed specialize IH.
        {
          unfold dangling_vars_cached. unfold dangling_vars_cached in HCached.
          destruct HCached as [HCachede HCacheds].
          split.
          + unfold dangling_evars_cached.
            intros b Hpb.
            destruct b.
            {
              exists (npatt_evar (evs_fresh evs p)).
              apply lookup_insert.
            }
            specialize (HCachede b).
            simpl in HCachede. specialize (HCachede Hpb).
            destruct HCachede as [nphi Hnphi].
            exists nphi.
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_evar.
            replace (patt_bound_evar (S b)) with (incr_one_evar (patt_bound_evar b)) by reflexivity.
            rewrite lookup_kmap_Some.
            exists (patt_bound_evar b).
            split;[reflexivity|].
            exact Hnphi.
          + unfold dangling_svars_cached.
            intros b Hpb.
            specialize (HCacheds b).
            simpl in HCacheds. specialize (HCacheds Hpb).
            destruct HCacheds as [nphi Hnphi].
            exists nphi.
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_evar.
            replace (patt_bound_svar b) with (incr_one_evar (patt_bound_svar b)) by reflexivity.
            rewrite lookup_kmap_Some.
            exists (patt_bound_svar b).
            split;[reflexivity|].
            exact Hnphi.
        }
        specialize (IH p').
        unfold is_bound_evar_entry in Hbep'. simpl in Hbep'.
        feed specialize IH.
        {
          destruct (decide (p' = BoundVarSugar.b0)).
          {
            subst p'. exfalso. apply Hbep'. exists 0. reflexivity.
          }
          rewrite lookup_insert_ne.
          { apply not_eq_sym. assumption. }
          unfold cache_incr_evar.
          replace p' with (incr_one_evar p').
          2: {
            destruct p'; simpl; try reflexivity.
            exfalso. apply Hbep'. exists n1. reflexivity.
          }
          rewrite lookup_kmap_None.
          intros p'' Hp''.
          apply (inj incr_one_evar) in Hp''.
          subst p''.
          exact HCp'.
        }
        {
          exists np'. exact Hg0p'.
        }
        destruct IH as [Hbe Hbs].
        split. exact Hbe. exact Hbs.
      }
      {
        unfold keep_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hcontra _]. rewrite HCp' in Hcontra. inversion Hcontra.
      }
    - repeat case_match. invert_tuples.
      simpl in *.
      rewrite lookup_insert_Some in Hcall.
      destruct Hcall as [Hcall|Hcall].
      { destruct Hcall as [Hp' Hnp']. subst p' np'.
       split; intros Hcontra; inversion Hcontra; inversion H.
      }
      destruct Hcall as [Hp' Hnp'].
      rewrite lookup_union_Some in Hnp'.
      2: { apply remove_disjoint_keep_s. }
      destruct Hnp' as [Hnp'|Hnp'].
      {
        unfold remove_bound_svars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hg0p' Hbep'].
        pose proof (IH := IHp (<[BoundVarSugar.B0:=npatt_svar (svs_fresh s p)]>
        (cache_incr_svar C)) evs (s ∪ {[svs_fresh s p]})).
        rewrite Heqp3 in IH. simpl in IH.
        feed specialize IH.
        {
          unfold dangling_vars_cached. unfold dangling_vars_cached in HCached.
          destruct HCached as [HCachede HCacheds].
          split.
          + unfold dangling_evars_cached.
            intros b Hpb.
            specialize (HCachede b).
            simpl in HCachede. specialize (HCachede Hpb).
            destruct HCachede as [nphi Hnphi].
            exists nphi.
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_svar.
            replace (patt_bound_evar b) with (incr_one_svar (patt_bound_evar b)) by reflexivity.
            rewrite lookup_kmap_Some.
            exists (patt_bound_evar b).
            split;[reflexivity|].
            exact Hnphi.
          + unfold dangling_svars_cached.
            intros b Hpb.
            destruct b.
            {
              exists (npatt_svar (svs_fresh s p)).
              apply lookup_insert.
            }
            specialize (HCacheds b).
            simpl in HCacheds. specialize (HCacheds Hpb).
            destruct HCacheds as [nphi Hnphi].
            exists nphi.
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_svar.
            replace (patt_bound_svar (S b)) with (incr_one_svar (patt_bound_svar b)) by reflexivity.
            rewrite lookup_kmap_Some.
            exists (patt_bound_svar b).
            split;[reflexivity|].
            exact Hnphi.
        }
        specialize (IH p').
        unfold is_bound_svar_entry in Hbep'. simpl in Hbep'.
        feed specialize IH.
        {
          destruct (decide (p' = BoundVarSugar.B0)).
          {
            subst p'. exfalso. apply Hbep'. exists 0. reflexivity.
          }
          rewrite lookup_insert_ne.
          { apply not_eq_sym. assumption. }
          unfold cache_incr_svar.
          replace p' with (incr_one_svar p').
          2: {
            destruct p'; simpl; try reflexivity.
            exfalso. apply Hbep'. exists n1. reflexivity.
          }
          rewrite lookup_kmap_None.
          intros p'' Hp''.
          apply (inj incr_one_svar) in Hp''.
          subst p''.
          exact HCp'.
        }
        {
          exists np'. exact Hg0p'.
        }
        destruct IH as [Hbe Hbs].
        split. exact Hbe. exact Hbs.
      }
      {
        unfold keep_bound_evars in Hnp'.
        rewrite map_filter_lookup_Some in Hnp'.
        destruct Hnp' as [Hcontra _]. rewrite HCp' in Hcontra. inversion Hcontra.
      }
  Qed.

  Definition cache_continuous_prop (C : Cache) : Prop :=
    (∃ (k : nat), ∀ (k' : nat),
        (k' < k)
        <->
          (∃ (np : NamedPattern), C !! (patt_bound_evar k') = Some np)
    ) /\
      (∃ (k : nat), ∀ (k' : nat),
          (k' < k)
          <->          
            (∃ (np : NamedPattern), C !! (patt_bound_svar k') = Some np)).

  Lemma cache_continuous_empty: cache_continuous_prop ∅.
  Proof.
    split; exists 0; intros; split; intros H.
    - lia.
    - destruct H as [e Hcontra]. inversion Hcontra.
    - lia.
    - destruct H as [e Hcontra]. inversion Hcontra.
  Qed.

  
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

  Lemma cache_continuous_shift_e C e:
    cache_continuous_prop C ->
    cache_continuous_prop (
          <[BoundVarSugar.b0:=npatt_evar e]>
          (cache_incr_evar C)).
  Proof.
    intros [Hconte Hconts].
    split.
    + destruct Hconte as [k Hk]. exists (S k). intros k'.
      split; intros H.
      * destruct k'.
        --
          exists (npatt_evar e).
          apply lookup_insert.
        --
          specialize (Hk k').
          destruct Hk as [Hk1 Hk2].
          specialize (Hk1 ltac:(lia)).
          destruct Hk1 as [e' He'].
          exists e'.
          rewrite lookup_insert_ne.
          { discriminate. }
          unfold cache_incr_evar.
          replace (patt_bound_evar (S k')) with (incr_one_evar (patt_bound_evar k')) by reflexivity.
          rewrite lookup_kmap.
          exact He'.
      * destruct H as [e' He'].
        destruct k'.
        { lia. }
        cut (k' < k).
        { lia. }
        rewrite Hk.
        rewrite lookup_insert_ne in He'.
        { discriminate. }
        unfold cache_incr_evar in He'.
        replace (patt_bound_evar (S k')) with (incr_one_evar (patt_bound_evar k')) in He' by reflexivity.
        rewrite lookup_kmap in He'.
        exists e'. exact He'.

    + destruct Hconts as [k Hk]. exists k. intros k'.
      rewrite lookup_insert_ne.
      { discriminate. }
      unfold cache_incr_evar.
      replace (patt_bound_svar k') with (incr_one_evar (patt_bound_svar k')) by reflexivity.
      rewrite lookup_kmap.
      apply Hk.
  Qed. 

  Lemma cache_continuous_shift_s C s:
    cache_continuous_prop C ->
    cache_continuous_prop (
          <[BoundVarSugar.B0:=npatt_svar s]>
          (cache_incr_svar C)).
  Proof.
  intros [Hconte Hconts].
  split.
  + destruct Hconte as [k Hk]. exists (k). intros k'.
    rewrite lookup_insert_ne.
    { discriminate. }
    unfold cache_incr_svar.
    replace (patt_bound_evar k')
      with (incr_one_svar (patt_bound_evar k'))
      by reflexivity.
    rewrite lookup_kmap.
    apply Hk.
  + destruct Hconts as [k Hk].
    exists (S k). intros k'. split.
    * intros Hk'.
      destruct k'.
      --
        exists (npatt_svar s).
        apply lookup_insert.
      --
        specialize (Hk k').
        destruct Hk as [Hk1 Hk2].
        specialize (Hk1 ltac:(lia)).
        destruct Hk1 as [np Hnp].
        exists np.
        rewrite lookup_insert_ne.
        { discriminate. }
        unfold cache_incr_svar.
        replace (patt_bound_svar (S k'))
          with (incr_one_svar (patt_bound_svar k'))
          by reflexivity.
        rewrite lookup_kmap.
        exact Hnp.
    * intros H.
      destruct H as [np Hnp].
      rewrite lookup_insert_Some in Hnp.
      destruct Hnp as [Hnp|Hnp].
      --
        destruct Hnp as [Hnp1 Hnp2].
        inversion Hnp1. subst k' np.
        lia.
      --
        destruct Hnp as [Hk' Hck'].
        unfold cache_incr_svar in Hck'.
        destruct (decide (k' = k)).
        {
          subst k'. lia.
        }

        destruct k'.
        {
          contradiction.
        }
        replace (patt_bound_svar (S k'))
          with (incr_one_svar (patt_bound_svar k'))
          in Hck' by reflexivity.
        rewrite lookup_kmap in Hck'.
        cut (k' < k).
        { intros. lia. }
        apply Hk.
        exists np.
        apply Hck'.
  Qed.

  Lemma cache_continuous_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet):
    dangling_vars_cached C p ->
    cache_continuous_prop C ->
    cache_continuous_prop (to_NamedPattern2' p C evs svs).1.1.2.
  Proof.
    intros Hcached Hsub.
    move: C Hcached Hsub evs svs.
    induction p; intros C Hcached Hsub evs svs; simpl; case_match; simpl; try apply Hsub.
    - apply cache_continuous_add_not_bound;[|exact Hsub].
      intros Hcontra.
      inversion Hcontra.
    - apply cache_continuous_add_not_bound;[|exact Hsub].
      intros Hcontra.
      inversion Hcontra.
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
    - apply cache_continuous_add_not_bound;[|exact Hsub].
      intros Hcontra.
      inversion Hcontra.
    - repeat case_match. subst. invert_tuples. simpl.
      
      specialize (IHp1 C).
      feed specialize IHp1.
      { eapply dangling_vars_cached_app_proj1. apply Hcached. }
      { apply Hsub. }
      specialize (IHp1 evs svs).
      rewrite Heqp0 in IHp1. simpl in IHp1.


      unfold dangling_vars_cached in Hcached.
      destruct Hcached as [Hcachede Hcacheds].
      unfold dangling_evars_cached in Hcachede.
      unfold dangling_svars_cached in Hcacheds.
    
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
      apply cache_continuous_add_not_bound.
      intros Hcontra. inversion Hcontra.
      apply IHp2.
    - apply cache_continuous_add_not_bound;[|exact Hsub].
      intros Hcontra.
      inversion Hcontra.
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
      apply cache_continuous_add_not_bound.
      intros Hcontra. inversion Hcontra.
      apply IHp2.
    - repeat case_match. subst. invert_tuples. simpl.
      unfold dangling_vars_cached in Hcached.
      destruct Hcached as [Hcachede Hcacheds].
      unfold dangling_evars_cached in Hcachede.
      unfold dangling_svars_cached in Hcacheds.
      specialize (IHp (<[BoundVarSugar.b0:=npatt_evar (evs_fresh evs p)]>
      (cache_incr_evar C))).
      feed specialize IHp.
      {
        split; unfold dangling_evars_cached; unfold dangling_svars_cached; intros.
        + destruct b.
          {
            exists (npatt_evar (evs_fresh evs p)).
            apply lookup_insert.
          }
          pose proof (Hcachedeb := Hcachede b H).
          destruct Hcachedeb as [nphi Hnphi].
          exists nphi.
          rewrite -Hnphi.
          rewrite lookup_insert_ne.
          { discriminate. }
          unfold cache_incr_evar.
          replace (patt_bound_evar (S b)) with (incr_one_evar (patt_bound_evar b)) by reflexivity.
          apply lookup_kmap. apply _.
        + rewrite lookup_insert_ne.
          { discriminate. }
          pose proof (Hcachedsb := Hcacheds b H).
          destruct Hcachedsb as [nphi Hnphi].
          exists nphi. rewrite -Hnphi.
          replace (patt_bound_svar (b)) with (incr_one_evar (patt_bound_svar b)) by reflexivity.
          apply lookup_kmap. apply _.
      }
      {
        apply cache_continuous_shift_e. apply Hsub.
      }
      pose proof (IHp0 := IHp (evs ∪ {[evs_fresh evs p]}) s).
      rewrite Heqp1 in IHp0. simpl in IHp0.
      apply cache_continuous_add_not_bound.
      { intros Hcontra. inversion Hcontra. }
      unfold cache_continuous_prop.
      destruct IHp0 as [Hge Hgs].
      destruct Hsub as [HCe HCs].
      split.
      + destruct HCe as [k Hk].
        exists k. intros k'.
        split; intros H.
        * rewrite Hk in H.
          destruct H as [e He].
          exists e.
          rewrite lookup_union_Some.
          --
            right.
            unfold keep_bound_evars.
            rewrite map_filter_lookup_Some.
            split.
            ++
              exact He.
            ++ unfold is_bound_evar_entry. simpl. exists k'. reflexivity.
          -- apply remove_disjoint_keep_e.
        * apply Hk.
          destruct H as [e He].
          exists e.
          rewrite lookup_union_Some in He.
          2: { apply remove_disjoint_keep_e. }
          destruct He as [He|He].
          --
            unfold remove_bound_evars in He.
            rewrite map_filter_lookup_Some in He.
            destruct He as [He1 He2].
            unfold is_bound_evar_entry in He2. simpl in He2.
            exfalso. apply He2. exists k'. reflexivity.
          --
            unfold keep_bound_evars in He.
            rewrite map_filter_lookup_Some in He.
            destruct He as [He1 He2].
            exact He1.
      + destruct HCs as [k Hk].
        exists k.
        intros k'.
        split; intros H.
        * rewrite Hk in H.
          destruct H as [s1 Hs1].
          exists s1.
          apply lookup_union_Some.
          { apply remove_disjoint_keep_e.  }
          left.
          unfold remove_bound_evars.
          rewrite map_filter_lookup_Some.
          split.
          {
            epose proof (Hext := to_NamedPattern2'_extends_cache _ _ _ _).
            erewrite Heqp1 in Hext. simpl in Hext.
            eapply lookup_weaken;[|eassumption].
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_evar.
            rewrite lookup_kmap_Some.
            exists (patt_bound_svar k').
            split.
            * reflexivity.
            * exact Hs1.
          }
          { unfold is_bound_evar_entry. simpl. intros [witness Hwitness].
            inversion Hwitness.
          }
        * destruct H as [s1 Hs1].
          destruct (C !! patt_bound_svar k') eqn:Hck'.
          {
            rewrite Hk.
            exists n0. exact Hck'.
          }
          {
            destruct Hgs as [k2 Hk2].
            clear Hge HCe.
            (* If [C] does not contain [k'], and [g] contains it,
              then something is wrong.
              Bound variables are added to the cache only temporarily,
              for the recursive calls.
            *)
            rewrite lookup_union_Some in Hs1.
            2: {
              apply remove_disjoint_keep_e.
            }
            destruct Hs1 as [Hs1|Hs1].
            2: {
              unfold keep_bound_evars in Hs1.
              rewrite map_filter_lookup_Some in Hs1.
              destruct Hs1 as [Hs11 Hs12].
              rewrite Hck' in Hs11. inversion Hs11.
            }
            unfold remove_bound_evars in Hs1.
            rewrite map_filter_lookup_Some in Hs1.
            destruct Hs1 as [Hgk' _].
            pose proof (Hoas := onlyAddsSubpatterns (<[BoundVarSugar.b0:=npatt_evar (evs_fresh evs p)]>
            (cache_incr_evar C)) p (evs ∪ {[evs_fresh evs p]}) s).
            feed specialize Hoas.
            {
              split.
              + unfold dangling_evars_cached.
                intros b Hb.
                destruct b.
                {
                  exists (npatt_evar (evs_fresh evs p)).
                  apply lookup_insert.
                }
                specialize (Hcachede b Hb).
                destruct Hcachede as [nphi Hnphi].
                exists nphi.
                rewrite lookup_insert_ne.
                { discriminate. }
                unfold cache_incr_evar.
                replace (patt_bound_evar (S b))
                  with (incr_one_evar (patt_bound_evar b))
                  by reflexivity.
                rewrite lookup_kmap.
                exact Hnphi.
              + unfold dangling_svars_cached.
                intros b Hb.
                rewrite lookup_insert_ne.
                { discriminate. }
                specialize (Hcacheds b Hb).
                destruct Hcacheds as [nphi Hnphi].
                exists nphi.
                unfold cache_incr_evar.
                replace (patt_bound_svar b)
                  with (incr_one_evar (patt_bound_svar b))
                  by reflexivity.
                rewrite lookup_kmap.
                exact Hnphi.
            }
            specialize (Hoas (patt_bound_svar k')).
            feed specialize Hoas.
            {
              rewrite lookup_insert_None.
              split;[|discriminate].
              unfold cache_incr_evar.
              rewrite lookup_kmap_None.
              intros p'' Hp''.
              replace (patt_bound_svar k')
                with (incr_one_evar (patt_bound_svar k'))
                in Hp'' by reflexivity.
              apply (inj incr_one_evar) in Hp''.
              subst p''.
              exact Hck'.
            }
            {
              rewrite Heqp1. simpl.
              exists s1. exact Hgk'.
            }
            destruct Hoas as [_ [_ Hcontra]].
            exfalso. apply Hcontra. exists k'. reflexivity.
          }
    - repeat case_match. subst. invert_tuples. simpl.
      unfold dangling_vars_cached in Hcached.
      destruct Hcached as [Hcachede Hcacheds].
      unfold dangling_evars_cached in Hcachede.
      unfold dangling_svars_cached in Hcacheds.
      specialize (IHp (<[BoundVarSugar.B0:=npatt_svar (svs_fresh s p)]>
          (cache_incr_svar C))).
      feed specialize IHp.
      {
        split; unfold dangling_evars_cached; unfold dangling_svars_cached; intros.
        + rewrite lookup_insert_ne.
          { discriminate. }
          pose proof (Hcachedeb := Hcachede b H).
          destruct Hcachedeb as [nphi Hnphi].
          exists nphi. rewrite -Hnphi.
          replace (patt_bound_evar (b)) with (incr_one_svar (patt_bound_evar b)) by reflexivity.
          apply lookup_kmap. apply _.
        + destruct b.
          {
            exists (npatt_svar (svs_fresh s p)).
            apply lookup_insert.
          }
          pose proof (Hcachedsb := Hcacheds b H).
          destruct Hcachedsb as [nphi Hnphi].
          exists nphi.
          rewrite -Hnphi.
          rewrite lookup_insert_ne.
          { discriminate. }
          unfold cache_incr_svar.
          replace (patt_bound_svar (S b)) with (incr_one_svar (patt_bound_svar b)) by reflexivity.
          apply lookup_kmap. apply _.
      }
      {
        apply cache_continuous_shift_s. apply Hsub.
      }
      pose proof (IHp0 := IHp evs (s ∪ {[svs_fresh s p]})).
      rewrite Heqp1 in IHp0. simpl in IHp0.
      apply cache_continuous_add_not_bound.
      { intros Hcontra. inversion Hcontra. }
      unfold cache_continuous_prop.
      destruct IHp0 as [Hge Hgs].
      destruct Hsub as [HCe HCs].
      split.
      + destruct HCe as [k Hk].
        exists k.
        intros k'.
        split; intros H.
        * rewrite Hk in H.
          destruct H as [s1 Hs1].
          exists s1.
          apply lookup_union_Some.
          { apply remove_disjoint_keep_s.  }
          left.
          unfold remove_bound_svars.
          rewrite map_filter_lookup_Some.
          split.
          {
            epose proof (Hext := to_NamedPattern2'_extends_cache _ _ _ _).
            erewrite Heqp1 in Hext. simpl in Hext.
            eapply lookup_weaken;[|eassumption].
            rewrite lookup_insert_ne.
            { discriminate. }
            unfold cache_incr_svar.
            rewrite lookup_kmap_Some.
            exists (patt_bound_evar k').
            split.
            * reflexivity.
            * exact Hs1.
          }
          { unfold is_bound_svar_entry. simpl. intros [witness Hwitness].
            inversion Hwitness.
          }
        * destruct H as [s1 Hs1].
          destruct (C !! patt_bound_evar k') eqn:Hck'.
          {
            rewrite Hk.
            exists n0. exact Hck'.
          }
          {
            destruct Hgs as [k2 Hk2].
            rewrite lookup_union_Some in Hs1.
            2: {
              apply remove_disjoint_keep_s.
            }
            destruct Hs1 as [Hs1|Hs1].
            2: {
              unfold keep_bound_svars in Hs1.
              rewrite map_filter_lookup_Some in Hs1.
              destruct Hs1 as [Hs11 Hs12].
              rewrite Hck' in Hs11. inversion Hs11.
            }
            unfold remove_bound_svars in Hs1.
            rewrite map_filter_lookup_Some in Hs1.
            destruct Hs1 as [Hgk' _].
            pose proof (Hoas := onlyAddsSubpatterns (<[BoundVarSugar.B0:=npatt_svar (svs_fresh s p)]>
            (cache_incr_svar C)) p evs (s ∪ {[svs_fresh s p]})).
            feed specialize Hoas.
            {
              split.
              + unfold dangling_evars_cached.
                intros b Hb.
                rewrite lookup_insert_ne.
                { discriminate. }
                specialize (Hcachede b Hb).
                destruct Hcachede as [nphi Hnphi].
                exists nphi.
                unfold cache_incr_svar.
                replace (patt_bound_evar b)
                  with (incr_one_svar (patt_bound_evar b))
                  by reflexivity.
                rewrite lookup_kmap.
                exact Hnphi.
              + unfold dangling_svars_cached.
                intros b Hb.
                destruct b.
                {
                  exists (npatt_svar (svs_fresh s p)).
                  apply lookup_insert.
                }
                specialize (Hcacheds b Hb).
                destruct Hcacheds as [nphi Hnphi].
                exists nphi.
                rewrite lookup_insert_ne.
                { discriminate. }
                unfold cache_incr_svar.
                replace (patt_bound_svar (S b))
                  with (incr_one_svar (patt_bound_svar b))
                  by reflexivity.
                rewrite lookup_kmap.
                exact Hnphi.
            }
            specialize (Hoas (patt_bound_evar k')).
            feed specialize Hoas.
            {
              rewrite lookup_insert_None.
              split;[|discriminate].
              unfold cache_incr_svar.
              rewrite lookup_kmap_None.
              intros p'' Hp''.
              replace (patt_bound_evar k')
                with (incr_one_svar (patt_bound_evar k'))
                in Hp'' by reflexivity.
              apply (inj incr_one_svar) in Hp''.
              subst p''.
              exact Hck'.
            }
            {
              rewrite Heqp1. simpl.
              exists s1. exact Hgk'.
            }
            destruct Hoas as [_ [Hcontra _]].
            exfalso. apply Hcontra. exists k'. reflexivity.
          }
      + destruct HCs as [k Hk].
        exists k. intros k'.
        split; intros H.
        * rewrite Hk in H.
          destruct H as [e He].
          exists e.
          rewrite lookup_union_Some.
          --
            right.
            unfold keep_bound_svars.
            rewrite map_filter_lookup_Some.
            split.
            ++
              exact He.
            ++ unfold is_bound_svar_entry. simpl. exists k'. reflexivity.
          -- apply remove_disjoint_keep_s.
        * apply Hk.
          destruct H as [e He].
          exists e.
          rewrite lookup_union_Some in He.
          2: { apply remove_disjoint_keep_s. }
          destruct He as [He|He].
          --
            unfold remove_bound_svars in He.
            rewrite map_filter_lookup_Some in He.
            destruct He as [He1 He2].
            unfold is_bound_svar_entry in He2. simpl in He2.
            exfalso. apply He2. exists k'. reflexivity.
          --
            unfold keep_bound_svars in He.
            rewrite map_filter_lookup_Some in He.
            destruct He as [He1 He2].
            exact He1.
  Qed.

  Ltac case_match_in_hyp H :=
  lazymatch type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.

  Lemma dangling_vars_cached_shift_e C e p:
    dangling_vars_cached C (patt_exists p) ->
    dangling_vars_cached
      (<[BoundVarSugar.b0:=npatt_evar e]> (cache_incr_evar C))
      p
  .
  Proof.
    intros Hdangling.
    unfold dangling_vars_cached. unfold dangling_evars_cached.
    unfold dangling_svars_cached.
    destruct Hdangling as [Hdanglinge Hdanglings].
    split.
    --
      unfold dangling_evars_cached in Hdanglinge.
      intros b Hb.
      destruct b.
      {
        exists (npatt_evar e).
        apply lookup_insert.
      }
      specialize (Hdanglinge b Hb).
      destruct Hdanglinge as [nphi Hnphi].
      exists nphi.
      rewrite lookup_insert_ne.
      { discriminate. }
      unfold cache_incr_evar.
      replace (patt_bound_evar (S b))
        with (incr_one_evar (patt_bound_evar b))
        by reflexivity.
      rewrite lookup_kmap.
      exact Hnphi.
    --
      unfold dangling_svars_cached in Hdanglings.
      intros b Hb.
      specialize (Hdanglings b Hb).
      destruct Hdanglings as [nphi Hnphi].
      exists nphi.
      rewrite lookup_insert_ne.
      { discriminate. }
      replace (patt_bound_svar b)
        with (incr_one_evar (patt_bound_svar b))
        by reflexivity.
      unfold cache_incr_evar.
      rewrite lookup_kmap.
      exact Hnphi.
  Qed.

  Lemma dangling_vars_cached_shift_s C s p:
    dangling_vars_cached C (patt_mu p) ->
    dangling_vars_cached
      (<[BoundVarSugar.B0:=npatt_svar s]> (cache_incr_svar C))
      p
  .
  Proof.
    intros Hdangling.
    unfold dangling_vars_cached. unfold dangling_evars_cached.
    unfold dangling_svars_cached.
    destruct Hdangling as [Hdanglinge Hdanglings].
    split.
    --
      unfold dangling_evars_cached in Hdanglinge.
      intros b Hb.
      specialize (Hdanglinge b Hb).
      destruct Hdanglinge as [nphi Hnphi].
      exists nphi.
      rewrite lookup_insert_ne.
      { discriminate. }
      replace (patt_bound_evar b)
        with (incr_one_svar (patt_bound_evar b))
        by reflexivity.
      unfold cache_incr_svar.
      rewrite lookup_kmap.
      exact Hnphi.
    --
      unfold dangling_svars_cached in Hdanglings.
      intros b Hb.
      destruct b.
      {
        exists (npatt_svar s).
        apply lookup_insert.
      }
      specialize (Hdanglings b Hb).
      destruct Hdanglings as [nphi Hnphi].
      exists nphi.
      rewrite lookup_insert_ne.
      { discriminate. }
      unfold cache_incr_svar.
      replace (patt_bound_svar (S b))
        with (incr_one_svar (patt_bound_svar b))
        by reflexivity.
      rewrite lookup_kmap.
      exact Hnphi.
  Qed.

  Lemma bound_evar_cont_cache_shift C p e:
    cache_continuous_prop C ->
    is_bound_evar p ->
    (exists (np : NamedPattern), C !! p = Some np) ->
    exists (np : NamedPattern),
      (<[BoundVarSugar.b0:=npatt_evar e]>
       (cache_incr_evar C)
      ) !! p = Some np.
  Proof.
    intros Hcont Hbe [np Hnp].
    unfold cache_continuous_prop in Hcont.
    destruct Hcont as [Hconte _].
    destruct Hconte as [k Hk].
    unfold is_bound_evar in Hbe.
    destruct Hbe as [b Hb]. subst p.
    destruct b.
    {
      exists (npatt_evar e). apply lookup_insert.
    }
    rewrite lookup_insert_ne.
    { discriminate. }
    unfold cache_incr_evar.
    replace (patt_bound_evar (S b)) with (incr_one_evar (patt_bound_evar b)) by reflexivity.
    rewrite lookup_kmap.
    pose proof (Hb := Hk (S b)).
    destruct Hb as [Hb1 Hb2].
    feed specialize Hb2.
    {
      exists np. exact Hnp.
    }
    rewrite -Hk.
    lia.
  Qed.

  Lemma bound_svar_cont_cache_shift C p s:
    cache_continuous_prop C ->
    is_bound_svar p ->
    (exists (np : NamedPattern), C !! p = Some np) ->
    exists (np : NamedPattern),
      (<[BoundVarSugar.B0:=npatt_svar s]>
      (cache_incr_svar C)
      ) !! p = Some np.
  Proof.
    intros Hcont Hbs [np Hnp].
    unfold cache_continuous_prop in Hcont.
    destruct Hcont as [_ Hconts].
    destruct Hconts as [k Hk].
    unfold is_bound_svar in Hbs.
    destruct Hbs as [b Hb]. subst p.
    destruct b.
    {
      exists (npatt_svar s). apply lookup_insert.
    }
    rewrite lookup_insert_ne.
    { discriminate. }
    unfold cache_incr_svar.
    replace (patt_bound_svar (S b)) with (incr_one_svar (patt_bound_svar b)) by reflexivity.
    rewrite lookup_kmap.
    pose proof (Hb := Hk (S b)).
    destruct Hb as [Hb1 Hb2].
    feed specialize Hb2.
    {
      exists np. exact Hnp.
    }
    rewrite -Hk.
    lia.
  Qed.

(*
  Lemma app_exist_p_q_neq_p p q:
    ~ patt_app (patt_exists p) q = p.
  Proof. Admitted.

  Lemma is_not_subformula_1 p q:
    ~is_subformula_of_ind (patt_app (patt_exists p) q) p.
  Proof. Admitted.

  Lemma is_not_subformula_2 p q:
    ~is_subformula_of_ind (patt_app q (patt_exists p)) p.
  Proof. Admitted.
*)
  Lemma bound_evar_is_bound_var p:
    is_bound_evar p ->
    is_bound_var p.
  Proof.
    intros [b H]. subst p. simpl. exact I.
  Qed.

  Lemma bound_svar_is_bound_var p:
    is_bound_svar p ->
    is_bound_var p.
  Proof.
    intros [b H]. subst p. simpl. exact I.
  Qed.

  Lemma sub_prop_shift_e C e:
    sub_prop C ->
    sub_prop (<[BoundVarSugar.b0:=npatt_evar e]> (cache_incr_evar C)).
  Proof.
    remember (<[BoundVarSugar.b0:=npatt_evar e]> (cache_incr_evar C)) as C'.
    unfold sub_prop.
    intros Hsub p1 np1 Hnp1.
    rewrite HeqC' in Hnp1.

    Local Ltac destruct_lookup_in_C' Hnp :=
      match type of Hnp with
      | ((_ !! ?P) = _) =>
      (rewrite lookup_insert_ne in Hnp;[discriminate|]);
      unfold cache_incr_evar in Hnp;
      rewrite lookup_kmap_Some in Hnp;
      destruct Hnp as [pincr [Hpincr1 Hpincr2]];
      assert (Hpincreq: pincr = P);
      [(destruct pincr; simpl in Hpincr1; inversion Hpincr1; reflexivity)|];
      subst pincr; clear Hpincr1; rename Hpincr2 into Hnp
      end.

      Local Ltac propagate_cached_into_C' HeqC' Hcp1_1 Hnbound :=
        match goal with
        | [ |- bound_or_cached _ ?p1_1] =>
          destruct Hcp1_1 as [np1_1 Hnp1_1];
          right;
          exists np1_1;
          rewrite HeqC';
          rewrite lookup_insert_ne;
          [(
            intros HContra; subst p1_1;
            apply Hnbound; exists 0; reflexivity
          )|];
          unfold cache_incr_evar;
          replace (p1_1) with (incr_one_evar p1_1);
          [|(destruct p1_1; try reflexivity;
            exfalso; apply Hnbound; eexists; reflexivity)
          ];
          rewrite lookup_kmap;
          exact Hnp1_1
        end.

        Local Ltac propagate_bound p1_1 Hnbound :=
          destruct (decide (is_bound_evar p1_1)) as [Hbound|Hnbound];
          [(
            left;
            unfold is_bound_evar in Hbound;
            destruct Hbound as [b Hbound];
            subst p1_1;
            reflexivity
          )|].

          Local Ltac make_subpattern_boc Hsub Hnp1 subpattern Hsubcached :=
            match type of Hnp1 with
            | (?C !! ?big_pattern = Some ?np1) =>
              pose proof (Hsub1 := Hsub big_pattern np1 Hnp1);
              simpl in Hsub1;
              assert (Hsubboc: bound_or_cached C subpattern) by (destruct_and?; assumption);
              destruct Hsubboc as [Hsubbound|Hsubcached];
              [(left; exact Hsubbound)|]
            end.

    Local Ltac subpattern_boc HeqC' Hsub Hnp1 p1_1 :=
      let Hnbound := fresh "Hnbound" in
      propagate_bound p1_1 Hnbound;
      destruct_lookup_in_C' Hnp1;
      let Hsubcached := fresh "Hsubcached" in
      make_subpattern_boc Hsub Hnp1 p1_1 Hsubcached;
      propagate_cached_into_C' HeqC' Hsubcached Hnbound.

    
    destruct p1; try exact I.
    {            
      split.
      { subpattern_boc HeqC' Hsub Hnp1 p1_1. }
      { subpattern_boc HeqC' Hsub Hnp1 p1_2. }
    }
    {
      split.
      { subpattern_boc HeqC' Hsub Hnp1 p1_1. }
      { subpattern_boc HeqC' Hsub Hnp1 p1_2. }
    }
    { subpattern_boc HeqC' Hsub Hnp1 p1. }
    { subpattern_boc HeqC' Hsub Hnp1 p1. }
  Qed.

  Lemma sub_prop_shift_s C s:
    sub_prop C ->
    sub_prop (<[BoundVarSugar.B0:=npatt_svar s]> (cache_incr_svar C)).
  Proof.
    intros Hsub.
    remember (<[BoundVarSugar.B0:=npatt_svar s]> (cache_incr_svar C)) as C'.
    intros p1 np1 Hnp1.
          rewrite HeqC' in Hnp1.

          Local Ltac mu_destruct_lookup_in_C' Hnp :=
            match type of Hnp with
            | ((_ !! ?P) = _) =>
            (rewrite lookup_insert_ne in Hnp;[discriminate|]);
            unfold cache_incr_svar in Hnp;
            rewrite lookup_kmap_Some in Hnp;
            destruct Hnp as [pincr [Hpincr1 Hpincr2]];
            assert (Hpincreq: pincr = P);
            [(destruct pincr; simpl in Hpincr1; inversion Hpincr1; reflexivity)|];
            subst pincr; clear Hpincr1; rename Hpincr2 into Hnp
            end.

            Local Ltac mu_propagate_cached_into_C' HeqC' Hcp1_1 Hnbound :=
              match goal with
              | [ |- bound_or_cached _ ?p1_1] =>
                destruct Hcp1_1 as [np1_1 Hnp1_1];
                right;
                exists np1_1;
                rewrite HeqC';
                rewrite lookup_insert_ne;
                [(
                  intros HContra; subst p1_1;
                  apply Hnbound; exists 0; reflexivity
                )|];
                unfold cache_incr_svar;
                replace (p1_1) with (incr_one_svar p1_1);
                [|(destruct p1_1; try reflexivity;
                  exfalso; apply Hnbound; eexists; reflexivity)
                ];
                rewrite lookup_kmap;
                exact Hnp1_1
              end.

              Local Ltac mu_propagate_bound p1_1 Hnbound :=
                destruct (decide (is_bound_svar p1_1)) as [Hbound|Hnbound];
                [(
                  left;
                  unfold is_bound_svar in Hbound;
                  destruct Hbound as [b Hbound];
                  subst p1_1;
                  reflexivity
                )|].

                Local Ltac mu_make_subpattern_boc Hsub Hnp1 subpattern Hsubcached :=
                  match type of Hnp1 with
                  | (?C !! ?big_pattern = Some ?np1) =>
                    pose proof (Hsub1 := Hsub big_pattern np1 Hnp1);
                    simpl in Hsub1;
                    assert (Hsubboc: bound_or_cached C subpattern) by (destruct_and?; assumption);
                    destruct Hsubboc as [Hsubbound|Hsubcached];
                    [(left; exact Hsubbound)|]
                  end.

          Local Ltac mu_subpattern_boc HeqC' Hsub Hnp1 p1_1 :=
            let Hnbound := fresh "Hnbound" in
            mu_propagate_bound p1_1 Hnbound;
            mu_destruct_lookup_in_C' Hnp1;
            let Hsubcached := fresh "Hsubcached" in
            mu_make_subpattern_boc Hsub Hnp1 p1_1 Hsubcached;
            mu_propagate_cached_into_C' HeqC' Hsubcached Hnbound.

          destruct p1; try exact I.
          {            
            split.
            { mu_subpattern_boc HeqC' Hsub Hnp1 p1_1. }
            { mu_subpattern_boc HeqC' Hsub Hnp1 p1_2. }
          }
          {
            split.
            { mu_subpattern_boc HeqC' Hsub Hnp1 p1_1. }
            { mu_subpattern_boc HeqC' Hsub Hnp1 p1_2. }
          }
          { mu_subpattern_boc HeqC' Hsub Hnp1 p1. }
          { mu_subpattern_boc HeqC' Hsub Hnp1 p1. }
  Qed.

  Lemma sub_prop_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet):
    dangling_vars_cached C p ->
    cache_continuous_prop C ->
    sub_prop C ->
    sub_prop (to_NamedPattern2' p C evs svs).1.1.2.
  Proof.
    intros Hdangling Hcont Hsub.
    move: C Hdangling Hcont Hsub evs svs.
    induction p; intros C Hdangling Hcont Hsub evs svs;
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
        destruct H4 as [H4 H5];
        split;[rename H4 into HBoC; rename p0_1 into pcached|rename H5 into HBoC;rename p0_2 into pcached];
           (destruct HBoC as [HBound|HCached];[
               (left; exact HBound)|
               (right; destruct HCached as [npcached HCached];
                destruct (decide (P = pcached));
                [(subst; exists NP; apply lookup_insert)
                |(exists npcached; rewrite -HCached; apply lookup_insert_ne; assumption)]
          )]));
      try (rewrite lookup_insert_Some in H;
      destruct H as [[H1 H2] | [H3 H4]]; subst; auto; try inversion H1;
           apply Hsub in H4; rename H4 into HBoC; rename p0 into pcached;
           (destruct HBoC as [HBound|HCached];[
               (left; exact HBound)|
               (right; destruct HCached as [npcached HCached];
                destruct (decide (P = pcached));
                [(subst; exists NP; apply lookup_insert)
                |(exists npcached; rewrite -HCached; apply lookup_insert_ne; assumption)]
          )]))
          end.

            Local Ltac reuse_Hboc Hboc lhs rhs pcached :=
          destruct Hboc as [Hbound|Hcached];
          [(left; exact Hbound)
          |(right;
            destruct (decide (lhs = pcached));
            [(exists rhs; subst; apply lookup_insert)
            |(destruct Hcached as [npcached Hnpcached];
              exists npcached; rewrite lookup_insert_ne; assumption;
              exact Hnpcached)])
          ].

        Local Ltac if_equal_then_cached H Heqp0 Heqp1 :=
          lazymatch type of H with
          | _ = (_ ?p0_1 ?p0_2) =>
              inversion H; subst; clear H;
              lazymatch type of Heqp0 with
              | (to_NamedPattern2' ?p1 ?C ?evs ?svs = (?n0, _, _, _)) =>
                  lazymatch type of Heqp1 with
                  | (to_NamedPattern2' ?p2 ?g0 ?e0 ?s0 = (?n1, ?g, _, _)) =>
                      pose proof (Htmp := to_NamedPattern2'_ensures_present p0_1 C evs svs);
                      rewrite Heqp0 in Htmp; simpl in Htmp;
                      pose proof (Hec := to_NamedPattern2'_extends_cache g0 p0_2 e0 s0);
                      rewrite Heqp1 in Hec; simpl in Hec;
                      pose proof (Htmp2 := to_NamedPattern2'_ensures_present p0_2 g0 e0 s0);
                      rewrite Heqp1 in Htmp2; simpl in Htmp2;
                      eapply lookup_weaken with (m2 := g) in Htmp;[|assumption];
                      split; right;
                      [(exists n0; rewrite -Htmp; apply lookup_insert_ne)
                      |(exists n1; rewrite -Htmp2; apply lookup_insert_ne)
                      ]; auto using app_neq1,app_neq2,imp_neq1,imp_neq2
                  end
              end        
          end.

        Local Ltac if_not_equal_boc_1 H' Hsub'' pai npai :=
          lazymatch type of H' with
          | _ !! (?connective ?p0) = Some ?np =>
              unfold sub_prop in Hsub'';
              pose proof (Htmp := Hsub'' (connective p0) np H');
              simpl in Htmp;
              reuse_Hboc Htmp pai npai p0
          end.

        Local Ltac if_not_equal_boc_2 H' Hsub'' pai npai :=
          lazymatch type of H' with
          | _ !! (?connective ?p0_1 ?p0_2) = Some ?np =>
              unfold sub_prop in Hsub'';
              pose proof (Htmp := Hsub'' (connective p0_1 p0_2) np H');
              simpl in Htmp;
              destruct Htmp as [Hboc1 Hboc2];
              split;
              [reuse_Hboc Hboc1 pai npai p0_1
              |reuse_Hboc Hboc2 pai npai p0_2
              ]
          end.

      * repeat case_match_in_hyp H.
        repeat case_match_in_hyp Heqp.
        subst. simpl in *. invert_tuples.
        rewrite lookup_insert_Some in H.

        assert (HdanglingCp1: dangling_vars_cached C p1).
        { eapply dangling_vars_cached_app_proj1. apply Hdangling. }
        pose proof (Hext1 := to_NamedPattern2'_extends_cache C p1 evs svs).
        rewrite Heqp0 in Hext1. simpl in Hext1.
        pose proof (Hcont' := cache_continuous_step C p1 evs svs HdanglingCp1 Hcont).
        rewrite Heqp0 in Hcont'.
        simpl in Hcont'.

        assert (Hdanglingg0p2: dangling_vars_cached g0 p2).
        {
          eapply dangling_vars_subcache.
          2:{ apply Hext1. }
          eapply dangling_vars_cached_app_proj2.
          apply Hdangling.
        }
        pose proof (Hcont'' := cache_continuous_step g0 p2 e0 s0 Hdanglingg0p2 Hcont').
        rewrite Heqp1 in Hcont''.
        simpl in Hcont''.
        pose proof (Hsub' := IHp1 C HdanglingCp1 Hcont Hsub evs svs).
        rewrite Heqp0 in Hsub'; simpl in Hsub'.
        pose proof (Hsub'' := IHp2 g0 Hdanglingg0p2 Hcont' Hsub' e0 s0).
        rewrite Heqp1 in Hsub''; simpl in Hsub''.

        destruct p0; auto; destruct H as [[H _]|[_ H']].
        -- if_equal_then_cached H Heqp0 Heqp1.
        -- if_not_equal_boc_2 H' Hsub'' (patt_app p1 p2) (npatt_app n0 n1).
        -- if_equal_then_cached H Heqp0 Heqp1.
        -- if_not_equal_boc_2 H' Hsub'' (patt_app p1 p2) (npatt_app n0 n1).
        -- if_equal_then_cached H Heqp0 Heqp1.
        -- if_not_equal_boc_1 H' Hsub'' (patt_app p1 p2) (npatt_app n0 n1).
        -- if_equal_then_cached H Heqp0 Heqp1.
        -- if_not_equal_boc_1 H' Hsub'' (patt_app p1 p2) (npatt_app n0 n1).

      * repeat case_match_in_hyp H.
        repeat case_match_in_hyp Heqp.
        subst. simpl in *. invert_tuples.
        rewrite lookup_insert_Some in H.

        assert (HdanglingCp1: dangling_vars_cached C p1).
        { eapply dangling_vars_cached_app_proj1. apply Hdangling. }
        pose proof (Hext1 := to_NamedPattern2'_extends_cache C p1 evs svs).
        rewrite Heqp0 in Hext1. simpl in Hext1.
        pose proof (Hcont' := cache_continuous_step C p1 evs svs HdanglingCp1 Hcont).
        rewrite Heqp0 in Hcont'.
        simpl in Hcont'.

        assert (Hdanglingg0p2: dangling_vars_cached g0 p2).
        {
          eapply dangling_vars_subcache.
          2:{ apply Hext1. }
          eapply dangling_vars_cached_app_proj2.
          apply Hdangling.
        }
        pose proof (Hcont'' := cache_continuous_step g0 p2 e0 s0 Hdanglingg0p2 Hcont').
        rewrite Heqp1 in Hcont''.
        simpl in Hcont''.
        pose proof (Hsub' := IHp1 C HdanglingCp1 Hcont Hsub evs svs).
        rewrite Heqp0 in Hsub'; simpl in Hsub'.
        pose proof (Hsub'' := IHp2 g0 Hdanglingg0p2 Hcont' Hsub' e0 s0).
        rewrite Heqp1 in Hsub''; simpl in Hsub''.

        destruct p0; auto; destruct H as [[H _]|[_ H']].
        -- if_equal_then_cached H Heqp0 Heqp1.
        -- if_not_equal_boc_2 H' Hsub'' (patt_imp p1 p2) (npatt_imp n0 n1).
        -- if_equal_then_cached H Heqp0 Heqp1.
        -- if_not_equal_boc_2 H' Hsub'' (patt_imp p1 p2) (npatt_imp n0 n1).
        -- if_equal_then_cached H Heqp0 Heqp1.
        -- if_not_equal_boc_1 H' Hsub'' (patt_imp p1 p2) (npatt_imp n0 n1).
        -- if_equal_then_cached H Heqp0 Heqp1.
        -- if_not_equal_boc_1 H' Hsub'' (patt_imp p1 p2) (npatt_imp n0 n1).

      * repeat case_match_in_hyp H.
        repeat case_match_in_hyp Heqp.
        subst. simpl in *. invert_tuples.
        rewrite lookup_insert_Some in H.

        remember (evs ∪ {[evs_fresh evs p0]}) as evs'.
        remember (<[BoundVarSugar.b0:=npatt_evar (evs_fresh evs p0)]> (cache_incr_evar C)) as C'.

        assert (HdanglingC'p0: dangling_vars_cached C' p0).
        { 
          rewrite HeqC'. apply dangling_vars_cached_shift_e. apply Hdangling.
        }       
        
        assert (HcontC': cache_continuous_prop C').
        {
          rewrite HeqC'. apply cache_continuous_shift_e. exact Hcont.
        }

        (* need to show sub_prop C' holds *)
        assert(HsubC' : sub_prop C').
        { subst C'. apply sub_prop_shift_e. apply Hsub. }
        epose proof (IH1 := IHp C' HdanglingC'p0 HcontC' HsubC' _ _).
        erewrite Heqp0 in IH1. simpl in IH1.

        Ltac ex_propagate_bound subpattern Hnbound :=
          destruct (decide (is_bound_evar subpattern)) as [Hbound|Hnbound];
          [
            left; apply bound_evar_is_bound_var; exact Hbound
          |].
        Ltac ex_propagate_same subpattern largepattern nlargepattern :=
          destruct (decide (subpattern = largepattern)) as [Hsame|Hnsame];
          [
            (right;
            exists nlargepattern;
            subst;
            apply lookup_insert)
          |].            
        
        Ltac ex_extract_Hg0large H Hg0large :=
          destruct H as [H|H];
          [
            (destruct H as [Hcontra _]; inversion Hcontra)
          |];
          destruct H as [_ H];
          rewrite lookup_union_Some in H;
          [|apply remove_disjoint_keep_e];
          unfold keep_bound_evars in H;
          rewrite map_filter_lookup_Some in H;
          destruct H as [H|H];
          [|(
            rewrite map_filter_lookup_Some in H;
            destruct H as [_ Hcontra];
            destruct Hcontra as [dbi Hcontradbi];
            inversion Hcontradbi
          )];
          destruct H as [Hg0large _].


        Ltac ex_extract_cached_subpattern H IH1 Hg0large subpattern :=
          lazymatch type of Hg0large with
          | (?g0 !! ?large_pattern = Some ?np) =>
            pose proof (IH1 large_pattern np Hg0large);
            simpl in H;
            assert(Hbocsubpattern: bound_or_cached g0 subpattern);
            [(destruct_and?; assumption)|];
            destruct Hbocsubpattern as [Hboundsubpattern|Hcachedsubpattern];
            [(left; exact Hboundsubpattern)|];
            destruct Hcachedsubpattern as [nsubpattern Hnsubpattern]
          end.

        Ltac ex_finish_cached Hnsame Hnsubpattern Hnbound :=
          lazymatch type of Hnsubpattern with
          | ((?g0 !! ?subpattern) = Some ?nsubpattern) =>
            right;
            exists nsubpattern;
            rewrite lookup_insert_ne;
            [(apply not_eq_sym; apply Hnsame)|];
            rewrite lookup_union_Some;
            [|apply remove_disjoint_keep_e];
            left;
            unfold remove_bound_evars;
            rewrite map_filter_lookup_Some;
            split;
            [exact Hnsubpattern|];
            unfold is_bound_evar_entry;
            simpl;
            exact Hnbound
          end.


        destruct p00; try exact I.
        {
          split.
          {
            ex_propagate_bound p00_1 Hnbound.
            ex_propagate_same p00_1 (patt_exists p0) (npatt_exists (evs_fresh evs p0) n0).  
            ex_extract_Hg0large H Hg0large.
            ex_extract_cached_subpattern H IH1 Hg0large p00_1.
            ex_finish_cached Hnsame Hnsubpattern Hnbound.
          }
          {
            ex_propagate_bound p00_2 Hnbound.
            ex_propagate_same p00_2 (patt_exists p0) (npatt_exists (evs_fresh evs p0) n0).
            ex_extract_Hg0large H Hg0large.
            ex_extract_cached_subpattern H IH1 Hg0large p00_2.
            ex_finish_cached Hnsame Hnsubpattern Hnbound.
          }
        }
        {
          split.
          {
            ex_propagate_bound p00_1 Hnbound.
            ex_propagate_same p00_1 (patt_exists p0) (npatt_exists (evs_fresh evs p0) n0).  
            ex_extract_Hg0large H Hg0large.
            ex_extract_cached_subpattern H IH1 Hg0large p00_1.
            ex_finish_cached Hnsame Hnsubpattern Hnbound.
          }
          {
            ex_propagate_bound p00_2 Hnbound.
            ex_propagate_same p00_2 (patt_exists p0) (npatt_exists (evs_fresh evs p0) n0).
            ex_extract_Hg0large H Hg0large.
            ex_extract_cached_subpattern H IH1 Hg0large p00_2.
            ex_finish_cached Hnsame Hnsubpattern Hnbound.
          }
        }
        {
          ex_propagate_bound p00 Hnbound.
          ex_propagate_same p00 (patt_exists p0) (npatt_exists (evs_fresh evs p0) n0).

          destruct H as [H|H].
          {
            destruct H as [H1 H2].
            inversion H1. subst. clear H1.
            epose proof (Hp00present := to_NamedPattern2'_ensures_present _ _ _ _).
            erewrite Heqp0 in Hp00present. simpl in Hp00present.
            right.
            exists n0.
            rewrite lookup_insert_ne.
            { apply not_eq_sym. exact Hnsame. }
            rewrite lookup_union_Some.
            2: { apply remove_disjoint_keep_e. }
            left.
            unfold remove_bound_evars.
            rewrite map_filter_lookup_Some.
            split.
            {
              exact Hp00present.
            }
            {
              unfold is_bound_evar_entry. simpl. exact Hnbound.
            }
          }

          destruct H as [_ H];
          rewrite lookup_union_Some in H;
          [|apply remove_disjoint_keep_e];
          unfold keep_bound_evars in H;
          rewrite map_filter_lookup_Some in H;
          destruct H as [H|H];
          [|(
            rewrite map_filter_lookup_Some in H;
            destruct H as [_ Hcontra];
            destruct Hcontra as [dbi Hcontradbi];
            inversion Hcontradbi
          )];
          destruct H as [Hg0large _].

          ex_extract_cached_subpattern H IH1 Hg0large p00.
          ex_finish_cached Hnsame Hnsubpattern Hnbound.
        }
        {
          ex_propagate_bound p00 Hnbound.
          ex_propagate_same p00 (patt_exists p0) (npatt_exists (evs_fresh evs p0) n0).
          ex_extract_Hg0large H Hg0large.
          ex_extract_cached_subpattern H IH1 Hg0large p00.
          ex_finish_cached Hnsame Hnsubpattern Hnbound.
        }
      * repeat case_match_in_hyp H.
        repeat case_match_in_hyp Heqp.
        subst. simpl in *. invert_tuples.
        rewrite lookup_insert_Some in H.

        remember (s ∪ {[svs_fresh s p0]}) as svs'.
        remember (<[BoundVarSugar.B0:=npatt_svar (svs_fresh s p0)]> (cache_incr_svar C)) as C'.

        assert (HdanglingC'p0: dangling_vars_cached C' p0).
        { 
          rewrite HeqC'. apply dangling_vars_cached_shift_s. apply Hdangling.
        }       
        
        assert (HcontC': cache_continuous_prop C').
        {
          rewrite HeqC'. apply cache_continuous_shift_s. exact Hcont.
        }

        (* need to show sub_prop C' holds *)
        assert(HsubC' : sub_prop C').
        { subst C'. apply sub_prop_shift_s. apply Hsub. }

        epose proof (IH1 := IHp C' HdanglingC'p0 HcontC' HsubC' _ _).
        erewrite Heqp0 in IH1. simpl in IH1.

        Ltac mu2_propagate_bound subpattern Hnbound :=
          destruct (decide (is_bound_svar subpattern)) as [Hbound|Hnbound];
          [
            left; apply bound_svar_is_bound_var; exact Hbound
          |].
        Ltac mu2_propagate_same subpattern largepattern nlargepattern :=
          destruct (decide (subpattern = largepattern)) as [Hsame|Hnsame];
          [
            (right;
            exists nlargepattern;
            subst;
            apply lookup_insert)
          |].            
        
        Ltac mu2_extract_Hg0large H Hg0large :=
          destruct H as [H|H];
          [
            (destruct H as [Hcontra _]; inversion Hcontra)
          |];
          destruct H as [_ H];
          rewrite lookup_union_Some in H;
          [|apply remove_disjoint_keep_s];
          unfold keep_bound_svars in H;
          rewrite map_filter_lookup_Some in H;
          destruct H as [H|H];
          [|(
            rewrite map_filter_lookup_Some in H;
            destruct H as [_ Hcontra];
            destruct Hcontra as [dbi Hcontradbi];
            inversion Hcontradbi
          )];
          destruct H as [Hg0large _].


        Ltac mu2_extract_cached_subpattern H IH1 Hg0large subpattern :=
          lazymatch type of Hg0large with
          | (?g0 !! ?large_pattern = Some ?np) =>
            pose proof (IH1 large_pattern np Hg0large);
            simpl in H;
            assert(Hbocsubpattern: bound_or_cached g0 subpattern);
            [(destruct_and?; assumption)|];
            destruct Hbocsubpattern as [Hboundsubpattern|Hcachedsubpattern];
            [(left; exact Hboundsubpattern)|];
            destruct Hcachedsubpattern as [nsubpattern Hnsubpattern]
          end.

        Ltac mu2_finish_cached Hnsame Hnsubpattern Hnbound :=
          lazymatch type of Hnsubpattern with
          | ((?g0 !! ?subpattern) = Some ?nsubpattern) =>
            right;
            exists nsubpattern;
            rewrite lookup_insert_ne;
            [(apply not_eq_sym; apply Hnsame)|];
            rewrite lookup_union_Some;
            [|apply remove_disjoint_keep_s];
            left;
            unfold remove_bound_svars;
            rewrite map_filter_lookup_Some;
            split;
            [exact Hnsubpattern|];
            unfold is_bound_svar_entry;
            simpl;
            exact Hnbound
          end.


        destruct p00; try exact I.
        {
          split.
          {
            mu2_propagate_bound p00_1 Hnbound.
            mu2_propagate_same p00_1 (patt_mu p0) (npatt_mu (svs_fresh s p0) n0).  
            mu2_extract_Hg0large H Hg0large.
            mu2_extract_cached_subpattern H IH1 Hg0large p00_1.
            mu2_finish_cached Hnsame Hnsubpattern Hnbound.
          }
          {
            mu2_propagate_bound p00_2 Hnbound.
            mu2_propagate_same p00_2 (patt_mu p0) (npatt_mu (svs_fresh s p0) n0).  
            mu2_extract_Hg0large H Hg0large.
            mu2_extract_cached_subpattern H IH1 Hg0large p00_2.
            mu2_finish_cached Hnsame Hnsubpattern Hnbound.
          }
        }
        {
          split.
          {
            mu2_propagate_bound p00_1 Hnbound.
            mu2_propagate_same p00_1 (patt_mu p0) (npatt_mu (svs_fresh s p0) n0).  
            mu2_extract_Hg0large H Hg0large.
            mu2_extract_cached_subpattern H IH1 Hg0large p00_1.
            mu2_finish_cached Hnsame Hnsubpattern Hnbound.
          }
          {
            mu2_propagate_bound p00_2 Hnbound.
            mu2_propagate_same p00_2 (patt_mu p0) (npatt_mu (svs_fresh s p0) n0).  
            mu2_extract_Hg0large H Hg0large.
            mu2_extract_cached_subpattern H IH1 Hg0large p00_2.
            mu2_finish_cached Hnsame Hnsubpattern Hnbound.
          }
        }
        {
          mu2_propagate_bound p00 Hnbound.
          mu2_propagate_same p00 (patt_mu p0) (npatt_mu (svs_fresh s p0) n0).  
          mu2_extract_Hg0large H Hg0large.
          mu2_extract_cached_subpattern H IH1 Hg0large p00.
          mu2_finish_cached Hnsame Hnsubpattern Hnbound.
        }
        {
          mu2_propagate_bound p00 Hnbound.
          mu2_propagate_same p00 (patt_mu p0) (npatt_mu (svs_fresh s p0) n0).

          destruct H as [H|H].
          {
            destruct H as [H1 H2].
            inversion H1. subst. clear H1.
            epose proof (Hp00present := to_NamedPattern2'_ensures_present _ _ _ _).
            erewrite Heqp0 in Hp00present. simpl in Hp00present.
            right.
            exists n0.
            rewrite lookup_insert_ne.
            { apply not_eq_sym. exact Hnsame. }
            rewrite lookup_union_Some.
            2: { apply remove_disjoint_keep_s. }
            left.
            unfold remove_bound_svars.
            rewrite map_filter_lookup_Some.
            split.
            {
              exact Hp00present.
            }
            {
              unfold is_bound_svar_entry. simpl. exact Hnbound.
            }
          }

          destruct H as [_ H];
          rewrite lookup_union_Some in H;
          [|apply remove_disjoint_keep_s];
          unfold keep_bound_evars in H;
          rewrite map_filter_lookup_Some in H;
          destruct H as [H|H];
          [|(
            rewrite map_filter_lookup_Some in H;
            destruct H as [_ Hcontra];
            destruct Hcontra as [dbi Hcontradbi];
            inversion Hcontradbi
          )];
          destruct H as [Hg0large _].

          mu2_extract_cached_subpattern H IH1 Hg0large p00.
          mu2_finish_cached Hnsame Hnsubpattern Hnbound.
        }
  Qed.

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
    | [] => C = ∅
    | (x::xs) =>
        x.2.1.1.2 = C /\
          (match (last (x::xs)) with
           | None => False
           | Some (p_l, x_l) =>
            dangling_vars_cached ∅ p_l /\
            x_l = (to_NamedPattern2' p_l ∅ ∅ ∅)
           end) /\
          forall (i:nat),
            match xs!!i with
            | None => True
            (* p_i came from the result of the cache c_Si and everything before it *)
            | Some (p_Si, (np_Si, c_Si, evs_Si, svs_Si)) =>
                exists p_i,
                c_Si !! p_i = None /\
                dangling_vars_cached c_Si p_i /\
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

  Lemma history_generator_empty:
    History_generator empty.
  Proof.
    apply mkHistory with (Hst_history := []).
    simpl. reflexivity.
  Qed.

  Lemma history_generator_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet)
    (hC : History_generator C) :
    ((fmap evs_of (head (Hst_history C hC)) = Some evs /\
     fmap svs_of (head (Hst_history C hC)) = Some svs)
     \/ ( (Hst_history C hC = []) /\ C = ∅ /\ evs = ∅ /\ svs = ∅)) ->
    dangling_vars_cached C p ->
    History_generator (to_NamedPattern2' p C evs svs).1.1.2.
  Proof.
    intros Hevssvs HdcCp.
    destruct (C !! p) eqn:Hin.
    - exists (Hst_history C hC).
      unfold to_NamedPattern2'.
      destruct p; simpl; rewrite Hin; simpl;  destruct hC; simpl; assumption.
    - exists ((p, to_NamedPattern2' p C evs svs) :: (Hst_history C hC)).
      simpl.
      split;[reflexivity|].
      destruct hC. simpl in *.

      destruct Hevssvs as [[Hevs Hsvs]|Hevssvs].
      {
        unfold hist_prop in Hst_prop0.
        destruct Hst_history0.
        { subst C. simpl in *. inversion Hevs. }
        destruct Hst_prop0 as [Hcache [HhistoryC Hinner]].
        split.
        { subst C. destruct h as [p0 [[[np0 C0] evs0] svs0]].
          simpl in * |-. inversion Hevs. inversion Hsvs. clear Hevs Hsvs. subst.
          repeat unfold fst,snd,svs_of,evs_of.
          unfold evs_of, svs_of in *. simpl in *.
          rewrite last_cons. rewrite last_cons in HhistoryC.
          destruct (last Hst_history0) eqn:Heqtmp.
          { exact HhistoryC. }
          { exact HhistoryC. }
        }
        destruct i; simpl.
        unfold evs_of, svs_of in *. simpl in *.
        inversion Hevs; inversion Hsvs; subst.
        repeat case_match; simpl in *; subst.
        + exists p. split. exact Hin. split. exact HdcCp. reflexivity.
        + exists p. split. exact Hin. split. exact HdcCp. reflexivity.
        + apply Hinner.
      }
      {
        destruct Hevssvs as [H1 [H2 [H3 H4]]]. subst.
        split.
        {
          simpl. split. exact HdcCp. reflexivity.
        }
        {
          intros i. simpl. exact I.
        }
      }
  Defined.

  Lemma dangling_vars_cached_proj_insert C p q nq:
    ~is_bound_var q ->
    dangling_vars_cached (<[q := nq]> C) p ->
    dangling_vars_cached C p.
  Proof.
    intros Hnb Hc.
    destruct Hc as [Hce Hcs].
    unfold dangling_evars_cached in Hce.
    unfold dangling_svars_cached in Hcs.
    split.
    - unfold dangling_evars_cached.
      intros b Hdng.
      specialize (Hce b Hdng).
      destruct Hce as [nphi Hnphi].
      exists nphi.
      rewrite lookup_insert_ne in Hnphi.
      {
        destruct q; try discriminate.
        exfalso. apply Hnb.
        apply bound_evar_is_bound_var. exists n. reflexivity.
      }
      exact Hnphi.
    - unfold dangling_svars_cached.
      intros b Hdng.
      specialize (Hcs b Hdng).
      destruct Hcs as [nphi Hnphi].
      exists nphi.
      rewrite lookup_insert_ne in Hnphi.
      {
        destruct q; try discriminate.
        exfalso. apply Hnb.
        apply bound_svar_is_bound_var. exists n. reflexivity.
      }
      exact Hnphi.
  Qed.

  Lemma sub_prop_trans C p np q:
    is_subformula_of_ind q p ->
    ~ is_bound_var q ->
    sub_prop C ->
    C !! p = Some np ->
    exists nq, C !! q = Some nq.
  Proof.
    intros Hsubf.
    move: C np.
    induction Hsubf; intros C np Hnbound Hsubp HCp.
    {
      subst. exists np. exact HCp.
    }
    {
      pose proof (Hsubp' := Hsubp (patt_app ϕ₂ ϕ₃) np HCp). simpl in Hsubp'.
      destruct Hsubp' as [Hboc2 Hboc3].
      destruct Hboc2 as [Hbound2|Hcached2].
      {
        destruct ϕ₂; simpl in Hbound2; inversion Hbound2.
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
      }
      destruct Hcached2 as [nϕ2 Hnϕ2].

      eapply IHHsubf.
      { exact Hnbound. }
      { exact Hsubp. }
      { exact Hnϕ2. }
    }
    {
      pose proof (Hsubp' := Hsubp (patt_app ϕ₂ ϕ₃) np HCp). simpl in Hsubp'.
      destruct Hsubp' as [Hboc2 Hboc3].
      destruct Hboc3 as [Hbound3|Hcached3].
      {
        destruct ϕ₃; simpl in Hbound3; inversion Hbound3.
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
      }
      destruct Hcached3 as [nϕ3 Hnϕ3].

      eapply IHHsubf.
      { exact Hnbound. }
      { exact Hsubp. }
      { exact Hnϕ3. }
    }
    {
      pose proof (Hsubp' := Hsubp (patt_imp ϕ₂ ϕ₃) np HCp). simpl in Hsubp'.
      destruct Hsubp' as [Hboc2 Hboc3].
      destruct Hboc2 as [Hbound2|Hcached2].
      {
        destruct ϕ₂; simpl in Hbound2; inversion Hbound2.
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
      }
      destruct Hcached2 as [nϕ2 Hnϕ2].

      eapply IHHsubf.
      { exact Hnbound. }
      { exact Hsubp. }
      { exact Hnϕ2. }
    }
    {
      pose proof (Hsubp' := Hsubp (patt_imp ϕ₂ ϕ₃) np HCp). simpl in Hsubp'.
      destruct Hsubp' as [Hboc2 Hboc3].
      destruct Hboc3 as [Hbound3|Hcached3].
      {
        destruct ϕ₃; simpl in Hbound3; inversion Hbound3.
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
      }
      destruct Hcached3 as [nϕ3 Hnϕ3].

      eapply IHHsubf.
      { exact Hnbound. }
      { exact Hsubp. }
      { exact Hnϕ3. }
    }
    {
      pose proof (Hsubp' := Hsubp (patt_exists ϕ₂) np HCp). simpl in Hsubp'.
      destruct Hsubp' as [Hbound|Hcached].
      {
        destruct ϕ₂; simpl in Hbound; inversion Hbound.
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
      }
      destruct Hcached as [nϕ Hnϕ].
      eapply IHHsubf.
      { exact Hnbound. }
      { exact Hsubp. }
      { exact Hnϕ. }
    }
    {
      pose proof (Hsubp' := Hsubp (patt_mu ϕ₂) np HCp). simpl in Hsubp'.
      destruct Hsubp' as [Hbound|Hcached].
      {
        destruct ϕ₂; simpl in Hbound; inversion Hbound.
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
        { inversion Hsubf. subst. clear Hsubf. exfalso. apply Hnbound. simpl. exact I. }
      }
      destruct Hcached as [nϕ Hnϕ].
      eapply IHHsubf.
      { exact Hnbound. }
      { exact Hsubp. }
      { exact Hnϕ. }
    }
  Qed.

  Lemma actually_adds_subpatterns p C evs svs q:
    dangling_vars_cached C p ->
    cache_continuous_prop C ->
    sub_prop C ->
    is_subformula_of_ind q p ->
    ~ is_bound_var q ->
    exists nq, (to_NamedPattern2' p C evs svs).1.1.2 !! q = Some nq.
  Proof.
    intros Hdgcached Hccont Hsubp Hsubf Hnbound.
    epose proof (to_NamedPattern2'_ensures_present p C evs svs).
    Check sub_prop_trans.
    pose proof (Htrans := sub_prop_trans (to_NamedPattern2' p C evs svs).1.1.2 p (to_NamedPattern2' p C evs svs).1.1.1 q Hsubf Hnbound).
    feed specialize Htrans.
    { apply sub_prop_step; assumption. }
    { exact H. }
    exact Htrans.
  Qed.

  #[global]
  Instance NamedPattern_eqdec : EqDecision NamedPattern.
  Proof.
    solve_decision.
  Defined.

  Lemma find_nested_call
    (p : Pattern)
    (Cin : Cache)
    (evsin : EVarSet)
    (svsin : SVarSet)
    (Cout : Cache)
    (q : Pattern)
    (nq : NamedPattern):
    ~ is_bound_var q ->
    dangling_vars_cached Cin p ->
    cache_continuous_prop Cin ->
    sub_prop Cin ->
    Cin !! q = None ->
    Cout !! q = Some nq ->
    (to_NamedPattern2' p Cin evsin svsin).1.1.2 = Cout ->
    exists Cfound evsfound svsfound,
      Cfound !! q = None /\
      (to_NamedPattern2' q Cfound evsfound svsfound).1.1.1 = nq.
  Proof.
    intros Hnbq Hdvc Hccp Hsp Hqin Hqout Hcall.
    (*
    pose proof (Hsub := onlyAddsSubpatterns2 Cin p evsin svsin q Hqin).
    feed specialize Hsub.
    {
      exists nq. rewrite Hcall. exact Hqout.
    }*)
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz) by lia.
    clear Heqsz.
    move: p Hsz q nq evsin svsin Cin Cout Hnbq Hdvc Hccp Hsp Hqin Hqout Hcall.
    induction sz.
    { intros p Hsz; destruct p; simpl in Hsz; lia. }
    intros p Hsz; destruct p; simpl in Hsz; intros q nq evsin svsin Cin Cout Hnbq Hdvc Hccp Hsp Hqin Hqout Hcall;
      simpl in Hcall.
    {
      case_match_in_hyp Hcall.
      {
        simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
      }
      simpl in Hcall.
      rewrite -Hcall in Hqout.
      rewrite lookup_insert_Some in Hqout.
      destruct Hqout as [H|H].
      {
        destruct H as [H1 H2]. subst.
        exists Cin, evsin, svsin.
        simpl.
        rewrite Hqin. simpl. split; reflexivity.
      }
      {
        destruct H as [H1 H2].
        rewrite H2 in Hqin. inversion Hqin.
      }
    }
    {
      case_match_in_hyp Hcall.
      {
        simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
      }
      simpl in Hcall.
      rewrite -Hcall in Hqout.
      rewrite lookup_insert_Some in Hqout.
      destruct Hqout as [H|H].
      {
        destruct H as [H1 H2]. subst.
        exists Cin, evsin, svsin.
        simpl.
        rewrite Hqin. simpl. split; reflexivity.
      }
      {
        destruct H as [H1 H2].
        rewrite H2 in Hqin. inversion Hqin.
      }
    }
    {
      case_match_in_hyp Hcall.
      {
        simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
      }
      simpl in Hcall.
      rewrite -Hcall in Hqout.
      rewrite lookup_insert_Some in Hqout.
      destruct Hqout as [H|H].
      {
        destruct H as [H1 H2]. subst.
        exists Cin, evsin, svsin.
        simpl.
        rewrite Hqin. simpl. split; reflexivity.
      }
      {
        destruct H as [H1 H2].
        rewrite H2 in Hqin. inversion Hqin.
      }
    }
    {
      case_match_in_hyp Hcall.
      {
        simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
      }
      simpl in Hcall.
      rewrite -Hcall in Hqout.
      rewrite lookup_insert_Some in Hqout.
      destruct Hqout as [H|H].
      {
        destruct H as [H1 H2]. subst.
        exists Cin, evsin, svsin.
        simpl.
        rewrite Hqin. simpl. split; reflexivity.
      }
      {
        destruct H as [H1 H2].
        rewrite H2 in Hqin. inversion Hqin.
      }
    }
    {
      case_match_in_hyp Hcall.
      {
        simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
      }
      simpl in Hcall.
      rewrite -Hcall in Hqout.
      rewrite lookup_insert_Some in Hqout.
      destruct Hqout as [H|H].
      {
        destruct H as [H1 H2]. subst.
        exists Cin, evsin, svsin.
        simpl.
        rewrite Hqin. simpl. split; reflexivity.
      }
      {
        destruct H as [H1 H2].
        rewrite H2 in Hqin. inversion Hqin.
      }
    }
    {
      case_match_in_hyp Hcall.
      {
        simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
      }
      repeat case_match. invert_tuples. simpl in *.
      rewrite lookup_insert_Some in Hqout.
      destruct Hqout as [Heq|Hneq].
      {
        destruct Heq as [Heq1 Heq2].
        subst.
        exists Cin, evsin, svsin.
        simpl. rewrite Hqin.
        repeat case_match. invert_tuples. simpl in *.
        rewrite Heqp2 in Heqp5. inversion Heqp5. subst. split; reflexivity.
      }
      {
        destruct Hneq as [Hneq1 Hnq].
        
        assert (Hdvcp1: dangling_vars_cached Cin p1).
          {
            eapply dangling_vars_cached_app_proj1. exact Hdvc.
          }

          assert (Hdvcp2: dangling_vars_cached Cin p2).
          {
            eapply dangling_vars_cached_app_proj2. exact Hdvc.
          }
          assert (Hdvg0p2 : dangling_vars_cached g0 p2).
          {
            eapply dangling_vars_subcache.
            { apply Hdvcp2. }
            { epose proof (Htmp := to_NamedPattern2'_extends_cache _ _ _ _).
              erewrite Heqp1 in Htmp. simpl in Htmp. exact Htmp.
            }
          }

          destruct (g0 !! q) eqn:Hg0q.
          {
            epose proof (Hext := to_NamedPattern2'_extends_cache _ _ _ _).
            erewrite Heqp2 in Hext. simpl in Hext.
            pose proof (Hg0q' := Hg0q).
            eapply lookup_weaken in Hg0q';[|exact Hext].
            rewrite Hnq in Hg0q'. inversion Hg0q'; subst; clear Hg0q'.
            
            eapply IHsz with (p := p1).
            { lia. }
            { exact Hnbq. }
            { exact Hdvcp1. }
            { exact Hccp. }
            { exact Hsp. }
            { exact Hqin. }
            { exact Hg0q. }
            { erewrite Heqp1. reflexivity. }
          }
          {
            eapply IHsz with (p := p2).
            { lia. }
            { exact Hnbq. }
            { exact Hdvg0p2. }
            { epose proof (Htmp := cache_continuous_step _ _ _ _).
              erewrite Heqp1 in Htmp. simpl in Htmp.
              apply Htmp.
              { exact Hdvcp1. }
              { exact Hccp. }
            }
            { epose proof (Htmp := sub_prop_step _ _ _ _).
              erewrite Heqp1 in Htmp. simpl in Htmp.
              apply Htmp.
              { exact Hdvcp1. }
              { exact Hccp. }
              { exact Hsp. }
            }
            { exact Hg0q. }
            { exact Hnq. }
            { erewrite Heqp2. simpl. reflexivity. }
          }
        }
      }
      {
        case_match_in_hyp Hcall.
        {
          simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
        }
        simpl in Hcall.
        rewrite -Hcall in Hqout.
        rewrite lookup_insert_Some in Hqout.
        destruct Hqout as [H|H].
        {
          destruct H as [H1 H2]. subst.
          exists Cin, evsin, svsin.
          simpl.
          rewrite Hqin. simpl. split; reflexivity.
        }
        {
          destruct H as [H1 H2].
          rewrite H2 in Hqin. inversion Hqin.
        }
      }
      {
        case_match_in_hyp Hcall.
        {
          simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
        }
        repeat case_match. invert_tuples. simpl in *.
        rewrite lookup_insert_Some in Hqout.
        destruct Hqout as [Heq|Hneq].
        {
          destruct Heq as [Heq1 Heq2].
          subst.
          exists Cin, evsin, svsin.
          simpl. rewrite Hqin.
          repeat case_match. invert_tuples. simpl in *.
          rewrite Heqp2 in Heqp5. inversion Heqp5. subst. split; reflexivity.
        }
        {
          destruct Hneq as [Hneq1 Hnq].
          
          assert (Hdvcp1: dangling_vars_cached Cin p1).
            {
              eapply dangling_vars_cached_app_proj1. exact Hdvc.
            }
  
            assert (Hdvcp2: dangling_vars_cached Cin p2).
            {
              eapply dangling_vars_cached_app_proj2. exact Hdvc.
            }
            assert (Hdvg0p2 : dangling_vars_cached g0 p2).
            {
              eapply dangling_vars_subcache.
              { apply Hdvcp2. }
              { epose proof (Htmp := to_NamedPattern2'_extends_cache _ _ _ _).
                erewrite Heqp1 in Htmp. simpl in Htmp. exact Htmp.
              }
            }
  
            destruct (g0 !! q) eqn:Hg0q.
            {
              epose proof (Hext := to_NamedPattern2'_extends_cache _ _ _ _).
              erewrite Heqp2 in Hext. simpl in Hext.
              pose proof (Hg0q' := Hg0q).
              eapply lookup_weaken in Hg0q';[|exact Hext].
              rewrite Hnq in Hg0q'. inversion Hg0q'; subst; clear Hg0q'.
              
              eapply IHsz with (p := p1).
              { lia. }
              { exact Hnbq. }
              { exact Hdvcp1. }
              { exact Hccp. }
              { exact Hsp. }
              { exact Hqin. }
              { exact Hg0q. }
              { erewrite Heqp1. reflexivity. }
            }
            {
              eapply IHsz with (p := p2).
              { lia. }
              { exact Hnbq. }
              { exact Hdvg0p2. }
              { epose proof (Htmp := cache_continuous_step _ _ _ _).
                erewrite Heqp1 in Htmp. simpl in Htmp.
                apply Htmp.
                { exact Hdvcp1. }
                { exact Hccp. }
              }
              { epose proof (Htmp := sub_prop_step _ _ _ _).
                erewrite Heqp1 in Htmp. simpl in Htmp.
                apply Htmp.
                { exact Hdvcp1. }
                { exact Hccp. }
                { exact Hsp. }
              }
              { exact Hg0q. }
              { exact Hnq. }
              { erewrite Heqp2. simpl. reflexivity. }
            }
          }
        }
        {
          case_match_in_hyp Hcall.
          {
            simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
          }
          repeat case_match. invert_tuples. simpl in *.
          rewrite lookup_insert_Some in Hqout.
          destruct Hqout as [Heq|Hneq].
          {
            destruct Heq as [Heq1 Heq2].
            subst.
            exists Cin, evsin, s.
            simpl. rewrite Hqin.
            repeat case_match. invert_tuples. simpl in *.
            split; reflexivity.
          }
          {
            destruct Hneq as [Hneq1 Hnq].
            rewrite lookup_union_Some in Hnq.
            2: { apply remove_disjoint_keep_e. }
            destruct Hnq as [Hnq|Hnq].
            2: {
              unfold keep_bound_evars in Hnq.
              rewrite map_filter_lookup_Some in Hnq.
              destruct Hnq as [_ Hcontra].
              unfold is_bound_evar_entry in Hcontra. simpl in Hcontra.
              exfalso. apply Hnbq. apply bound_evar_is_bound_var.
              exact Hcontra.
            }
            unfold remove_bound_evars in Hnq.
            rewrite map_filter_lookup_Some in Hnq.
            destruct Hnq as [Hg0q _].

            epose proof (IH := IHsz p ltac:(lia) q nq _ _ _ _ Hnbq).
            feed specialize IH.
            {
              apply dangling_vars_cached_shift_e with (e := (evs_fresh evsin p)) in Hdvc.
              apply Hdvc.
            }
            {
              apply cache_continuous_shift_e.
              exact Hccp.
            }
            { apply sub_prop_shift_e. exact Hsp. }
            { rewrite lookup_insert_ne.
              { intros HContra. subst q. apply Hnbq. simpl. exact I. }
              { unfold cache_incr_evar. replace q with (incr_one_evar q).
                2: { destruct q; simpl; try reflexivity. exfalso. apply Hnbq. simpl. exact I. }
                rewrite lookup_kmap. exact Hqin.
              }
            }
            { exact Hg0q. }
            { erewrite Heqp3. reflexivity. }
            apply IH.
          }
        }
        {
          case_match_in_hyp Hcall.
          {
            simpl in Hcall. rewrite Hcall in Hqin. rewrite Hqout in Hqin. inversion Hqin.
          }
          repeat case_match. invert_tuples. simpl in *.
          rewrite lookup_insert_Some in Hqout.
          destruct Hqout as [Heq|Hneq].
          {
            destruct Heq as [Heq1 Heq2].
            subst.
            exists Cin, evsin, s.
            simpl. rewrite Hqin.
            repeat case_match. invert_tuples. simpl in *.
            split; reflexivity.
          }
          {
            destruct Hneq as [Hneq1 Hnq].
            rewrite lookup_union_Some in Hnq.
            2: { apply remove_disjoint_keep_s. }
            destruct Hnq as [Hnq|Hnq].
            2: {
              unfold keep_bound_evars in Hnq.
              rewrite map_filter_lookup_Some in Hnq.
              destruct Hnq as [_ Hcontra].
              unfold is_bound_evar_entry in Hcontra. simpl in Hcontra.
              exfalso. apply Hnbq. apply bound_svar_is_bound_var.
              exact Hcontra.
            }
            unfold remove_bound_evars in Hnq.
            rewrite map_filter_lookup_Some in Hnq.
            destruct Hnq as [Hg0q _].

            epose proof (IH := IHsz p ltac:(lia) q nq _ _ _ _ Hnbq).
            feed specialize IH.
            {
              apply dangling_vars_cached_shift_s with (s := (svs_fresh s p)) in Hdvc.
              apply Hdvc.
            }
            {
              apply cache_continuous_shift_s.
              exact Hccp.
            }
            { apply sub_prop_shift_s. exact Hsp. }
            { rewrite lookup_insert_ne.
              { intros HContra. subst q. apply Hnbq. simpl. exact I. }
              { unfold cache_incr_evar. replace q with (incr_one_svar q).
                2: { destruct q; simpl; try reflexivity. exfalso. apply Hnbq. simpl. exact I. }
                rewrite lookup_kmap. exact Hqin.
              }
            }
            { exact Hg0q. }
            { erewrite Heqp3. reflexivity. }
            apply IH.
          }
        }
  Qed.

  Lemma cached_p_impl_called_with_p
    (C : Cache)
    (hg : History_generator C)
    (p : Pattern)
    (np : NamedPattern):
    ~ is_bound_var p ->
    C !! p = Some np ->
    exists (C' : Cache) (evs' : EVarSet) (svs' : SVarSet),
      C' !! p = None /\ (to_NamedPattern2' p C' evs' svs').1.1.1 = np.
  Proof.
    intros Hnboundp Hcached.
    destruct hg as [history Hhistory].
    move: p np C Hnboundp Hcached Hhistory.
    induction history; intros p np C Hnboundp Hcached Hhistory.
    {
      simpl in Hhistory. inversion Hhistory. subst C.
      rewrite lookup_empty in Hcached. inversion Hcached.
    }
    {
      destruct history.
      {
        simpl in Hhistory.
        destruct Hhistory as [Hhistory1 [Hhistory2 Hhistory3]].
        destruct a as [hip [[[hinp hiC] hievs] hisvs]].
        simpl in Hhistory1. subst hiC.
        clear Hhistory3 IHhistory.
        simpl in Hhistory2.
        destruct Hhistory2 as [Hhistory2a Hhistory2b].
        pose proof (Hfnc := find_nested_call hip empty empty empty C p np Hnboundp Hhistory2a).
        feed specialize Hfnc.
        { apply cache_continuous_empty. }
        { apply sub_prop_empty. }
        { apply lookup_empty. }
        { exact Hcached. }
        { rewrite -Hhistory2b. reflexivity. }
        apply Hfnc.
      }
      {
        destruct h as [hip [[[hinp hiC] hievs] hisvs]].
        destruct (hiC !! p) eqn:HeqhiCp.
        {
          admit.
        }
        {
          exists hiC, hievs, hisvs.
          destruct a as [ap [[[anp aC] aievs] aisvs]].
          split;[exact HeqhiCp|].
          simpl in Hhistory.
          destruct Hhistory as [Hhistory1 [Hhistory2 Hhistory3]].
          subst aC.
          specialize (Hhistory3 0). simpl in Hhistory3.
          destruct Hhistory3 as [p_i [HhiCp_i [Hdngl Hp_i]]].
          inversion Hp_i. subst ap. clear Hp_i.
          Check find_nested_call.
          pose proof (Hfnc := find_nested_call p_i hiC hievs hisvs C p np Hnboundp Hdngl).
          feed specialize Hfnc.
          eapply find_nested_call.
        }
        Print hist_prop.
        eapply IHhistory with (C := hiC).
        { exact Hnboundp. }
        { exact Hcached. }
        {
          simpl.
        }
      }
    }
  Qed.

  Lemma cached_imp_is_nimp
    (C : Cache)
    (hg : History_generator C)
    (p q : Pattern)
    (npq : NamedPattern):
    dangling_vars_cached C (patt_imp p q) -> (* Maybe not needed? *)
    C !! (patt_imp p q) = Some npq ->
    exists (np nq : NamedPattern), npq = npatt_imp np nq.
  Proof.
    intros Hdangling Hcached.
    destruct hg as [history Hhistory].
    move: p q npq C Hdangling Hhistory Hcached.
    induction history; intros p q npq C Hdangling Hhistory Hcached.
    {
      simpl in Hhistory. inversion Hhistory.
    }
    {
      simpl in Hhistory.
      destruct a as [p0 rest].
      destruct rest as [rest svs].
      destruct rest as [[np0 C'] evs].
      simpl in Hhistory.
      destruct Hhistory as [HC' Hhistory]. subst C'.
      remember (last ((p0, (np0, C, evs, svs)) :: history)) as Hlast.
      destruct Hlast.
      2: {
        destruct history.
        { simpl in HeqHlast. inversion HeqHlast. }
        {
          simpl in HeqHlast. rewrite last_cons in HeqHlast.
          destruct (last history) eqn:Hlh.
          {
            rewrite Hlh in HeqHlast. inversion HeqHlast.
          }
          {
            rewrite Hlh in HeqHlast. inversion HeqHlast.
          }
        }
      }
      rewrite -HeqHlast in Hhistory.
      destruct Hhistory as [Hhistory1 Hhistory2].
      destruct p1 as [p_l x_l]. subst x_l.

      destruct history.
      {
        simpl in HeqHlast. inversion HeqHlast. subst p_l. clear HeqHlast.
        (*clear IHhistory. *)
        destruct p0; simpl in H1;
        case_match_in_hyp H1; rewrite lookup_empty in Heqo; inversion Heqo; clear Heqo;
        inversion H1; subst; repeat case_match; invert_tuples;
        try (rewrite lookup_insert_ne in Hcached;[discriminate|];
        rewrite lookup_empty in Hcached; inversion Hcached).
        - rewrite lookup_insert_ne in Hcached.
          { discriminate. }
          apply dangling_vars_cached_proj_insert in Hdangling.
          2: { simpl. auto. }
          (* Contradiction. [g] cannot contain the implication. *)
          (*assert(empty !! patt_imp p q = None).*)
          assert (g0 !! patt_imp p q = None).
          {
            assert (~ (exists npq', g0 !! patt_imp p q = npq')).
            {
              intros HContra.
              pose proof (Honly1 := onlyAddsSubpatterns2 empty p0_1 empty empty).
              specialize (Honly1 (patt_imp p q)).
              feed specialize Honly1.
              {

              }
            }
            
          }
          
        
      }
      
    }
  Abort.

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
  Abort.

  (*
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
*)
End proof_system_translation.
