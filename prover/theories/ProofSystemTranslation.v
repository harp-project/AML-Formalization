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




   #[global]
   Instance NamedPattern_eqdec : EqDecision NamedPattern.
   Proof.
     solve_decision.
   Defined.
 
   Definition CES_prop (C : Cache) (evs : EVarSet) (svs : SVarSet) : Prop
   := (C = ∅) -> (evs = ∅ /\ svs = ∅).
 
   Lemma CES_prop_empty: CES_prop ∅ ∅ ∅.
   Proof. intros H. split; reflexivity. Qed.
 
   Lemma CES_prop_insert p np C evs svs:
     CES_prop (<[p := np]> C) evs svs.
   Proof.
     intros H. Search insert empty. exfalso.
     epose proof (Htmp := insert_non_empty C p np).
     contradiction.
   Qed.
 
 
   Lemma CES_prop_step p C evs svs:
     CES_prop C evs svs ->
     let: (_, C', evs', svs') := (to_NamedPattern2' p C evs svs) in
     CES_prop C' evs' svs'.
   Proof.
     intros HCES.
     induction p; simpl; repeat case_match; invert_tuples; try assumption;
       apply CES_prop_insert.
   Qed.
   
  Definition normal_hist_entry := (@Pattern signature * ((@NamedPattern signature) * Cache * (@EVarSet signature) * (@SVarSet signature)))%type.
  Definition inner_hist_entry := (Cache * (@EVarSet signature) * (@SVarSet signature))%type.
  Definition hist_entry := (normal_hist_entry + inner_hist_entry)%type.
  
  Definition pattern_of_nhe (h : normal_hist_entry) : (@Pattern signature) := h.1.
  Definition result_of_nhe (h : normal_hist_entry) := h.2.
  
  Definition cache_of_nhe (h : normal_hist_entry) : Cache := h.2.1.1.2.
  Definition evs_of_nhe (h : normal_hist_entry) : (@EVarSet signature) := h.2.1.2.
  Definition svs_of_nhe (h : normal_hist_entry) : (@SVarSet signature) := h.2.2.

  Definition cache_of_ihe (e : inner_hist_entry) : Cache := e.1.1.
  Definition evs_of_ihe (e : inner_hist_entry) : (@EVarSet signature) := e.1.2.
  Definition svs_of_ihe (e : inner_hist_entry) : (@SVarSet signature) := e.2.

  Definition cache_of (e : hist_entry) : Cache :=
    match e with
    | inl e' => cache_of_nhe e'
    | inr e' => cache_of_ihe e'
    end.

  Definition evs_of (e : hist_entry) : (@EVarSet signature) :=
    match e with
    | inl e' => evs_of_nhe e'
    | inr e' => evs_of_ihe e'
    end.

  Definition svs_of (e : hist_entry) : (@SVarSet signature) :=
    match e with
    | inl e' => svs_of_nhe e'
    | inr e' => svs_of_ihe e'
    end.
  
  Definition hist_prop (C : Cache) (evs : EVarSet) (svs : SVarSet) (history : list hist_entry) : Prop :=
    match history with
    | [] => C = ∅
    | (x::xs) =>
        cache_of x = C /\ evs_of x = evs /\ svs_of x = svs /\
          (match (last (x::xs)) with
           | None => False (* x::xs always has a last element *)
           | Some he =>
            match he with
            | inl nhe =>
              dangling_vars_cached ∅ (pattern_of_nhe nhe) /\
              result_of_nhe nhe = to_NamedPattern2' (pattern_of_nhe nhe) ∅ ∅ ∅
            | inr ihe =>
              exists (np : NamedPattern),
                (cache_of_ihe ihe = {[ patt_bound_evar 0 := np ]})
                \/
                (cache_of_ihe ihe = {[ patt_bound_svar 0 := np ]})
            end
           end) /\
          forall (i:nat), 
            match xs!!i with
            | None => True (* out of bounds, index too large *)
            (* p_i came from the result of the cache c_Si and everything before it *)
            | Some heSi => 
            let c_Si : Cache := (cache_of heSi) in
            let evs_Si := (evs_of heSi) in
            let svs_Si := (svs_of heSi) in
            CES_prop c_Si evs_Si svs_Si /\
              match ((x::xs)!!i) with
              | None => False (* this can never happen because i < length xs *)
              | Some hei =>
                match hei with
                | inl nhei => (
                  exists (p_i : Pattern), (
                    ((c_Si !! p_i) = None) /\ 
                    cache_continuous_prop c_Si /\  
                    sub_prop c_Si /\ 
                    dangling_vars_cached c_Si p_i /\
                    nhei = (p_i, (to_NamedPattern2' p_i c_Si evs_Si svs_Si))
                    )
                  )
                | inr ihei =>
                  (remove_bound_evars (cache_of_ihe ihei) = remove_bound_evars (cache_of heSi))
                  \/ (remove_bound_svars (cache_of_ihe ihei) = remove_bound_svars (cache_of heSi))
                end 
              end
            end
    end.

  Record History_generator (C : Cache) (evs : EVarSet) (svs : SVarSet) :=
    mkHistory {
        Hst_history : list hist_entry ;
        Hst_prop : hist_prop C evs svs Hst_history ;
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
    History_generator ∅ ∅ ∅.
  Proof.
    apply mkHistory with (Hst_history := []).
    simpl. reflexivity.
  Defined.

  Lemma history_generator_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet)
    (hC : History_generator C evs svs) :
    ((fmap evs_of (head (Hst_history C evs svs hC)) = Some evs /\
     fmap svs_of (head (Hst_history C evs svs hC)) = Some svs)
     \/ ( (Hst_history C evs svs hC = []) /\ C = ∅ /\ evs = ∅ /\ svs = ∅)) ->
    CES_prop C evs svs ->
    cache_continuous_prop C ->
    sub_prop C ->
    dangling_vars_cached C p ->
    let: (_, C', evs', svs') := to_NamedPattern2' p C evs svs in
    History_generator C' evs' svs'.
  Proof.
    intros Hevssvs HCES Hcont Hsubp HdcCp.
    destruct (C !! p) eqn:Hin.
    - repeat case_match. subst.
      exists (Hst_history C evs svs hC).
      destruct p; simpl in Heqp0; rewrite Hin in Heqp0; simpl;
        destruct hC; simpl in Heqp0; inversion Heqp0; subst; simpl; assumption.
    - repeat case_match. subst.
      exists ((inl (p, to_NamedPattern2' p C evs svs)) :: (Hst_history C evs svs hC)).
      simpl. rewrite Heqp0.
      split;[reflexivity|].
      split;[reflexivity|].
      split;[reflexivity|].
      destruct hC. simpl in *.

      destruct Hevssvs as [[Hevs Hsvs]|Hevssvs].
      {
        unfold hist_prop in Hst_prop0.
        destruct Hst_history0.
        { subst C. simpl in *. inversion Hevs. }
        destruct Hst_prop0 as [Hcache [H2evs [H2svs [HhistoryC Hinner]]]].
        subst evs svs.
        split.
        { subst C.
          destruct h as [hnormal|hinner].
          {
            destruct hnormal as [p0 [[[np0 C0] evs0] svs0]].
            simpl in * |-. inversion Hevs. inversion Hsvs. clear Hevs Hsvs. subst.
            repeat unfold fst,snd,svs_of,evs_of.
            unfold evs_of, svs_of in *. simpl in *.
            rewrite last_cons. rewrite last_cons in HhistoryC.
            destruct (last Hst_history0) eqn:Heqtmp.
            { exact HhistoryC. }
            { exact HhistoryC. }
          }
          {
            unfold evs_of, svs_of in *. simpl in *.
            rewrite last_cons. rewrite last_cons in HhistoryC.
            destruct (last Hst_history0) eqn:Heqtmp.
            { exact HhistoryC. }
            { exact HhistoryC. }
          }
        }
        destruct i; simpl.
        unfold evs_of, svs_of in *. simpl in *.
        inversion Hevs; inversion Hsvs; subst.
        repeat case_match; simpl in *; subst.
        + split;[exact HCES|].
          exists p. split. exact Hin. split.
          exact Hcont. split. exact Hsubp. split.
          exact HdcCp. rewrite Heqp0.
          reflexivity.
        + split;[exact HCES|].
          exists p. split. exact Hin. split.
          exact Hcont. split. exact Hsubp. split.
          exact HdcCp. rewrite Heqp0.
          reflexivity.
        + split;[exact HCES|].
          clear Hevs Hsvs. exists p. rewrite Heqp0. simpl.
          split;[exact Hin|].
          split;[exact Hcont|].
          split;[exact Hsubp|].
          split;[exact HdcCp|].
          reflexivity.
        + split;[exact HCES|].
        clear Hevs Hsvs. exists p. rewrite Heqp0. simpl.
        split;[exact Hin|].
        split;[exact Hcont|].
        split;[exact Hsubp|].
        split;[exact HdcCp|].
        reflexivity.
        + split;[exact HCES|].
        clear Hevs Hsvs. exists p. rewrite Heqp0. simpl.
        split;[exact Hin|].
        split;[exact Hcont|].
        split;[exact Hsubp|].
        split;[exact HdcCp|].
        reflexivity.
        + split;[exact HCES|].
        clear Hevs Hsvs. exists p. rewrite Heqp0. simpl.
        split;[exact Hin|].
        split;[exact Hcont|].
        split;[exact Hsubp|].
        split;[exact HdcCp|].
        reflexivity.
        + 
          apply Hinner.
      }
      {
        destruct Hevssvs as [H1 [H2 [H3 H4]]]. subst.
        split.
        {
          simpl. split. exact HdcCp. rewrite Heqp0. reflexivity.
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
    pose proof (Htrans := sub_prop_trans (to_NamedPattern2' p C evs svs).1.1.2 p (to_NamedPattern2' p C evs svs).1.1.1 q Hsubf Hnbound).
    feed specialize Htrans.
    { apply sub_prop_step; assumption. }
    { exact H. }
    exact Htrans.
  Qed.

 

  Lemma History_generator_shift_e Cin evsin svsin e:
  CES_prop Cin evsin svsin ->
  History_generator Cin evsin svsin ->
  History_generator (<[BoundVarSugar.b0:=npatt_evar e]> (cache_incr_evar Cin))
       (evsin ∪ {[e]}) svsin.
  Proof.
    intros HCES Hhist.
    destruct Hhist as [history Hhistory].
    exists ((inr ((<[BoundVarSugar.b0:=npatt_evar e]> (cache_incr_evar Cin)), (evsin ∪ {[e]}), svsin))::history).
    simpl.
    split.
    { reflexivity. }
    split.
    { reflexivity. }
    split.
    { reflexivity. }
    split.
    {
      rewrite last_cons.
      destruct (last history) eqn:Heqlsthist.
      {
        unfold hist_prop in Hhistory.
        destruct history.
        {
          simpl in Heqlsthist. inversion Heqlsthist.
        }
        rewrite Heqlsthist in Hhistory.
        destruct h as [nhe | ihe].
        {
          destruct Hhistory as [Hcache [Hevs [Hsvs Hhistory]]]. subst evsin svsin.
          destruct Hhistory as [[Hdngl Hresult] Hhistory].
          split. exact Hdngl. exact Hresult.
        }
        {
          destruct Hhistory as [Hcache [Hevs [Hsvs Hhistory]]]. subst evsin svsin.
          destruct Hhistory as [[np Hnp] Hhistory].
          exists np. exact Hnp.
        }
      }
      {
        unfold hist_prop in Hhistory.
        destruct history.
        2: { rewrite last_cons in Heqlsthist. destruct (last history); simpl in Heqlsthist; inversion Heqlsthist. }
        clear Heqlsthist.
        exists (npatt_evar e). left. subst Cin. reflexivity.
      }
    }
    {
      unfold hist_prop in Hhistory.
      destruct history.
      {
        intros i. simpl. exact I.
      }
      {
        destruct Hhistory as [Hcache [Hevs [Hsvs Hhistory]]]. subst Cin evsin svsin.
        destruct Hhistory as [Hlast Hhistory].
        intros i.
        destruct i; simpl.
        {
          split.
          {
            exact HCES.
          }
          left. repeat unfold cache_of_ihe,fst.
          unfold remove_bound_evars.
          rewrite map_filter_insert.
          unfold is_bound_evar_entry. simpl.
          rewrite map_filter_delete_not.
          {
            intros np. simpl. unfold cache_incr_evar.
            rewrite lookup_kmap_Some.
            intros [p [Hp1 Hp2]].
            destruct p; simpl in Hp1; inversion Hp1.
          }
          unfold cache_incr_evar.
          rewrite map_filter_strong_ext.
          intros p np. simpl.
          split; intros H.
          {
            destruct H as [H1 H2].
            split;[exact H1|].
            replace p with (incr_one_evar p) in H2.
            2: {
              destruct p; simpl; try reflexivity.
              exfalso. apply H1. exists n. reflexivity.
            }
            rewrite lookup_kmap in H2.
            exact H2.
          }
          {
            destruct H as [H1 H2].
            split;[exact H1|].
            replace p with (incr_one_evar p).
            2: {
              destruct p; simpl; try reflexivity.
              exfalso. apply H1. exists n. reflexivity.
            }
            rewrite lookup_kmap. exact H2.
          }
        }
        {
          apply Hhistory.
        }
      }
    }
  Defined.

  Lemma History_generator_shift_s Cin evsin svsin s:
  CES_prop Cin evsin svsin ->
  History_generator Cin evsin svsin ->
  History_generator (<[BoundVarSugar.B0:=npatt_svar s]> (cache_incr_svar Cin))
       evsin (svsin ∪ {[s]}).
  Proof.
    intros HCES Hhist.
    destruct Hhist as [history Hhistory].
    exists ((inr ((<[BoundVarSugar.B0:=npatt_svar s]> (cache_incr_svar Cin)), evsin, (svsin ∪ {[s]})))::history).
    simpl.
    split.
    { reflexivity. }
    split.
    { reflexivity. }
    split.
    { reflexivity. }
    split.
    {
      rewrite last_cons.
      destruct (last history) eqn:Heqlsthist.
      {
        unfold hist_prop in Hhistory.
        destruct history.
        {
          simpl in Heqlsthist. inversion Heqlsthist.
        }
        rewrite Heqlsthist in Hhistory.
        destruct h as [nhe | ihe].
        {
          destruct Hhistory as [Hcache [Hevs [Hsvs Hhistory]]]. subst evsin svsin.
          destruct Hhistory as [[Hdngl Hresult] Hhistory].
          split. exact Hdngl. exact Hresult.
        }
        {
          destruct Hhistory as [Hcache [Hevs [Hsvs Hhistory]]]. subst evsin svsin.
          destruct Hhistory as [[np Hnp] Hhistory].
          exists np. exact Hnp.
        }
      }
      {
        unfold hist_prop in Hhistory.
        destruct history.
        2: { rewrite last_cons in Heqlsthist. destruct (last history); simpl in Heqlsthist; inversion Heqlsthist. }
        clear Heqlsthist.
        exists (npatt_svar s). right. subst Cin. reflexivity.
      }
    }
    {
      unfold hist_prop in Hhistory.
      destruct history.
      {
        intros i. simpl. exact I.
      }
      {
        destruct Hhistory as [Hcache [Hevs [Hsvs Hhistory]]]. subst Cin evsin svsin.
        destruct Hhistory as [Hlast Hhistory].
        intros i.
        destruct i; simpl.
        {
          split.
          { exact HCES. }
          right. repeat unfold cache_of_ihe,fst.
          unfold remove_bound_svars.
          rewrite map_filter_insert.
          unfold is_bound_svar_entry. simpl.
          rewrite map_filter_delete_not.
          {
            intros np. simpl. unfold cache_incr_svar.
            rewrite lookup_kmap_Some.
            intros [p [Hp1 Hp2]].
            destruct p; simpl in Hp1; inversion Hp1.
          }
          unfold cache_incr_svar.
          rewrite map_filter_strong_ext.
          intros p np. simpl.
          split; intros H.
          {
            destruct H as [H1 H2].
            split;[exact H1|].
            replace p with (incr_one_svar p) in H2.
            2: {
              destruct p; simpl; try reflexivity.
              exfalso. apply H1. exists n. reflexivity.
            }
            rewrite lookup_kmap in H2.
            exact H2.
          }
          {
            destruct H as [H1 H2].
            split;[exact H1|].
            replace p with (incr_one_svar p).
            2: {
              destruct p; simpl; try reflexivity.
              exfalso. apply H1. exists n. reflexivity.
            }
            rewrite lookup_kmap. exact H2.
          }
        }
        {
          apply Hhistory.
        }
      }
    }
  Defined.

  Lemma remove_bound_evars_mono C1 C2:
  C1 ⊆ C2 -> remove_bound_evars C1 ⊆ remove_bound_evars C2.
Proof.
  intros H.
  unfold remove_bound_evars.
  apply map_filter_subseteq_mono.
  exact H.
Qed.

Lemma remove_bound_svars_mono C1 C2:
  C1 ⊆ C2 -> remove_bound_svars C1 ⊆ remove_bound_svars C2.
Proof.
  intros H.
  unfold remove_bound_svars.
  apply map_filter_subseteq_mono.
  exact H.
Qed.

Lemma remove_bound_evars_remove_bound_svars_comm C:
  remove_bound_evars (remove_bound_svars C) = remove_bound_svars (remove_bound_evars C).
Proof.
  unfold remove_bound_evars. unfold remove_bound_svars.
  apply map_filter_comm.
Qed.

  Lemma not_is_subformula_of_app_l p1 p2:
  ~ is_subformula_of_ind (patt_app p1 p2) p1.
  Proof. Admitted.

  Lemma not_is_subformula_of_app_r p1 p2:
  ~ is_subformula_of_ind (patt_app p1 p2) p2.
  Proof. Admitted.

  Lemma not_is_subformula_of_imp_l p1 p2:
  ~ is_subformula_of_ind (patt_imp p1 p2) p1.
  Proof. Admitted.

  Lemma not_is_subformula_of_imp_r p1 p2:
  ~ is_subformula_of_ind (patt_imp p1 p2) p2.
  Proof. Admitted.

  Lemma not_is_subformula_of_ex p:
  ~ is_subformula_of_ind (patt_exists p) p.
  Proof. Admitted.

  Lemma not_is_subformula_of_mu p:
  ~ is_subformula_of_ind (patt_mu p) p.
  Proof. Admitted.


  Lemma find_nested_call
    (p : Pattern)
    (Cin : Cache)
    (evsin : EVarSet)
    (svsin : SVarSet)
    (Cout : Cache)
    (q : Pattern)
    (nq : NamedPattern):
    CES_prop Cin evsin svsin ->
    ~ is_bound_var q ->
    History_generator Cin evsin svsin ->
    dangling_vars_cached Cin p ->
    cache_continuous_prop Cin ->
    sub_prop Cin ->
    Cin !! q = None ->
    Cout !! q = Some nq ->
    (to_NamedPattern2' p Cin evsin svsin).1.1.2 = Cout ->
    exists Cfound evsfound svsfound (HhistCfound : History_generator Cfound evsfound svsfound),
      Cfound !! q = None
      /\ remove_bound_evars (remove_bound_svars Cfound) ⊆ remove_bound_evars (remove_bound_svars Cout)
      /\ remove_bound_evars (remove_bound_svars Cin) ⊆ remove_bound_evars (remove_bound_svars Cfound)
      /\ CES_prop Cfound evsfound svsfound
      /\ cache_continuous_prop Cfound
      /\ sub_prop Cfound
      /\ dangling_vars_cached Cfound q
      /\ (to_NamedPattern2' q Cfound evsfound svsfound).1.1.1 = nq.
  Proof.
    intros HCES Hnbq Hhist Hdvc Hccp Hsp Hqin Hqout Hcall.
    remember (size' p) as sz.
    assert (Hsz: size' p <= sz) by lia.
    clear Heqsz.
    move: p Hsz q nq evsin svsin Cin HCES Cout Hnbq Hhist Hdvc Hccp Hsp Hqin Hqout Hcall.
    induction sz.
    { intros p Hsz; destruct p; simpl in Hsz; lia. }
    intros p Hsz; destruct p; simpl in Hsz; intros q nq evsin svsin Cin HCES Cout Hnbq Hhist Hdvc Hccp Hsp Hqin Hqout Hcall;
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
        exists Cin, evsin, svsin, Hhist.
        simpl.
        rewrite Hqin. simpl.
        split;[reflexivity|].
        split.
        {
          apply remove_bound_evars_mono.
          apply remove_bound_svars_mono.
          apply insert_subseteq.
          exact Hqin.
        }
        split.
        {
          apply reflexivity.
        }
        split;[apply HCES|].
        split;[apply Hccp|].
        split;[apply Hsp|].
        split;[apply Hdvc|].
        reflexivity.
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
        exists Cin, evsin, svsin, Hhist.
        simpl.
        rewrite Hqin. simpl.
        split;[reflexivity|].
        split.
        {
          apply remove_bound_evars_mono.
          apply remove_bound_svars_mono.
          apply insert_subseteq.
          exact Hqin.
        }
        split.
        {
          apply reflexivity.
        }
        split;[apply HCES|].
        split;[apply Hccp|].
        split;[apply Hsp|].
        split;[apply Hdvc|].
        reflexivity.
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
        exists Cin, evsin, svsin, Hhist.
        simpl.
        rewrite Hqin. simpl.
        split;[reflexivity|].
        split.
        {
          apply remove_bound_evars_mono.
          apply remove_bound_svars_mono.
          apply insert_subseteq.
          exact Hqin.
        }
        split.
        {
          apply reflexivity.
        }
        split;[apply HCES|].
        split;[apply Hccp|].
        split;[apply Hsp|].
        split;[apply Hdvc|].
        reflexivity.
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
        exists Cin, evsin, svsin, Hhist.
        simpl.
        rewrite Hqin. simpl.
        split;[reflexivity|].
        split.
        {
          apply remove_bound_evars_mono.
          apply remove_bound_svars_mono.
          apply insert_subseteq.
          exact Hqin.
        }
        split.
        {
          apply reflexivity.
        }
        split;[apply HCES|].
        split;[apply Hccp|].
        split;[apply Hsp|].
        split;[apply Hdvc|].
        reflexivity.
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
        exists Cin, evsin, svsin, Hhist.
        simpl.
        rewrite Hqin. simpl.
        split;[reflexivity|].
        split.
        {
          apply remove_bound_evars_mono.
          apply remove_bound_svars_mono.
          apply insert_subseteq.
          exact Hqin.
        }
        split.
        {
          apply reflexivity.
        }
        split;[apply HCES|].
        split;[apply Hccp|].
        split;[apply Hsp|].
        split;[apply Hdvc|].
        reflexivity.
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
        exists Cin, evsin, svsin, Hhist.
        simpl. rewrite Hqin.
        repeat case_match. invert_tuples. simpl in *.
        rewrite Heqp2 in Heqp5. inversion Heqp5. subst.
        split;[reflexivity|].
        split.
        {
          apply remove_bound_evars_mono.
          apply remove_bound_svars_mono.
          pose proof (Htmp1 := to_NamedPattern2'_extends_cache Cin p1 evsin svsin).
          rewrite Heqp0 in Htmp1. simpl in Htmp1.
          pose proof (Htmp2 := to_NamedPattern2'_extends_cache g0 p2 e0 s0).
          rewrite Heqp2 in Htmp2. simpl in Htmp2.
          eapply transitivity. apply Htmp1.
          eapply transitivity. apply Htmp2.
          apply insert_subseteq.

          destruct (g3 !! patt_app p1 p2) eqn:Hg3appp1p2;[|reflexivity].
          exfalso.
          destruct (g0 !! patt_app p1 p2) eqn:Hg0appp1p2.
          {
            pose proof (Htmp3 := onlyAddsSubpatterns2 Cin p1 evsin svsin (patt_app p1 p2) Hqin).
            feed specialize Htmp3.
            {
              rewrite Heqp0. simpl. exists n1. exact Hg0appp1p2.
            }
            eapply not_is_subformula_of_app_l. apply Htmp3.
          }
          {
            pose proof (Htmp4 := onlyAddsSubpatterns2 g0 p2 e0 s0 (patt_app p1 p2) Hg0appp1p2).
            feed specialize Htmp4.
            {
              rewrite Heqp2. simpl. exists n. exact Hg3appp1p2.
            }
            eapply not_is_subformula_of_app_r. apply Htmp4.
          }
        }
        split.
        {
          apply reflexivity.
        }
        split;[apply HCES|].
        split;[apply Hccp|].
        split;[apply Hsp|].
        split;[apply Hdvc|].
        reflexivity.
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
            

            epose proof (IH := IHsz p1 ltac:(lia) _ _ _ _ _ (ltac:(auto using CES_prop_step)) _ Hnbq Hhist Hdvcp1 Hccp Hsp Hqin Hg0q).
            erewrite Heqp1 in IH. simpl in IH. specialize (IH erefl).
            destruct IH as [Cfound [evsfound [svsfound [Hhistgen' [H1 H2]]]]].
            exists Cfound,evsfound,svsfound,Hhistgen'. split. exact H1.
            destruct H2 as [H21 [H22 H23]].
            split.
            {
              eapply transitivity. exact H21.
              eapply transitivity.
              { apply remove_bound_evars_mono. apply remove_bound_svars_mono. apply Hext. }
              apply remove_bound_evars_mono. apply remove_bound_svars_mono.
              apply insert_subseteq.

              destruct (g !! patt_app p1 p2) eqn:Hgappp1p2;[|reflexivity].
              exfalso.
              destruct (g0 !! patt_app p1 p2) eqn:Hg0appp1p2.
              {
                pose proof (Htmp3 := onlyAddsSubpatterns2 Cin p1 evsin svsin (patt_app p1 p2) Heqo).
                feed specialize Htmp3.
                {
                  rewrite Heqp1. simpl. exists n3. exact Hg0appp1p2.
                }
                eapply not_is_subformula_of_app_l. apply Htmp3.
              }
              {
                pose proof (Htmp4 := onlyAddsSubpatterns2 g0 p2 e0 s0 (patt_app p1 p2) Hg0appp1p2).
                feed specialize Htmp4.
                {
                  rewrite Heqp2. simpl. exists n2. exact Hgappp1p2.
                }
                eapply not_is_subformula_of_app_r. apply Htmp4.
              }
            }
            split.
            { exact H22. }
            exact H23.
          }
          {
            assert (Hhist': History_generator g0 e0 s0).
            {
              replace g0 with ((n0, g0, e0, s0).1.1.2) by reflexivity.
              rewrite -Heqp1.
              
              destruct (decide (Cin = ∅)).
              {
                subst Cin. 
                specialize (HCES erefl). destruct HCES as [HCES1 HCES2].
                subst.
                pose hempty := history_generator_empty.
                pose proof (Xstep := history_generator_step ∅ p1 ∅ ∅ hempty).
                feed specialize Xstep.
                {
                  right. unfold hempty. simpl.
                  repeat split; reflexivity.
                }
                {
                  apply CES_prop_empty.
                }
                { apply cache_continuous_empty. }
                { apply sub_prop_empty. }
                { exact Hdvcp1. }
                { repeat case_match. invert_tuples. simpl.
                  exact Xstep.
                }
              }
              {
                pose proof (Xstep := history_generator_step Cin p1 evsin svsin Hhist).
                feed specialize Xstep.
                {
                  left.
                  destruct Hhist as [Hst_history0 Hst_prop0].
                  simpl.
                  destruct Hst_history0.
                  { simpl in Hst_prop0. contradiction. }
                  { simpl in Hst_prop0. simpl.
                    pose proof (Hst_prop1 := Hst_prop0).
                    rewrite last_cons in Hst_prop1.
                    destruct Hst_history0.
                    { simpl in Hst_prop1. destruct_and?. subst.
                      split; reflexivity.
                    }
                    {
                      destruct_and?. subst. split; reflexivity.
                    }
                  }
                }
                { exact HCES. }
                { exact Hccp. }
                { exact Hsp. }
                { eapply dangling_vars_cached_imp_proj1. exact Hdvc. }
                repeat case_match. invert_tuples. simpl.
                exact Xstep.
              }
            }
            epose proof (IH := IHsz p2 ltac:(lia) _ _ _ _ _ _ _ Hnbq Hhist').
            feed specialize IH.
            {
              epose proof (Hextends := to_NamedPattern2'_extends_cache _ _ _ _).
              erewrite Heqp1 in Hextends. simpl in Hextends.
              epose proof (Htmp := dangling_vars_subcache _ _ _ Hdvcp2 Hextends).
              exact Htmp.
            }
            { epose proof (Htmp := cache_continuous_step _ _ _ _).
              erewrite Heqp1 in Htmp. simpl in Htmp.
              apply Htmp.
              { exact Hdvcp1. }
              exact Hccp.
            }
            { epose proof (Htmp := sub_prop_step _ _ _ _).
              erewrite Heqp1 in Htmp. simpl in Htmp.
              apply Htmp.
              { exact Hdvcp1. }
              { exact Hccp. }
              exact Hsp.
            }
            { exact Hg0q. }
            { exact Hnq. }
            { erewrite Heqp2. simpl. reflexivity. }
            destruct IH as [Cfound [evsfound [svsfound [Hhistgen' [H1 H2]]]]].
            exists Cfound,evsfound,svsfound,Hhistgen'. split. exact H1.
            destruct H2 as [H21 [H22 H23]].
            split.
            {
              eapply transitivity. apply H21.
              apply remove_bound_evars_mono. apply remove_bound_svars_mono.
              apply insert_subseteq.

              destruct (g !! patt_app p1 p2) eqn:Hgappp1p2;[|reflexivity].
              exfalso.
              destruct (g0 !! patt_app p1 p2) eqn:Hg0appp1p2.
              {
                pose proof (Htmp3 := onlyAddsSubpatterns2 Cin p1 evsin svsin (patt_app p1 p2) Heqo).
                feed specialize Htmp3.
                {
                  rewrite Heqp1. simpl. eexists. exact Hg0appp1p2.
                }
                eapply not_is_subformula_of_app_l. apply Htmp3.
              }
              {
                pose proof (Htmp4 := onlyAddsSubpatterns2 g0 p2 e0 s0 (patt_app p1 p2) Hg0appp1p2).
                feed specialize Htmp4.
                {
                  rewrite Heqp2. simpl. eexists. exact Hgappp1p2.
                }
                eapply not_is_subformula_of_app_r. apply Htmp4.
              }
            }
            split.
            {
              eapply transitivity.
              2: { apply H22. }
              epose proof (Htmp := to_NamedPattern2'_extends_cache _ _ _ _).
              erewrite Heqp1 in Htmp. simpl in Htmp.
              apply remove_bound_evars_mono. apply remove_bound_svars_mono. apply Htmp.
            }
            exact H23.
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
          exists Cin, evsin, svsin, Hhist.
          simpl.
          rewrite Hqin. simpl.
          split;[reflexivity|].
          split.
          {
            apply remove_bound_evars_mono.
            apply remove_bound_svars_mono.
            apply insert_subseteq.
            exact Hqin.
          }
          split.
          {
            apply reflexivity.
          }
          split;[apply HCES|].
          split;[apply Hccp|].
          split;[apply Hsp|].
          split;[apply Hdvc|].
          reflexivity.
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
          exists Cin, evsin, svsin, Hhist.
          simpl. rewrite Hqin.
          repeat case_match. invert_tuples. simpl in *.
          rewrite Heqp2 in Heqp5. inversion Heqp5. subst.
          split;[reflexivity|].
          split.
          {
            apply remove_bound_evars_mono.
            apply remove_bound_svars_mono.
            pose proof (Htmp1 := to_NamedPattern2'_extends_cache Cin p1 evsin svsin).
            rewrite Heqp0 in Htmp1. simpl in Htmp1.
            pose proof (Htmp2 := to_NamedPattern2'_extends_cache g0 p2 e0 s0).
            rewrite Heqp2 in Htmp2. simpl in Htmp2.
            eapply transitivity. apply Htmp1.
            eapply transitivity. apply Htmp2.
            apply insert_subseteq.
  
            destruct (g3 !! patt_imp p1 p2) eqn:Hg3appp1p2;[|reflexivity].
            exfalso.
            destruct (g0 !! patt_imp p1 p2) eqn:Hg0appp1p2.
            {
              pose proof (Htmp3 := onlyAddsSubpatterns2 Cin p1 evsin svsin (patt_imp p1 p2) Hqin).
              feed specialize Htmp3.
              {
                rewrite Heqp0. simpl. exists n1. exact Hg0appp1p2.
              }
              eapply not_is_subformula_of_imp_l. apply Htmp3.
            }
            {
              pose proof (Htmp4 := onlyAddsSubpatterns2 g0 p2 e0 s0 (patt_imp p1 p2) Hg0appp1p2).
              feed specialize Htmp4.
              {
                rewrite Heqp2. simpl. exists n. exact Hg3appp1p2.
              }
              eapply not_is_subformula_of_imp_r. apply Htmp4.
            }
          }
          split.
          {
            apply reflexivity.
          }
          split;[apply HCES|].
          split;[apply Hccp|].
          split;[apply Hsp|].
          split;[apply Hdvc|].
          reflexivity.
        }
        {
          destruct Hneq as [Hneq1 Hnq].
          
          assert (Hdvcp1: dangling_vars_cached Cin p1).
            {
              eapply dangling_vars_cached_imp_proj1. exact Hdvc.
            }
  
            assert (Hdvcp2: dangling_vars_cached Cin p2).
            {
              eapply dangling_vars_cached_imp_proj2. exact Hdvc.
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
              
  
              epose proof (IH := IHsz p1 ltac:(lia) _ _ _ _ _ (ltac:(auto using CES_prop_step)) _ Hnbq Hhist Hdvcp1 Hccp Hsp Hqin Hg0q).
              erewrite Heqp1 in IH. simpl in IH. specialize (IH erefl).
              destruct IH as [Cfound [evsfound [svsfound [Hhistgen' [H1 H2]]]]].
              exists Cfound,evsfound,svsfound,Hhistgen'. split. exact H1.
              destruct H2 as [H21 [H22 H23]].
              split.
              {
                eapply transitivity. exact H21.
                eapply transitivity.
                { apply remove_bound_evars_mono. apply remove_bound_svars_mono. apply Hext. }
                apply remove_bound_evars_mono. apply remove_bound_svars_mono.
                apply insert_subseteq.

                destruct (g !! patt_imp p1 p2) eqn:Hgappp1p2;[|reflexivity].
                exfalso.
                destruct (g0 !! patt_imp p1 p2) eqn:Hg0appp1p2.
                {
                  pose proof (Htmp3 := onlyAddsSubpatterns2 Cin p1 evsin svsin (patt_imp p1 p2) Heqo).
                  feed specialize Htmp3.
                  {
                    rewrite Heqp1. simpl. exists n3. exact Hg0appp1p2.
                  }
                  eapply not_is_subformula_of_imp_l. apply Htmp3.
                }
                {
                  pose proof (Htmp4 := onlyAddsSubpatterns2 g0 p2 e0 s0 (patt_imp p1 p2) Hg0appp1p2).
                  feed specialize Htmp4.
                  {
                    rewrite Heqp2. simpl. exists n2. exact Hgappp1p2.
                  }
                  eapply not_is_subformula_of_imp_r. apply Htmp4.
                }
              }
              split.
              { exact H22. }
              exact H23.
            }
            {
              assert (Hhist': History_generator g0 e0 s0).
              {
                replace g0 with ((n0, g0, e0, s0).1.1.2) by reflexivity.
                rewrite -Heqp1.
                
                destruct (decide (Cin = ∅)).
                {
                  subst Cin. 
                  specialize (HCES erefl). destruct HCES as [HCES1 HCES2].
                  subst.
                  pose hempty := history_generator_empty.
                  pose proof (Xstep := history_generator_step ∅ p1 ∅ ∅ hempty).
                  feed specialize Xstep.
                  {
                    right. unfold hempty. simpl.
                    repeat split; reflexivity.
                  }
                  { apply CES_prop_empty. }
                  { apply cache_continuous_empty. }
                  { apply sub_prop_empty. }
                  { exact Hdvcp1. }
                  { repeat case_match. invert_tuples. simpl.
                    exact Xstep.
                  }
                }
                {
                  pose proof (Xstep := history_generator_step Cin p1 evsin svsin Hhist).
                  feed specialize Xstep.
                  {
                    left.
                    destruct Hhist as [Hst_history0 Hst_prop0].
                    simpl.
                    destruct Hst_history0.
                    { simpl in Hst_prop0. contradiction. }
                    { simpl in Hst_prop0. simpl.
                      pose proof (Hst_prop1 := Hst_prop0).
                      rewrite last_cons in Hst_prop1.
                      destruct Hst_history0.
                      { simpl in Hst_prop1. destruct_and?. subst.
                        split; reflexivity.
                      }
                      {
                        destruct_and?. subst. split; reflexivity.
                      }
                    }
                  }
                  { exact HCES. }
                  { exact Hccp. }
                  { exact Hsp. }
                  { eapply dangling_vars_cached_imp_proj1. exact Hdvc. }
                  repeat case_match. invert_tuples. simpl.
                  exact Xstep.
                }
              }
              epose proof (IH := IHsz p2 ltac:(lia) _ _ _ _ _ _ _ Hnbq Hhist').
              feed specialize IH.
              {
                epose proof (Hextends := to_NamedPattern2'_extends_cache _ _ _ _).
                erewrite Heqp1 in Hextends. simpl in Hextends.
                epose proof (Htmp := dangling_vars_subcache _ _ _ Hdvcp2 Hextends).
                exact Htmp.
              }
              { epose proof (Htmp := cache_continuous_step _ _ _ _).
                erewrite Heqp1 in Htmp. simpl in Htmp.
                apply Htmp.
                { exact Hdvcp1. }
                exact Hccp.
              }
              { epose proof (Htmp := sub_prop_step _ _ _ _).
                erewrite Heqp1 in Htmp. simpl in Htmp.
                apply Htmp.
                { exact Hdvcp1. }
                { exact Hccp. }
                exact Hsp.
              }
              { exact Hg0q. }
              { exact Hnq. }
              { erewrite Heqp2. simpl. reflexivity. }
              destruct IH as [Cfound [evsfound [svsfound [Hhistgen' [H1 H2]]]]].
              exists Cfound,evsfound,svsfound,Hhistgen'. split. exact H1.
              destruct H2 as [H21 [H22 H23]].
              split.
              {
                eapply transitivity. apply H21.
                apply remove_bound_evars_mono. apply remove_bound_svars_mono.
                apply insert_subseteq.
  
                destruct (g !! patt_imp p1 p2) eqn:Hgappp1p2;[|reflexivity].
                exfalso.
                destruct (g0 !! patt_imp p1 p2) eqn:Hg0appp1p2.
                {
                  pose proof (Htmp3 := onlyAddsSubpatterns2 Cin p1 evsin svsin (patt_imp p1 p2) Heqo).
                  feed specialize Htmp3.
                  {
                    rewrite Heqp1. simpl. eexists. exact Hg0appp1p2.
                  }
                  eapply not_is_subformula_of_imp_l. apply Htmp3.
                }
                {
                  pose proof (Htmp4 := onlyAddsSubpatterns2 g0 p2 e0 s0 (patt_imp p1 p2) Hg0appp1p2).
                  feed specialize Htmp4.
                  {
                    rewrite Heqp2. simpl. eexists. exact Hgappp1p2.
                  }
                  eapply not_is_subformula_of_imp_r. apply Htmp4.
                }
              }
              split.
              {
                eapply transitivity.
                2: { apply H22. }
                epose proof (Htmp := to_NamedPattern2'_extends_cache _ _ _ _).
                erewrite Heqp1 in Htmp. simpl in Htmp.
                apply remove_bound_evars_mono. apply remove_bound_svars_mono. apply Htmp.
              }
              exact H23.
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
            exists Cin, evsin, s, Hhist.
            simpl. rewrite Hqin.
            repeat case_match. invert_tuples. simpl in *.
            split;[reflexivity|].
            split.
            {
              do 2 unfold remove_bound_evars at 1.
              do 2 unfold remove_bound_svars at 1.
              do 2 rewrite map_filter_filter.
              rewrite map_filter_insert.
              case_match.
              2: {
                exfalso. apply n. unfold is_bound_evar_entry,is_bound_svar_entry. simpl.
                split; intros [n' Hcontran']; inversion Hcontran'.
              }
              eapply transitivity.
              2: {
                apply insert_subseteq.
                rewrite map_filter_lookup_None.
                left.
                rewrite lookup_union_None.
                split.
                2: {
                  unfold keep_bound_evars.
                  rewrite map_filter_lookup_None.
                  left. exact Hqin.
                }
                epose proof (Hoas := onlyAddsSubpatterns2 _ _ _ _ (patt_exists p)).
                erewrite Heqp1 in Hoas. simpl in Hoas.
                destruct (g0 !! patt_exists p) eqn:Hgoexp.
                2: {
                  unfold remove_bound_evars.
                  rewrite map_filter_lookup_None. left. exact Hgoexp.
                }
                feed specialize Hoas.
                {
                  rewrite lookup_insert_ne.
                  { discriminate. }
                  unfold cache_incr_evar.
                  replace (patt_exists p) with (incr_one_evar (patt_exists p)) by reflexivity.
                  rewrite lookup_kmap. exact Hqin.
                }
                {
                  exists n. reflexivity.
                }
                exfalso. eapply not_is_subformula_of_ex. apply Hoas.
              }
              
              rewrite map_filter_strong_subseteq_ext.
              intros pi npi [[Hpi1 Hpi2] Hpi3].
              split.
              { split; assumption. }
              rewrite lookup_union_Some.
              2: { apply remove_disjoint_keep_e. }
              left.
              epose proof (Hextends := to_NamedPattern2'_extends_cache _ _ _ _).
              erewrite Heqp1 in Hextends. simpl in Hextends.
              unfold remove_bound_evars.
              rewrite map_filter_lookup_Some.
              split.
              2: { exact Hpi1. }
              eapply lookup_weaken.
              2: { apply Hextends. }
              rewrite lookup_insert_ne.
              { intros Hcontra. apply Hpi1. subst. exists 0. reflexivity. }
              unfold cache_incr_evar.
              replace pi with (incr_one_evar pi).
              2: { destruct pi; simpl; try reflexivity. exfalso. apply Hpi1. exists n. reflexivity. }
              rewrite lookup_kmap. exact Hpi3.
            }
            split.
            { apply reflexivity. }
            split;[apply HCES|].
            split;[apply Hccp|].
            split;[apply Hsp|].
            split;[apply Hdvc|].
            reflexivity.
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

            epose proof (IH := IHsz p ltac:(lia) q nq (evsin ∪ {[evs_fresh evsin p]}) s
              (<[BoundVarSugar.b0:=npatt_evar (evs_fresh evsin p)]> (cache_incr_evar Cin))
              (CES_prop_insert _ _ _ _ _)
              _ Hnbq
            ).
            feed specialize IH.
            {
              apply History_generator_shift_e.
              { exact HCES. }
              exact Hhist.
            }
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
            { rewrite Heqp3. reflexivity. }
            destruct IH as [Cfound [evsfound [svsfound [Hhistgen' [H1 H2]]]]].
            exists Cfound,evsfound,svsfound,Hhistgen'. split. exact H1.
            destruct H2 as [H21 [H22 H23]].
            split.
            {
              eapply transitivity. apply H21.
              do 2 unfold remove_bound_evars at 1.
              do 2 unfold remove_bound_svars at 1.
              do 2 rewrite map_filter_filter.
              rewrite map_filter_insert.
              case_match.
              2: {
                exfalso. apply n. split; intros Hcontra; destruct Hcontra as [x Hx]; inversion Hx.
              }
              clear Heqs1.
              eapply transitivity.
              2: {
                apply insert_subseteq.
                rewrite map_filter_lookup_None.
                left.
                rewrite lookup_union_None.
                split.
                2: {
                  unfold keep_bound_evars.
                  rewrite map_filter_lookup_None.
                  left. exact Heqo.
                }
                epose proof (Hoas := onlyAddsSubpatterns2 _ _ _ _ (patt_exists p)).
                erewrite Heqp3 in Hoas. simpl in Hoas.
                destruct (g0 !! patt_exists p) eqn:Hgoexp.
                2: {
                  unfold remove_bound_evars.
                  rewrite map_filter_lookup_None. left. exact Hgoexp.
                }
                feed specialize Hoas.
                {
                  rewrite lookup_insert_ne.
                  { discriminate. }
                  unfold cache_incr_evar.
                  replace (patt_exists p) with (incr_one_evar (patt_exists p)) by reflexivity.
                  rewrite lookup_kmap. exact Heqo.
                }
                {
                  exists n. reflexivity.
                }
                exfalso. eapply not_is_subformula_of_ex. apply Hoas.
              }
              rewrite map_filter_strong_subseteq_ext.
              intros pi npi [[Hpi1 Hpi2] Hpi3].
              split.
              { split; assumption. }
              rewrite lookup_union_Some.
              2: { apply remove_disjoint_keep_e. }
              left.
              unfold remove_bound_evars.
              rewrite map_filter_lookup_Some.
              split. exact Hpi3. exact Hpi1.
            }
            split.
            {
              eapply transitivity.
              2: { apply H22. }
              do 2 unfold remove_bound_evars at 1.
              do 2 unfold remove_bound_svars at 1.
              do 2 rewrite map_filter_filter.
              rewrite map_filter_insert.
              case_match.
              1: {
                destruct a as [a1 a2]. exfalso. apply a1. exists 0. reflexivity.
              }
              clear n Heqs1.
              rewrite map_filter_strong_subseteq_ext.
              intros ip nip [[Hip1 Hip2] Hip3].
              split.
              { split; assumption. }
              Search lookup delete.
              rewrite lookup_delete_Some.
              split.
              { intros HContra. apply Hip1. subst. exists 0. reflexivity. }
              unfold cache_incr_evar.
              replace ip with (incr_one_evar ip).
              2: {
                destruct ip; simpl; try reflexivity. exfalso. apply Hip1. exists n. reflexivity.
              }
              rewrite lookup_kmap.
              exact Hip3.
            }
            exact H23.
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
            exists Cin, evsin, s, Hhist.
            simpl. rewrite Hqin.
            repeat case_match. invert_tuples. simpl in *.
            split;[reflexivity|].
            split.
            {
              do 2 unfold remove_bound_evars at 1.
              do 2 unfold remove_bound_svars at 1.
              do 2 rewrite map_filter_filter.
              rewrite map_filter_insert.
              case_match.
              2: {
                exfalso. apply n. unfold is_bound_evar_entry,is_bound_svar_entry. simpl.
                split; intros [n' Hcontran']; inversion Hcontran'.
              }
              eapply transitivity.
              2: {
                apply insert_subseteq.
                rewrite map_filter_lookup_None.
                left.
                rewrite lookup_union_None.
                split.
                2: {
                  unfold keep_bound_evars.
                  rewrite map_filter_lookup_None.
                  left. exact Hqin.
                }
                epose proof (Hoas := onlyAddsSubpatterns2 _ _ _ _ (patt_mu p)).
                erewrite Heqp1 in Hoas. simpl in Hoas.
                destruct (g0 !! patt_mu p) eqn:Hgoexp.
                2: {
                  unfold remove_bound_evars.
                  rewrite map_filter_lookup_None. left. exact Hgoexp.
                }
                feed specialize Hoas.
                {
                  rewrite lookup_insert_ne.
                  { discriminate. }
                  unfold cache_incr_svar.
                  replace (patt_mu p) with (incr_one_svar (patt_mu p)) by reflexivity.
                  rewrite lookup_kmap. exact Hqin.
                }
                {
                  exists n. reflexivity.
                }
                exfalso. eapply not_is_subformula_of_mu. apply Hoas.
              }
              
              rewrite map_filter_strong_subseteq_ext.
              intros pi npi [[Hpi1 Hpi2] Hpi3].
              split.
              { split; assumption. }
              rewrite lookup_union_Some.
              2: { apply remove_disjoint_keep_s. }
              left.
              epose proof (Hextends := to_NamedPattern2'_extends_cache _ _ _ _).
              erewrite Heqp1 in Hextends. simpl in Hextends.
              unfold remove_bound_evars.
              rewrite map_filter_lookup_Some.
              split.
              2: { exact Hpi2. }
              eapply lookup_weaken.
              2: { apply Hextends. }
              rewrite lookup_insert_ne.
              { intros Hcontra. apply Hpi2. subst. exists 0. reflexivity. }
              unfold cache_incr_evar.
              replace pi with (incr_one_svar pi).
              2: { destruct pi; simpl; try reflexivity. exfalso. apply Hpi2. exists n. reflexivity. }
              rewrite lookup_kmap. exact Hpi3.
            }
            split.
            { apply reflexivity. }
            split;[apply HCES|].
            split;[apply Hccp|].
            split;[apply Hsp|].
            split;[apply Hdvc|].
            reflexivity.
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

            epose proof (IH := IHsz p ltac:(lia) q nq evsin (s ∪ {[svs_fresh s p]})
              (<[BoundVarSugar.B0:=npatt_svar (svs_fresh s p)]> (cache_incr_svar Cin))
              (CES_prop_insert _ _ _ _ _)
              _ Hnbq
            ).
            feed specialize IH.
            {
              apply History_generator_shift_s.
              { exact HCES. }
              exact Hhist.
            }
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
            { rewrite Heqp3. reflexivity. }
            destruct IH as [Cfound [evsfound [svsfound [Hhistgen' [H1 H2]]]]].
            exists Cfound,evsfound,svsfound,Hhistgen'. split. exact H1.
            destruct H2 as [H21 [H22 H23]].
            split.
            {
              eapply transitivity. apply H21.
              do 2 unfold remove_bound_evars at 1.
              do 2 unfold remove_bound_svars at 1.
              do 2 rewrite map_filter_filter.
              rewrite map_filter_insert.
              case_match.
              2: {
                exfalso. apply n. split; intros Hcontra; destruct Hcontra as [x Hx]; inversion Hx.
              }
              clear Heqs1.
              eapply transitivity.
              2: {
                apply insert_subseteq.
                rewrite map_filter_lookup_None.
                left.
                rewrite lookup_union_None.
                split.
                2: {
                  unfold keep_bound_evars.
                  rewrite map_filter_lookup_None.
                  left. exact Heqo.
                }
                epose proof (Hoas := onlyAddsSubpatterns2 _ _ _ _ (patt_mu p)).
                erewrite Heqp3 in Hoas. simpl in Hoas.
                destruct (g0 !! patt_mu p) eqn:Hgoexp.
                2: {
                  unfold remove_bound_svars.
                  rewrite map_filter_lookup_None. left. exact Hgoexp.
                }
                feed specialize Hoas.
                {
                  rewrite lookup_insert_ne.
                  { discriminate. }
                  unfold cache_incr_svar.
                  replace (patt_mu p) with (incr_one_svar (patt_mu p)) by reflexivity.
                  rewrite lookup_kmap. exact Heqo.
                }
                {
                  exists n. reflexivity.
                }
                exfalso. eapply not_is_subformula_of_mu. apply Hoas.
              }
              rewrite map_filter_strong_subseteq_ext.
              intros pi npi [[Hpi1 Hpi2] Hpi3].
              split.
              { split; assumption. }
              rewrite lookup_union_Some.
              2: { apply remove_disjoint_keep_s. }
              left.
              unfold remove_bound_svars.
              rewrite map_filter_lookup_Some.
              split. exact Hpi3. exact Hpi2.
            }
            split.
            {
              eapply transitivity.
              2: { apply H22. }
              do 2 unfold remove_bound_evars at 1.
              do 2 unfold remove_bound_svars at 1.
              do 2 rewrite map_filter_filter.
              rewrite map_filter_insert.
              case_match.
              1: {
                destruct a as [a1 a2]. exfalso. apply a2. exists 0. reflexivity.
              }
              clear n Heqs1.
              rewrite map_filter_strong_subseteq_ext.
              intros ip nip [[Hip1 Hip2] Hip3].
              split.
              { split; assumption. }
              rewrite lookup_delete_Some.
              split.
              { intros HContra. apply Hip2. subst. exists 0. reflexivity. }
              unfold cache_incr_evar.
              replace ip with (incr_one_svar ip).
              2: {
                destruct ip; simpl; try reflexivity. exfalso. apply Hip2. exists n. reflexivity.
              }
              rewrite lookup_kmap.
              exact Hip3.
            }
            exact H23.
          }
          Unshelve. all: auto.
          {
            epose proof (Htmp := CES_prop_step _ _ _ _).
            repeat case_match. subst. erewrite Heqp1 in Heqp.
            specialize (Htmp ltac:(assumption)).
            epose proof (Htmp2 := CES_prop_step _ _ _ _).
            repeat case_match. subst. erewrite Heqp2 in Heqp0. invert_tuples.
            exact Htmp.
          }
          {
            epose proof (Htmp := CES_prop_step _ _ _ _).
            repeat case_match. subst. erewrite Heqp1 in Heqp.
            specialize (Htmp ltac:(assumption)).
            epose proof (Htmp2 := CES_prop_step _ _ _ _).
            repeat case_match. subst. erewrite Heqp2 in Heqp0. invert_tuples.
            exact Htmp.
          }
        }
  Qed.


  Lemma hist_prop_strip_1 C evs svs a hip hinp hiC hievs hisvs history:
    hist_prop C evs svs (a :: (inl (hip, (hinp, hiC, hievs, hisvs))) :: history) ->
    hist_prop hiC hievs hisvs ((inl (hip, (hinp, hiC, hievs, hisvs))) :: history).
  Proof.
    intros HC.
    unfold hist_prop in *.
    destruct HC as [HC1 [Hevs [Hsvs [HC2 HC3]]]].
    subst C evs svs.
    split.
    { simpl. reflexivity. }
    split.
    { simpl. reflexivity. }
    split.
    { simpl. reflexivity. }
    split.
    { simpl in HC2. apply HC2. }
    clear HC2.
    intros i.
    specialize (HC3 (S i)).
    repeat case_match; subst; try exact I; try contradiction.
    {
      destruct HC3 as [HCES [p_i Hp_i]].
      rewrite lookup_cons_Some in Heqo0. simpl in Heqo0.
      rewrite lookup_cons_Some in Heqo. simpl in Heqo.
      destruct Heqo as [Heqo|Heqo].
      {
        destruct Heqo as [Hcontra _]. inversion Hcontra.
      }
      destruct Heqo as [_ Heqo].
      replace (i - 0) with i in Heqo by lia.
      replace (i - 0) with i in Heqo0 by lia.
      rewrite Heqo2 in Heqo0. inversion Heqo0; subst; clear Heqo0.
      { destruct H as [HContra _]. inversion HContra. }
      destruct H as [_ H]. inversion H. subst. clear H.
      rewrite Heqo in Heqo1. inversion Heqo1. subst. clear Heqo1.
      split.
      { exact HCES. }
      exists p_i.
      destruct_and!. split_and!; assumption.
    }
    {
      destruct HC3 as [HCES [p_i Hp_i]].
      rewrite lookup_cons_Some in Heqo0. simpl in Heqo0.
      rewrite lookup_cons_Some in Heqo. simpl in Heqo.
      destruct Heqo as [Heqo|Heqo].
      {
        destruct Heqo as [Hcontra _]. inversion Hcontra.
      }
      destruct Heqo as [_ Heqo].
      replace (i - 0) with i in Heqo by lia.
      replace (i - 0) with i in Heqo0 by lia.
      rewrite Heqo2 in Heqo0. inversion Heqo0; subst; clear Heqo0.
      { destruct H as [HContra _]. inversion HContra. }
      destruct H as [_ H]. inversion H.
    }
    {
      (* An ugly contradiction that we may extract into a lemma *)
      remember (inl (hip, (hinp, hiC, hievs, hisvs))) as b.
      clear -Heqo1 Heqo2.
      move: b history Heqo1 Heqo2.
      induction i; intros b history Heqo1 Heqo2.
      {
        simpl in *. inversion Heqo2.
      }
      {
        destruct history.
        { simpl in Heqo1. inversion Heqo1. }
        {
          simpl in *. eapply IHi. apply Heqo1. apply Heqo2.
        }
      }
    }
    {
      rewrite lookup_cons_Some in Heqo0. simpl in Heqo0.
      rewrite lookup_cons_Some in Heqo. simpl in Heqo.
      replace (i - 0) with i in Heqo by lia.
      replace (i - 0) with i in Heqo0 by lia.
      destruct Heqo as [Hcontra|Heqo].
      {
        destruct Hcontra as [Hcontra _]. inversion Hcontra.
      }
      destruct Heqo as [_ Heqo].
      destruct Heqo0 as [Hcontra|Heqo0].
      {
        destruct Hcontra as [Hcontra _]. inversion Hcontra.
      }
      destruct Heqo0 as [_ Heqo0].
      rewrite Heqo2 in Heqo0. inversion Heqo0.
    }
    {
      rewrite lookup_cons_Some in Heqo0. simpl in Heqo0.
      rewrite lookup_cons_Some in Heqo. simpl in Heqo.
      replace (i - 0) with i in Heqo by lia.
      replace (i - 0) with i in Heqo0 by lia.
      destruct Heqo as [Hcontra|Heqo].
      {
        destruct Hcontra as [Hcontra _]. inversion Hcontra.
      }
      destruct Heqo as [_ Heqo].
      destruct Heqo0 as [Hcontra|Heqo0].
      {
        destruct Hcontra as [Hcontra _]. inversion Hcontra.
      }
      destruct Heqo0 as [_ Heqo0].
      rewrite Heqo2 in Heqo0. inversion Heqo0.
      subst. clear Heqo0.
      rewrite Heqo in Heqo1. inversion Heqo1. subst. clear Heqo1.
      exact HC3.
    }
    {
      rewrite lookup_cons_Some in Heqo0. simpl in Heqo0.
      rewrite lookup_cons_Some in Heqo. simpl in Heqo.
      replace (i - 0) with i in Heqo by lia.
      replace (i - 0) with i in Heqo0 by lia.
      destruct Heqo as [Hcontra|Heqo].
      {
        destruct Hcontra as [Hcontra _]. inversion Hcontra.
      }
      destruct Heqo as [_ Heqo].
      destruct Heqo0 as [Hcontra|Heqo0].
      {
        destruct Hcontra as [Hcontra _]. inversion Hcontra.
      }
      destruct Heqo0 as [_ Heqo0].
      rewrite Heqo2 in Heqo0. inversion Heqo0.
    }
    {
      destruct HC3 as [_ HContra]. inversion HContra.
    }
    {
      destruct HC3 as [_ HContra]. inversion HContra.
    }
    {
      destruct HC3 as [_ HContra]. inversion HContra.
    }
    {
      rewrite lookup_cons in Heqo. 
      rewrite Heqo0 in Heqo. inversion Heqo.
    }
    {
      rewrite lookup_cons in Heqo. 
      rewrite Heqo0 in Heqo. inversion Heqo.
    }
    {
      rewrite lookup_cons in Heqo. 
      rewrite Heqo0 in Heqo. inversion Heqo.
    }
  Qed.

  Lemma hist_prop_strip_2 C evs svs a hiC hievs hisvs history:
    hist_prop C evs svs (a :: ((inr (hiC, hievs, hisvs)) :: history)) ->
    hist_prop hiC hievs hisvs ((inr (hiC, hievs, hisvs)) :: history).
  Proof.
    intros HC.
    unfold hist_prop in *.
    destruct HC as [HC1 [Hevs [Hsvs [HC2 HC3]]]].
    subst C evs svs.
    split.
    { simpl. reflexivity. }
    split.
    { simpl. reflexivity. }
    split.
    { simpl. reflexivity. }
    split.
    { simpl in HC2. apply HC2. }
    intros i.
    specialize (HC3 (S i)). simpl in HC3. apply HC3.
  Qed.


  Lemma hist_prop_subseteq C evs svs a b history:
    hist_prop C evs svs (a :: (inl b) :: history) ->
    remove_bound_evars (remove_bound_svars (cache_of_nhe b)) ⊆ remove_bound_evars (remove_bound_svars C).
  Proof.
    intros Hhist.
    unfold hist_prop in Hhist.
    destruct Hhist as [Hhist1 [Hevs [Hsvs [Hhist2 Hhist3]]]].
    subst C evs svs.
    specialize (Hhist3 0). simpl in Hhist3.
    repeat case_match; subst; simpl in *.
    {
      destruct Hhist3 as [p_i [Hcacheb [Hccp [Hsb [Hdngl [HCES Hn]]]]]].
      subst. unfold cache_of,evs_of,svs_of,
        svs_of_nhe,evs_of_nhe,cache_of_nhe,
        svs_of_ihe,evs_of_ihe,cache_of_ihe,fst,snd in *.
      repeat case_match; subst.
      {
        replace c0 with (n1, c0, e0, s0).1.1.2 by reflexivity.
        rewrite -Heqp4.
        apply remove_bound_evars_mono.
        apply remove_bound_svars_mono.
        apply to_NamedPattern2'_extends_cache.    
      }
    }
    {
      destruct Hhist3 as [p_i [Hcacheb [Hccp [Hsb [Hdngl [HCES Hn]]]]]].
      subst. unfold cache_of,evs_of,svs_of,
        svs_of_nhe,evs_of_nhe,cache_of_nhe,
        svs_of_ihe,evs_of_ihe,cache_of_ihe,fst,snd in *.
      repeat case_match; subst.
      {
        replace c1 with (n0, c1, e1, s1).1.1.2 by reflexivity.
        rewrite -Heqp5.
        apply remove_bound_evars_mono.
        apply remove_bound_svars_mono.
        apply to_NamedPattern2'_extends_cache.    
      }
    }
    {
      inversion Hhist2.
    }
    {
      destruct Hhist3 as [HCES [Hhist3|Hhist3]].
      {
        do 2 rewrite remove_bound_evars_remove_bound_svars_comm.
        rewrite -Hhist3.
        apply reflexivity.
      }
      {
        rewrite Hhist3. apply reflexivity.
      }
    }
    {
      destruct Hhist3 as [HCES [Hhist3|Hhist3]].
      {
        do 2 rewrite remove_bound_evars_remove_bound_svars_comm.
        rewrite -Hhist3.
        apply reflexivity.
      }
      {
        rewrite Hhist3. apply reflexivity.
      }
    }
    {
      inversion Hhist2.
    }
  Qed.
  
  Lemma cached_p_impl_called_with_p
    (C : Cache) (evs : EVarSet) (svs : SVarSet)
    (hg : History_generator C evs svs)
    (p : Pattern)
    (np : NamedPattern):
    CES_prop C evs svs ->
    ~ is_bound_var p ->
    C !! p = Some np ->
    exists (C' : Cache) (evs' : EVarSet) (svs' : SVarSet) (hgC' : History_generator C' evs' svs'),
      C' !! p = None
      /\ remove_bound_evars (remove_bound_svars C') ⊆ remove_bound_evars (remove_bound_svars C)
      /\ CES_prop C' evs' svs'
      /\ cache_continuous_prop C'
      /\ sub_prop C'
      /\ dangling_vars_cached C' p
      /\ (to_NamedPattern2' p C' evs' svs').1.1.1 = np.
  Proof.
    intros HCES Hnboundp Hcached.
    pose proof (hg' := hg).
    destruct hg as [history Hhistory].
    move: p np evs svs C hg' HCES Hnboundp Hcached Hhistory.
    induction history; intros p np evs svs C hg' HCES Hnboundp Hcached Hhistory.
    {
      simpl in Hhistory. inversion Hhistory. subst C.
      rewrite lookup_empty in Hcached. inversion Hcached.
    }
    {
      destruct history.
      {
        simpl in Hhistory.
        destruct Hhistory as [Hhistory1 [Hevs [Hsvs [Hhistory2 Hhistory3]]]].
        subst.
        destruct a as [nhe|ihe].
        {
          destruct nhe as [hip [[[hinp hiC] hievs] hisvs]].
          clear Hhistory3 IHhistory.
          simpl in Hhistory2.
          destruct Hhistory2 as [Hhistory2a Hhistory2b].
          pose proof (Hfnc := find_nested_call hip empty empty empty hiC p np (CES_prop_empty) Hnboundp history_generator_empty Hhistory2a).
          feed specialize Hfnc.
          { apply cache_continuous_empty. }
          { apply sub_prop_empty. }
          { apply lookup_empty. }
          { exact Hcached. }
          { rewrite -Hhistory2b. reflexivity. }
          cbn.
          destruct Hfnc as [Cfound [evsfound [svsfound [hgfound Hfnc]]]].
          exists Cfound,evsfound,svsfound,hgfound.
          destruct_and!. split_and!; assumption.
        }
        {
          destruct Hhistory2 as [np' [Hnp'|Hnp']].
          {
            unfold cache_of in Hcached. rewrite Hnp' in Hcached.
            unfold singletonM,map_singleton in Hcached.
            rewrite lookup_insert_Some in Hcached.
            destruct Hcached as [Hcached|Hcached].
            {
              destruct Hcached. subst. exfalso. apply Hnboundp.
              apply bound_evar_is_bound_var.
              exists 0. reflexivity.
            }
            {
              destruct Hcached as [_ Hcached].
              rewrite lookup_empty in Hcached.
              inversion Hcached.
            }
          }
          {
            unfold cache_of in Hcached. rewrite Hnp' in Hcached.
            unfold singletonM,map_singleton in Hcached.
            rewrite lookup_insert_Some in Hcached.
            destruct Hcached as [Hcached|Hcached].
            {
              destruct Hcached. subst. exfalso. apply Hnboundp.
              apply bound_svar_is_bound_var.
              exists 0. reflexivity.
            }
            {
              destruct Hcached as [_ Hcached].
              rewrite lookup_empty in Hcached.
              inversion Hcached.
            }
          }
        }
      }
      {
        destruct h as [nh|ih].
        {
          destruct nh as [hip [[[hinp hiC] hievs] hisvs]].
          destruct (hiC !! p) eqn:HeqhiCp.
          {
            
            pose proof (IH' := IHhistory p np hievs hisvs hiC).
            feed specialize IH'.
            { apply hist_prop_strip_1 in Hhistory. eexists. apply Hhistory. }
            { simpl in Hhistory.
              destruct Hhistory as [HC [Hevs [Hsvs Hhistory]]].
              subst.
              destruct Hhistory as [Hhistory1 Hhistory2].
              specialize (Hhistory2 0).
              simpl in Hhistory2.
              destruct Hhistory2 as [HCES' Hhistory2].
              apply HCES'.
            }
            { exact Hnboundp. }
            { pose proof (Htmp := HeqhiCp).
              assert(H: remove_bound_evars (remove_bound_svars hiC) ⊆ remove_bound_evars (remove_bound_svars C)).
              { 
                epose proof (Htmp' := hist_prop_subseteq _ _ _ _ _ _ Hhistory).
                apply Htmp'.
              }
              assert (Htmp2: (remove_bound_evars (remove_bound_svars hiC)) !! p = Some n).
              {
                unfold remove_bound_evars.
                rewrite map_filter_lookup_Some.
                split.
                2: { unfold is_bound_evar_entry. simpl. intros HContra. apply Hnboundp.
                  apply bound_evar_is_bound_var. exact HContra.
                }
                unfold remove_bound_svars.
                rewrite map_filter_lookup_Some.
                split.
                2: { unfold is_bound_svar_entry. simpl. intros HContra. apply Hnboundp.
                  apply bound_svar_is_bound_var. exact HContra.
                }
                exact Htmp.
              }
              apply lookup_weaken with (m2 := (remove_bound_evars (remove_bound_svars C))) in Htmp2.
              2: { exact H. }
              assert (Hcached2: (remove_bound_evars (remove_bound_svars C)) !! p = Some np ).
              {
                unfold remove_bound_evars.
                rewrite map_filter_lookup_Some.
                split.
                2: { unfold is_bound_evar_entry. simpl. intros HContra. apply Hnboundp.
                  apply bound_evar_is_bound_var. exact HContra.
                }
                unfold remove_bound_svars.
                rewrite map_filter_lookup_Some.
                split.
                2: { unfold is_bound_svar_entry. simpl. intros HContra. apply Hnboundp.
                  apply bound_svar_is_bound_var. exact HContra.
                }
                exact Hcached.
              }
              rewrite Htmp2 in Hcached2. inversion Hcached2. subst.
              exact Htmp.
            }
            { apply hist_prop_strip_1 in Hhistory. exact Hhistory. }
            
            destruct IH' as [C' [evs' [svs' [IH1 [IH2 IH3]]]]].
            subst.
            exists C',evs',svs', IH1.
            destruct_and!. split_and!; try assumption.

            eapply transitivity. apply H.
            simpl in Hhistory.
            destruct Hhistory as [HC [Hevs [Hsvs [Hhistory1 Hhistory2]]]].
            specialize (Hhistory2 0). simpl in Hhistory2. subst.
            destruct Hhistory2 as [HCES' Hhistory2].
            destruct a.
            {
              destruct Hhistory2 as [p_i Hp_i]. destruct_and!. subst. simpl.
              unfold cache_of_nhe. simpl.
              apply remove_bound_evars_mono. apply remove_bound_svars_mono.
              apply to_NamedPattern2'_extends_cache.
            }
            {
              destruct Hhistory2 as [Hhistory2|Hhistory2].
              {
                unfold cache_of. do 2 rewrite remove_bound_evars_remove_bound_svars_comm.
                apply remove_bound_svars_mono. rewrite Hhistory2. cbn.
                apply reflexivity.
              }
              {
                rewrite Hhistory2. cbn. apply reflexivity.
              }
            }
          }
          {
            pose proof (Hhistory' := Hhistory).
            apply hist_prop_strip_1 in Hhistory'.
            simpl in Hhistory.
            destruct Hhistory as [Hhistory1 [Hevs [Hsvs [Hhistory2 Hhistory3]]]].
            specialize (Hhistory3 0). simpl in Hhistory3.
            destruct Hhistory3 as [HCES' Hhistory3].
            destruct a as [anormal|ain].
            {
              destruct Hhistory3 as [p_i [HhiCp_i [Hcont_i [Hsubp_i [Hdngl Hp_i]]]]].
              destruct anormal as [ap [[[anp aC] aievs] aisvs]]. subst.
              inversion Hp_i. subst ap. clear Hp_i.
              cbn in HCES', HhiCp_i, Hcont_i, Hsubp_i, Hdngl, H1.
              (*unfold cache_of_nhe,evs_of_nhe,svs_of_nhe,fst,snd in *.*)
              pose proof (Hfnc := find_nested_call p_i hiC hievs hisvs aC p np HCES' Hnboundp).
              feed specialize Hfnc.
              {
                exists ((inl (hip, (hinp, hiC, hievs, hisvs)))::history).
                apply Hhistory'.
              }
              { exact Hdngl. }
              { exact Hcont_i. }
              { exact Hsubp_i. }
              { exact HeqhiCp. }
              { exact Hcached. }
              { rewrite -H1. reflexivity. }
              destruct Hfnc as [Cfound [evsfound [svsfound [hgfound Hfnc]]]].
              exists Cfound,evsfound,svsfound,hgfound.
              destruct_and!. split_and!; assumption.
            }
            {
              destruct ain as [[ainC ainE] ainS].
              clear Hhistory2.
              cbn in Hhistory3. cbn in HCES', Hhistory1, Hsvs, Hevs. subst ainC ainE ainS.
              clear -Hhistory3 HeqhiCp Hcached Hnboundp. exfalso.
              destruct Hhistory3 as [Hhistory3|Hhistory3].
              {
                assert (Hcached': (remove_bound_evars C) !! p = Some np).
                {
                  unfold remove_bound_evars. rewrite map_filter_lookup_Some.
                  split;[exact Hcached|]. unfold is_bound_evar_entry. simpl.
                  intros Hcontra. apply Hnboundp. apply bound_evar_is_bound_var.
                  exact Hcontra.
                }
                rewrite Hhistory3 in Hcached'.
                unfold remove_bound_evars in Hcached'.
                rewrite map_filter_lookup_Some in Hcached'.
                destruct Hcached' as [Hcontra _].
                rewrite HeqhiCp in Hcontra. inversion Hcontra.
              }
              {
                assert (Hcached': (remove_bound_svars C) !! p = Some np).
                {
                  unfold remove_bound_svars. rewrite map_filter_lookup_Some.
                  split;[exact Hcached|]. unfold is_bound_svar_entry. simpl.
                  intros Hcontra. apply Hnboundp. apply bound_svar_is_bound_var.
                  exact Hcontra.
                }
                rewrite Hhistory3 in Hcached'.
                unfold remove_bound_svars in Hcached'.
                rewrite map_filter_lookup_Some in Hcached'.
                destruct Hcached' as [Hcontra _].
                rewrite HeqhiCp in Hcontra. inversion Hcontra.
              }
            }
          }
        }
        {
          (*pose proof (Hhistory' := Hhistory).*)
          destruct ih as [[iC ievs] isvs].
          pose proof (Hhist_prop := Hhistory).
          eapply hist_prop_strip_2 in Hhist_prop.
          assert (Hhistory' : History_generator iC ievs isvs).
          {
            exists (inr (iC, ievs, isvs) :: history).
            apply Hhist_prop.
          }

          destruct (iC !! p) eqn:HiCp.
          {
            assert (n = np).
            {
              simpl in Hhistory. destruct Hhistory as [HC [Hevs [Hsvs [Hhistory1 Hhistory2]]]].
              subst. specialize (Hhistory2 0). simpl in Hhistory2.
              destruct Hhistory2 as [HCES' Hhistory2].
              destruct a.
              {
                destruct Hhistory2 as [p_i [Hhistory21 [Hhistory22 [Hhistory23 [Hhistory24 Hhistory25]]]]].
                subst. cbn in Hcached. unfold cache_of_nhe in Hcached. simpl in Hcached.
                pose proof (Hextends := to_NamedPattern2'_extends_cache iC p_i ievs isvs).
                eapply lookup_weaken in HiCp;[|apply Hextends].
                rewrite HiCp in Hcached. inversion Hcached.
                subst. reflexivity.
              }
              {
                destruct i. destruct p0. cbn in Hcached.
                cbn in Hhistory2.
                destruct Hhistory2 as [Hhistory2|Hhistory2].
                {
                  assert (HiCp': remove_bound_evars iC !! p = Some n).
                  {
                    unfold remove_bound_evars. rewrite map_filter_lookup_Some.
                    split. exact HiCp. unfold is_bound_evar_entry. simpl.
                    intros Hcontra. apply Hnboundp. apply bound_evar_is_bound_var.
                    apply Hcontra.
                  }
                  rewrite -Hhistory2 in HiCp'.
                  unfold remove_bound_evars in HiCp'.
                  rewrite map_filter_lookup_Some in HiCp'.
                  destruct HiCp' as [HiCp' _].
                  rewrite Hcached in HiCp'. inversion HiCp'. subst. reflexivity.
                }
                {
                  assert (HiCp': remove_bound_svars iC !! p = Some n).
                  {
                    unfold remove_bound_svars. rewrite map_filter_lookup_Some.
                    split. exact HiCp. unfold is_bound_svar_entry. simpl.
                    intros Hcontra. apply Hnboundp. apply bound_svar_is_bound_var.
                    apply Hcontra.
                  }
                  rewrite -Hhistory2 in HiCp'.
                  unfold remove_bound_svars in HiCp'.
                  rewrite map_filter_lookup_Some in HiCp'.
                  destruct HiCp' as [HiCp' _].
                  rewrite Hcached in HiCp'. inversion HiCp'. subst. reflexivity.
                }
              }
            }
            subst n.
            specialize (IHhistory p np  ievs isvs iC Hhistory').
            feed specialize IHhistory.
            {
              intros Hempty. subst iC. rewrite lookup_empty in HiCp. inversion HiCp.
            }
            { exact Hnboundp. }
            { exact HiCp. }
            { exact Hhist_prop. }
            destruct IHhistory as [C'' [evs'' [svs'' [hg'' IH'']]]].
            exists C'',evs'',svs'',hg''.
            destruct_and!. split_and!; try assumption.
            eapply transitivity. apply H1.
            simpl in Hhistory.
            destruct Hhistory as [HC [Hevs [Hsvs [Hhistory1 Hhistory2]]]].
            specialize (Hhistory2 0). simpl in Hhistory2.
            destruct Hhistory2 as [HCES2 Hhistory2].
            destruct a.
            {
              destruct Hhistory2 as [p_i Hp_i].
              destruct_and!. subst. cbn.
              apply remove_bound_evars_mono. apply remove_bound_svars_mono.
              apply to_NamedPattern2'_extends_cache.
            }
            {
              subst.
              destruct Hhistory2 as [Hhistory2|Hhistory2].
              {
                cbn in Hhistory2.
                do 2 rewrite remove_bound_evars_remove_bound_svars_comm.
                rewrite Hhistory2.
                apply reflexivity.
              }
              {
                cbn in Hhistory2.
                rewrite Hhistory2.
                apply reflexivity.
              }
            }
          }
          {
            simpl in Hhistory.
            destruct Hhistory as [HC [Hevs [Hsvs [Hhistory1 Hhistory2]]]]. subst.
            specialize (Hhistory2 0). simpl in Hhistory2.
            destruct Hhistory2 as [HCES' Hhistory2].
            destruct a.
            {
              destruct Hhistory2 as [p_i [Hhistory21 [Hhistory22 [Hhistory23 [Hhistory24 Hhistory25]]]]].
              subst. cbn in Hhistory21,Hhistory22,Hhistory23,Hhistory24, Hcached.
              unfold cache_of_nhe in Hcached. cbn in Hcached.
              pose proof (Hfnc := find_nested_call p_i iC ievs isvs).
              specialize (Hfnc (to_NamedPattern2' p_i iC ievs isvs).1.1.2 p np HCES').
              specialize (Hfnc Hnboundp Hhistory' Hhistory24 Hhistory22 Hhistory23 HiCp).
              specialize (Hfnc Hcached erefl).
              destruct Hfnc as [Cfound [evsfound [svsfound [hgfound Hfnc]]]].
              exists Cfound,evsfound,svsfound,hgfound.
              destruct_and!. split_and!; assumption.
            }
            {
              destruct i as [[iC' ievs'] isvs']. cbn in Hhistory2.
              destruct Hhistory2 as [Hhistory2|Hhistory2].
              {
                cbn in Hcached.
                assert (Hcached2: remove_bound_evars iC' !! p = Some np).
                {
                  unfold remove_bound_evars. rewrite map_filter_lookup_Some.
                  split. exact Hcached. unfold is_bound_evar_entry. simpl.
                  intros Hcontra. apply Hnboundp. apply bound_evar_is_bound_var.
                  apply Hcontra.
                }
                rewrite Hhistory2 in Hcached2.
                unfold remove_bound_evars in Hcached2.
                rewrite map_filter_lookup_Some in Hcached2.
                destruct Hcached2 as [Hcached2 _]. rewrite HiCp in Hcached2.
                inversion Hcached2.
              }
              {
                cbn in Hcached.
                assert (Hcached2: remove_bound_svars iC' !! p = Some np).
                {
                  unfold remove_bound_svars. rewrite map_filter_lookup_Some.
                  split. exact Hcached. unfold is_bound_svar_entry. simpl.
                  intros Hcontra. apply Hnboundp. apply bound_svar_is_bound_var.
                  apply Hcontra.
                }
                rewrite Hhistory2 in Hcached2.
                unfold remove_bound_svars in Hcached2.
                rewrite map_filter_lookup_Some in Hcached2.
                destruct Hcached2 as [Hcached2 _]. rewrite HiCp in Hcached2.
                inversion Hcached2.
              }
            }
          }
        }
      }
    }
  Qed.

  Lemma not_bound_evar_and_not_bound_svar_impl_not_bound_var (p : Pattern):
    ~ is_bound_evar p ->
    ~ is_bound_svar p ->
    ~ is_bound_var p.
  Proof.
    intros H1 H2.
    destruct p; simpl in *; auto.
    { exfalso. apply H1. exists n. reflexivity. }
    { exfalso. apply H2. exists n. reflexivity. }
  Qed.

  Instance is_bound_var_dec (p : Pattern) : Decision (is_bound_var p).
  Proof.
    destruct (decide (is_bound_evar p)).
    {
      left. apply bound_evar_is_bound_var. assumption.
    }
    destruct (decide (is_bound_svar p)).
    {
      left. apply bound_svar_is_bound_var. assumption.
    }
    right.
    apply not_bound_evar_and_not_bound_svar_impl_not_bound_var; assumption.
  Defined.

  Lemma cached_anyway C p:
    dangling_vars_cached C p ->
    bound_or_cached C p ->
    exists np1, C !! p = Some np1.
  Proof.
    intros Hdngcached Hbocp.
    unfold dangling_vars_cached in Hdngcached.
    destruct Hdngcached as [Hdngcachede Hdngcacheds].
    destruct (decide (is_bound_evar p)) as [Hboundep|Hnboundep].
    {
      destruct p; unfold is_bound_evar in Hboundep; simpl in Hboundep;
      destruct Hboundep as [b Hb]; inversion Hb; subst.
      unfold dangling_evars_cached in Hdngcachede.
      specialize (Hdngcachede b).
      simpl in Hdngcachede.
      destruct (decide (b = b));[|contradiction].
      apply Hdngcachede. reflexivity.
    }
    destruct (decide (is_bound_svar p)) as [Hboundsp|Hnboundsp].
    {
      destruct p; unfold is_bound_svar in Hboundsp; simpl in Hboundsp;
      destruct Hboundsp as [b Hb]; inversion Hb; subst.
      unfold dangling_svars_cached in Hdngcacheds.
      specialize (Hdngcacheds b).
      simpl in Hdngcacheds.
      destruct (decide (b = b));[|contradiction].
      apply Hdngcacheds. reflexivity.
    }
    assert (~ is_bound_var p).
    {
      apply not_bound_evar_and_not_bound_svar_impl_not_bound_var; assumption.
    }
    destruct Hbocp as [Hbp|Hcp].
    {
      contradiction.
    }
    exact Hcp.
  Qed.


  Definition inv_sub_prop (C : Cache) :=
    forall (p : Pattern) (np : NamedPattern),
    (* dangling_vars_cached C p -> *)
    C !! p = Some np ->
    match p with
    | patt_free_evar _ => True
    | patt_free_svar _ => True
    | patt_bound_evar _ => True
    | patt_bound_svar _ => True
    | patt_bott => True
    | patt_sym _ => True
    | patt_imp p' q' =>
(*      ~ is_bound_var p' ->
      ~ is_bound_var q' -> *)
      (forall np' nq',
        C !! p' = Some np' ->
        C !! q' = Some nq' -> (*
        dangling_vars_cached C p' /\ dangling_vars_cached C q' /\ *)
        np = npatt_imp np' nq')
    | patt_app p' q' => 
(*      ~ is_bound_var p' ->
      ~ is_bound_var q' -> *)
      (forall np' nq',
      C !! p' = Some np' ->
      C !! q' = Some nq' -> (*
      dangling_vars_cached C p' /\ dangling_vars_cached C q' /\ *)
      np = npatt_app np' nq')
    | patt_exists p' =>
(*      ~ is_bound_var p' -> *)
      (forall np' e,
        C !! p' = Some np' ->
        C !! (patt_bound_evar 0) = Some (npatt_evar e) ->
        np = npatt_exists e np'
      )
    | patt_mu p' =>
(*      ~ is_bound_var p' -> *)
      (forall np' s,
        C !! p' = Some np' ->
        C !! (patt_bound_svar 0) = Some (npatt_svar s) ->
        np = npatt_mu s np'
      )    
    end.

  Lemma inv_sub_prop_empty: inv_sub_prop ∅.
  Proof.
    intros p np (*Hcached*) H. rewrite lookup_empty in H. inversion H.
  Qed.

  (* This does not hold as is. *)
  
  Lemma inv_sub_prop_shift_e C e:
    sub_prop C ->
    inv_sub_prop C ->
    inv_sub_prop
      (<[BoundVarSugar.b0:=npatt_evar e]> (cache_incr_evar C)).
  Proof.
    intros Hsubp Hinv.
    intros p np (*Hcached*) Hp.
    destruct p; try exact I.
    {
      intros np' nq' Hnp' Hnq'.
      rewrite lookup_insert_ne in Hp.
      { discriminate. }
      (*Check dangling_vars_cached_shift_e.
      apply dangling_vars_cached_shift_e in Hdngl. *)
      unfold cache_incr_evar in Hp.
      replace (patt_app p1 p2) with (incr_one_evar (patt_app p1 p2)) in Hp by reflexivity.
      rewrite lookup_kmap in Hp.
      specialize (Hinv (patt_app p1 p2) np). simpl in Hinv.
      specialize (Hinv Hp).
      (*pose proof (Hsub' := Hsubp _ _ Hp). simpl in Hsub'.*)

      rewrite lookup_insert_Some in Hnp'.
      rewrite lookup_insert_Some in Hnq'.
      destruct Hnp',Hnq'; destruct_and!; subst.
      {
        Print inv_sub_prop.
        admit.
      }
      admit. admit. admit.
    }
  Abort.

  Lemma inv_sub_prop_step C p evs svs:
  sub_prop C ->
  cache_continuous_prop C ->
  dangling_vars_cached C p ->
  inv_sub_prop C ->
  inv_sub_prop (to_NamedPattern2' p C evs svs).1.1.2.
Proof.
  intros Hsubp Hcont Hdngl H.
  move: C evs svs Hsubp Hcont Hdngl H.
  induction p; intros C evs svs Hsubp Hcont Hdngl H; simpl; case_match; simpl; try exact H.
    Local Ltac contradict_not_cached Hdngl Heqo Hboc :=
    lazymatch type of Heqo with
    | (?C !! ?formula = None) =>
      assert (Hnp1: exists np1, C !! formula = Some np1);
      [(
        apply cached_anyway;
        [ exact Hdngl
        | exact Hboc
        ]
      )|];
      destruct Hnp1 as [np1 Hnp1];
      rewrite Heqo in Hnp1; inversion Hnp1
    end.
    Local Ltac solve_app_imp Hsubp Hinvsub Hdngl Heqo Hp :=
      lazymatch type of Hp with
      | (_ !! ?app_or_imp = Some ?np) =>
        intros np' nq' Hnp' Hnq';
        rewrite lookup_insert_ne in Hp;
        [discriminate|];
        rewrite lookup_insert_Some in Hnp';
        rewrite lookup_insert_Some in Hnq';
        pose proof (Hsubp' := Hsubp app_or_imp np Hp);
        simpl in Hsubp'; destruct Hsubp' as [Hbocp1 Hbocp2];
        destruct Hnp',Hnq'; destruct_and!; subst;
        [(contradict_not_cached Hdngl Heqo Hbocp1)
        |(contradict_not_cached Hdngl Heqo Hbocp1)
        |(contradict_not_cached Hdngl Heqo Hbocp2)
        |(pose proof (Hinv' := Hinvsub app_or_imp np Hp); simpl in Hinv'; apply Hinv'; assumption)
        ]
      end.
    Local Ltac solve_mu_ex Hsubp Hinvsub Hdngl Heqo Hp :=
      lazymatch type of Hp with
      | (_ !! ?mu_or_ex = Some ?np) =>
        intros np' nq' Hnp' Hnq';
        rewrite lookup_insert_ne in Hp;
        [discriminate|];
        rewrite lookup_insert_Some in Hnp';
        rewrite lookup_insert_Some in Hnq';
        pose proof (Hsubp' := Hsubp mu_or_ex np Hp);
        let Hbocp := fresh "Hbocp" in
        simpl in Hsubp'; rename Hsubp' into Hbocp;
        destruct Hnp',Hnq'; destruct_and!; subst;
        [(contradict_not_cached Hdngl Heqo Hbocp)
        |(contradict_not_cached Hdngl Heqo Hbocp)
        |(inversion H2)
        |(pose proof (Hinv' := Hinvsub mu_or_ex np Hp); simpl in Hinv'; apply Hinv'; assumption)
        ]
      end.
  - intros p np Hp.
    destruct p; try exact I.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
  - intros p np Hp.
    destruct p; try exact I.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
  - intros p np Hp.
    destruct p; try exact I.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp. inversion H3.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
    - intros p np Hp.
    destruct p; try exact I.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp. inversion H3.
  - intros p np Hp.
    destruct p; try exact I.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
  - intros p np Hp.
  Local Ltac app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp Hinvsub :=
  lazymatch type of Heqo with
  | (?C !! ?app_or_imp = None) => (
    lazymatch type of Heqp1 with
    | (to_NamedPattern2' ?p1 ?C ?evs ?svs = (?n0, ?g0, ?e0, ?s0)) => (
      lazymatch type of Heqp2 with
      | (to_NamedPattern2' ?p2 ?g0 ?e0 ?s0 = (?n1, ?g, ?e, ?s)) => (
        assert (HdngCp1: dangling_vars_cached C p1);
        [((eapply dangling_vars_cached_imp_proj1 + eapply dangling_vars_cached_app_proj1); apply Hdngl)|];
        assert (Hsubpg0: sub_prop g0);
        [(
          epose proof (Htmp := sub_prop_step _ _ _ _);
          erewrite Heqp1 in Htmp; simpl in Htmp;
          specialize (Htmp HdngCp1 Hcont Hsubp);
          exact Htmp
        )|];
        assert (Hcontg0: cache_continuous_prop g0);
        [(
          epose proof (Htmp := cache_continuous_step _ _ _ _);
          erewrite Heqp1 in Htmp; simpl in Htmp;
          specialize (Htmp HdngCp1 Hcont);
          exact Htmp
        )|];
        assert (HCsubg0: C ⊆ g0);
        [(
          epose proof (Htmp := to_NamedPattern2'_extends_cache _ _ _ _);
          erewrite Heqp1 in Htmp; simpl in Htmp;
          exact Htmp
        )|];
        assert (Hg0subg: g0 ⊆ g);
        [(
          epose proof (Htmp := to_NamedPattern2'_extends_cache _ _ _ _);
          erewrite Heqp2 in Htmp; simpl in Htmp;
          exact Htmp
        )|];
        assert (Hdnglg0: dangling_vars_cached g0 app_or_imp);
        [(
          eapply dangling_vars_subcache;
          [apply Hdngl
          |exact HCsubg0
          ]
        )|];
        assert (Hdnglg: dangling_vars_cached g app_or_imp);
        [(
          eapply dangling_vars_subcache;
          [apply Hdnglg0
          |exact Hg0subg
          ]
        )|];
        assert (Hdnglg0p2: dangling_vars_cached g0 p2);
        [(eapply dangling_vars_cached_app_proj2; exact Hdnglg0)|];
        assert (Hsubpg: sub_prop g);
        [(
          epose proof (Htmp := sub_prop_step _ _ _ _);
          erewrite Heqp2 in Htmp; simpl in Htmp;
          specialize (Htmp Hdnglg0p2 Hcontg0 Hsubpg0);
          exact Htmp
        )|];
        epose proof (IH1 := IHp1 _ _ _);
        erewrite Heqp1 in IH1; simpl in IH1;
        specialize (IH1 Hsubp Hcont HdngCp1 Hinvsub);
        clear IHp1;
        epose proof (IH2 := IHp2 _ _ _);
        erewrite Heqp2 in IH2; simpl in IH2;
        specialize (IH2 Hsubpg0 Hcontg0 Hdnglg0p2 IH1);
        assert (Hg0p1n0: g0 !! p1 = Some n0);
        [(
          epose proof (Htmp := to_NamedPattern2'_ensures_present _ _ _ _);
          erewrite Heqp1 in Htmp; simpl in Htmp;
          exact Htmp
        )|];
        assert (Hgp1n0: g !! p1 = Some n0);
        [(
          eapply lookup_weaken;[apply Hg0p1n0|apply Hg0subg]
        )|];
        assert (Hgp2n1: g !! p2 = Some n1);
        [(
          epose proof (Htmp := to_NamedPattern2'_ensures_present _ _ _ _);
          erewrite Heqp2 in Htmp; simpl in Htmp;
          exact Htmp
        )|];
        assert(Hg0appp1p2: g0 !! app_or_imp = None);
        [(
          let Hg0app := fresh "Hg0app" in
          destruct (g0 !! app_or_imp) eqn:Hg0app;[exfalso|reflexivity];
          pose proof (Htmp := onlyAddsSubpatterns2 C p1 evs svs app_or_imp Heqo);
          feed specialize Htmp;
          [(
            eexists; erewrite Heqp1; simpl; apply Hg0app
          )|];
          (*eauto using not_is_subformula_of_app_l,not_is_subformula_of_imp_l,Htmp*)
          (eapply not_is_subformula_of_app_l + eapply not_is_subformula_of_imp_l); apply Htmp
        )|];
        assert(Hgappp1p2: g !! app_or_imp = None);
        [(
          let Hg0app := fresh "Hg0app" in
          destruct (g !! app_or_imp) eqn:Hg0app;[exfalso|reflexivity];
          pose proof (Htmp := onlyAddsSubpatterns2 g0 p2 e0 s0 app_or_imp Hg0appp1p2);
          feed specialize Htmp;
          [(
            eexists; erewrite Heqp2; simpl; apply Hg0app
          )|];
          (*eauto using not_is_subformula_of_app_r,not_is_subformula_of_imp_r,Htmp*)
          (eapply not_is_subformula_of_app_r + eapply not_is_subformula_of_imp_r); apply Htmp
        )|])
      end)
    end)
  end.

    destruct p; try exact I.
    + repeat case_match. subst. invert_tuples. simpl in *.
      intros np' nq' Hnp' Hnq'.
      app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp H.
      (** end of preparation phase. **)

      rewrite lookup_insert_Some in Hp.
      destruct Hp as [Hp|Hp].
      {
        destruct Hp as [Hp1 Hp2]. inversion Hp1. subst. clear Hp1.
        rewrite lookup_insert_ne in Hnp'.
        { apply app_neq1. }
        rewrite lookup_insert_ne in Hnq'.
        { apply app_neq2. }
        congruence.
      }
      {
        destruct Hp as [Hp1 Hp2].
        rewrite lookup_insert_Some in Hnp'.
        rewrite lookup_insert_Some in Hnq'.
        destruct Hnp',Hnq'; destruct_and!; subst.
        {
          pose proof (Hsubp' := Hsubpg (patt_app (patt_app p1 p2) (patt_app p1 p2)) np Hp2).
          simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
          contradict_not_cached Hdnglg Hgappp1p2 Hbocp1.
        }
        {
          pose proof (Hsubp' := Hsubpg (patt_app (patt_app p1 p2) p4) np Hp2).
          simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
          contradict_not_cached Hdnglg Hgappp1p2 Hbocp1.
        }
        {
          pose proof (Hsubp' := Hsubpg (patt_app p3 (patt_app p1 p2)) np Hp2).
          simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
          contradict_not_cached Hdnglg Hgappp1p2 Hbocp2.
        }
        {
          pose proof (Hinv' := IH2 (patt_app p3 p4) np Hp2).
          simpl in Hinv'; apply Hinv'; assumption.
        }
      }
    + repeat case_match. subst. invert_tuples. simpl in *.
      intros np' nq' Hnp' Hnq'.
      app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp H.
      (** end of preparation phase. **)

      rewrite lookup_insert_Some in Hp.
      destruct Hp as [Hp|Hp].
      {
        destruct Hp as [Hp1 Hp2]. inversion Hp1.
      }
      {
        destruct Hp as [Hp1 Hp2].
        rewrite lookup_insert_Some in Hnp'.
        rewrite lookup_insert_Some in Hnq'.
        destruct Hnp',Hnq'; destruct_and!; subst.
        {
          pose proof (Hsubp' := Hsubpg (patt_imp (patt_app p1 p2) (patt_app p1 p2)) np Hp2).
          simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
          contradict_not_cached Hdnglg Hgappp1p2 Hbocp1.
        }
        {
          pose proof (Hsubp' := Hsubpg (patt_imp (patt_app p1 p2) p4) np Hp2).
          simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
          contradict_not_cached Hdnglg Hgappp1p2 Hbocp1.
        }
        {
          pose proof (Hsubp' := Hsubpg (patt_imp p3 (patt_app p1 p2)) np Hp2).
          simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
          contradict_not_cached Hdnglg Hgappp1p2 Hbocp2.
        }
        {
          pose proof (Hinv' := IH2 (patt_imp p3 p4) np Hp2).
          simpl in Hinv'; apply Hinv'; assumption.
        }
      }
    + repeat case_match. subst. invert_tuples. simpl in *.
      intros np' nq' Hnp' Hnq'.
      app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp H.
      rewrite lookup_insert_Some in Hp.
      destruct Hp as [Hp|Hp].
      {
        destruct Hp as [Hp1 Hp2]. inversion Hp1.
      }
      {
        destruct Hp as [Hp1 Hp2].
        rewrite lookup_insert_Some in Hnp'.
        rewrite lookup_insert_Some in Hnq'.
        destruct Hnp',Hnq'; destruct_and!; subst.
        {
          pose proof (Hsubp' := Hsubpg (patt_exists (patt_app p1 p2)) np Hp2).
          simpl in Hsubp'.
          contradict_not_cached Hdnglg Hgappp1p2 Hsubp'.
        }
        {
          pose proof (Hsubp' := Hsubpg (patt_exists (patt_app p1 p2)) np Hp2).
          simpl in Hsubp'. 
          contradict_not_cached Hdnglg Hgappp1p2 Hsubp'.
        }
        {
          inversion H2.
        }
        {
          pose proof (Hinv' := IH2 _ np Hp2).
          simpl in Hinv'; apply Hinv'; assumption.
        }
      }
    + repeat case_match. subst. invert_tuples. simpl in *.
      intros np' nq' Hnp' Hnq'.
      app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp H.
      rewrite lookup_insert_Some in Hp.
      destruct Hp as [Hp|Hp].
      {
        destruct Hp as [Hp1 Hp2]. inversion Hp1.
      }
      {
        destruct Hp as [Hp1 Hp2].
        rewrite lookup_insert_Some in Hnp'.
        rewrite lookup_insert_Some in Hnq'.
        destruct Hnp',Hnq'; destruct_and!; subst.
        {
          pose proof (Hsubp' := Hsubpg (patt_mu (patt_app p1 p2)) np Hp2).
          simpl in Hsubp'.
          contradict_not_cached Hdnglg Hgappp1p2 Hsubp'.
        }
        {
          pose proof (Hsubp' := Hsubpg (patt_mu (patt_app p1 p2)) np Hp2).
          simpl in Hsubp'. 
          contradict_not_cached Hdnglg Hgappp1p2 Hsubp'.
        }
        {
          inversion H2.
        }
        {
          pose proof (Hinv' := IH2 _ np Hp2).
          simpl in Hinv'; apply Hinv'; assumption.
        }
      }
  - intros p np Hp.
    destruct p; try exact I.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_app_imp Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp.
    + solve_mu_ex Hsubp H Hdngl Heqo Hp. 
  - intros p np Hp.
  
    destruct p; try exact I.
    + repeat case_match. subst. invert_tuples. simpl in *.
    intros np' nq' Hnp' Hnq'.
    app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp H.
    (** end of preparation phase. **)

    rewrite lookup_insert_Some in Hp.
    destruct Hp as [Hp|Hp].
    {
      destruct Hp as [Hp1 Hp2]. inversion Hp1.
    }
    {
      destruct Hp as [Hp1 Hp2].
      rewrite lookup_insert_Some in Hnp'.
      rewrite lookup_insert_Some in Hnq'.
      destruct Hnp',Hnq'; destruct_and!; subst.
      {
        pose proof (Hsubp' := Hsubpg (patt_app (patt_imp p1 p2) (patt_imp p1 p2)) np Hp2).
        simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
        contradict_not_cached Hdnglg Hgappp1p2 Hbocp1.
      }
      {
        pose proof (Hsubp' := Hsubpg (patt_app (patt_imp p1 p2) p4) np Hp2).
        simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
        contradict_not_cached Hdnglg Hgappp1p2 Hbocp1.
      }
      {
        pose proof (Hsubp' := Hsubpg (patt_app p3 (patt_imp p1 p2)) np Hp2).
        simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
        contradict_not_cached Hdnglg Hgappp1p2 Hbocp2.
      }
      {
        pose proof (Hinv' := IH2 (patt_app p3 p4) np Hp2).
        simpl in Hinv'; apply Hinv'; assumption.
      }
    }
  + repeat case_match. subst. invert_tuples. simpl in *.
    intros np' nq' Hnp' Hnq'.
    app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp H.
    (** end of preparation phase. **)

    rewrite lookup_insert_Some in Hp.
    destruct Hp as [Hp|Hp].
    {
      destruct Hp as [Hp1 Hp2]. inversion Hp1.
      subst. clear Hp1.
      rewrite lookup_insert_ne in Hnp'.
      { apply imp_neq1. }
      rewrite lookup_insert_ne in Hnq'.
      { apply imp_neq2. }
      congruence.
    }
    {
      destruct Hp as [Hp1 Hp2].
      rewrite lookup_insert_Some in Hnp'.
      rewrite lookup_insert_Some in Hnq'.
      destruct Hnp',Hnq'; destruct_and!; subst.
      {
        pose proof (Hsubp' := Hsubpg (patt_imp (patt_imp p1 p2) (patt_imp p1 p2)) np Hp2).
        simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
        contradict_not_cached Hdnglg Hgappp1p2 Hbocp1.
      }
      {
        pose proof (Hsubp' := Hsubpg (patt_imp (patt_imp p1 p2) p4) np Hp2).
        simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
        contradict_not_cached Hdnglg Hgappp1p2 Hbocp1.
      }
      {
        pose proof (Hsubp' := Hsubpg (patt_imp p3 (patt_imp p1 p2)) np Hp2).
        simpl in Hsubp'. destruct Hsubp' as [Hbocp1 Hbocp2].
        contradict_not_cached Hdnglg Hgappp1p2 Hbocp2.
      }
      {
        pose proof (Hinv' := IH2 (patt_imp p3 p4) np Hp2).
        simpl in Hinv'; apply Hinv'; assumption.
      }
    }
  + repeat case_match. subst. invert_tuples. simpl in *.
    intros np' nq' Hnp' Hnq'.
    app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp H.
    rewrite lookup_insert_Some in Hp.
    destruct Hp as [Hp|Hp].
    {
      destruct Hp as [Hp1 Hp2]. inversion Hp1.
    }
    {
      destruct Hp as [Hp1 Hp2].
      rewrite lookup_insert_Some in Hnp'.
      rewrite lookup_insert_Some in Hnq'.
      destruct Hnp',Hnq'; destruct_and!; subst.
      {
        pose proof (Hsubp' := Hsubpg (patt_exists (patt_imp p1 p2)) np Hp2).
        simpl in Hsubp'.
        contradict_not_cached Hdnglg Hgappp1p2 Hsubp'.
      }
      {
        pose proof (Hsubp' := Hsubpg (patt_exists (patt_imp p1 p2)) np Hp2).
        simpl in Hsubp'. 
        contradict_not_cached Hdnglg Hgappp1p2 Hsubp'.
      }
      {
        inversion H2.
      }
      {
        pose proof (Hinv' := IH2 _ np Hp2).
        simpl in Hinv'; apply Hinv'; assumption.
      }
    }
  + repeat case_match. subst. invert_tuples. simpl in *.
    intros np' nq' Hnp' Hnq'.
    app_imp_prepare Heqo IHp1 IHp2 Hdngl Heqp1 Heqp2 Hcont Hsubp H.
    rewrite lookup_insert_Some in Hp.
    destruct Hp as [Hp|Hp].
    {
      destruct Hp as [Hp1 Hp2]. inversion Hp1.
    }
    {
      destruct Hp as [Hp1 Hp2].
      rewrite lookup_insert_Some in Hnp'.
      rewrite lookup_insert_Some in Hnq'.
      destruct Hnp',Hnq'; destruct_and!; subst.
      {
        pose proof (Hsubp' := Hsubpg (patt_mu (patt_imp p1 p2)) np Hp2).
        simpl in Hsubp'.
        contradict_not_cached Hdnglg Hgappp1p2 Hsubp'.
      }
      {
        pose proof (Hsubp' := Hsubpg (patt_mu (patt_imp p1 p2)) np Hp2).
        simpl in Hsubp'. 
        contradict_not_cached Hdnglg Hgappp1p2 Hsubp'.
      }
      {
        inversion H2.
      }
      {
        pose proof (Hinv' := IH2 _ np Hp2).
        simpl in Hinv'; apply Hinv'; assumption.
      }
    }
  - 
  (*
  Local Ltac ex_mu_prepare Heqo IHp1 Hdngl Heqp1 Hcont Hsubp Hinvsub :=
  lazymatch type of Heqo with
  | (?C !! ?ex_or_mu = None) => (
    lazymatch type of Heqp1 with
    | (to_NamedPattern2' ?p1 ?C ?evs ?svs = (?n0, ?g0, ?e0, ?s0)) => (
        assert (HdngCp1: dangling_vars_cached C p1);
        [(eapply dangling_vars_cached_imp_proj1; apply Hdngl)|];
        assert (Hsubpg0: sub_prop g0);
        [(
          epose proof (Htmp := sub_prop_step _ _ _ _);
          erewrite Heqp1 in Htmp; simpl in Htmp;
          specialize (Htmp HdngCp1 Hcont Hsubp);
          exact Htmp
        )|];
        assert (Hcontg0: cache_continuous_prop g0);
        [(
          epose proof (Htmp := cache_continuous_step _ _ _ _);
          erewrite Heqp1 in Htmp; simpl in Htmp;
          specialize (Htmp HdngCp1 Hcont);
          exact Htmp
        )|];
        assert (HCsubg0: C ⊆ g0);
        [(
          epose proof (Htmp := to_NamedPattern2'_extends_cache _ _ _ _);
          erewrite Heqp1 in Htmp; simpl in Htmp;
          exact Htmp
        )|];
        assert (Hdnglg0: dangling_vars_cached g0 ex_or_mu);
        [(
          eapply dangling_vars_subcache;
          [apply Hdngl
          |exact HCsubg0
          ]
        )|];
        epose proof (IH1 := IHp1 _ _ _);
        erewrite Heqp1 in IH1; simpl in IH1;
        specialize (IH1 Hsubp Hcont HdngCp1 Hinvsub);
        clear IHp1;
        assert (Hg0p1n0: g0 !! p1 = Some n0);
        [(
          epose proof (Htmp := to_NamedPattern2'_ensures_present _ _ _ _);
          erewrite Heqp1 in Htmp; simpl in Htmp;
          exact Htmp
        )|];
        assert(Hg0appp1p2: g0 !! ex_or_mu = None);
        [(
          let Hg0app := fresh "Hg0app" in
          destruct (g0 !! ex_or_mu) eqn:Hg0app;[exfalso|reflexivity];
          pose proof (Htmp := onlyAddsSubpatterns2 C p1 evs svs ex_or_mu Heqo);
          feed specialize Htmp;
          [(
            eexists; erewrite Heqp1; simpl; apply Hg0app
          )|];
          (eapply not_is_subformula_of_ex + eapply not_is_subformula_of_mu); apply Htmp
        )|]
    )end)
  end.*)
  intros p0 np0 Hp0.
    destruct p0; try exact I.
    + repeat case_match. subst. invert_tuples. simpl in *.
      intros np' nq' Hnp' Hnq'.
      (*ex_mu_prepare Heqo IHp Hdngl Heqp3 Hcont Hsubp H.*)
      
      epose proof (IH := IHp _ _ _).
      erewrite Heqp3 in IH. simpl in IH.
      feed specialize IH.
      {
        apply sub_prop_shift_e. exact Hsubp.
      }
      {
        apply cache_continuous_shift_e. exact Hcont.
      }
      {
        apply dangling_vars_cached_shift_e. apply Hdngl.
      }
      {
        apply inv_sub_prop_shift_e.
      }
      
      rewrite lookup_insert_ne in Hp0.
      { discriminate. }

Qed.*)

  Lemma consistency_pqp
        (p q : Pattern)
        (np' nq' np'' : NamedPattern)
        (cache : Cache)
        (evs : EVarSet)
        (svs : SVarSet):
    CES_prop cache evs svs ->
    History_generator cache evs svs ->
    sub_prop cache ->
    inv_sub_prop cache ->
    dangling_vars_cached cache (patt_imp p (patt_imp q p)) ->
      exists np nq,
        (to_NamedPattern2' (patt_imp p (patt_imp q p)) cache evs svs).1.1.1
    = npatt_imp np (npatt_imp nq np).
  Proof.
    intros HCES Hhist Hsubp Hisp Hdngcached.
    remember ((to_NamedPattern2' (patt_imp p (patt_imp q p)) cache evs svs)) as Call.
    simpl in HeqCall.
    destruct (cache !! patt_imp p (patt_imp q p)) eqn:Hcachepqp.
    {
      rewrite Hcachepqp in HeqCall. rewrite HeqCall. simpl. rename n into npqp.
      pose proof (Hcall2 := cached_p_impl_called_with_p cache evs svs Hhist).
      specialize (Hcall2 (patt_imp p (patt_imp q p)) npqp HCES ltac:(simpl; auto) Hcachepqp).
      destruct Hcall2 as [C' [evs' [svs' [Hhist' [HC'notcached [Hsubseteq1 [HCES' [Hccp' [Hsp' [Hdng' HeqCall1]]]]]]]]]].
      rewrite -HeqCall1. simpl. rewrite HC'notcached.
      repeat case_match; invert_tuples; simpl in *.
      {
        pose proof (Heqo' := Heqo).
        apply cached_p_impl_called_with_p with (evs := e1) (svs := s) in Heqo.
        4: { simpl. auto. }
        3: { pose proof (Htmp := CES_prop_step p C' evs' svs' HCES').
          do 3 case_match_in_hyp Htmp. invert_tuples.
          exact Htmp.
        }
        2: {
          pose proof (Htmp := history_generator_step C' p evs' svs' Hhist').
          rewrite Heqp1 in Htmp.
          apply Htmp.
          5: {
            apply dangling_vars_cached_imp_proj1 in Hdng'. exact Hdng'.
          }
          4: { exact Hsp'. }
          3: { exact Hccp'. }
          2: { exact HCES'. }
          1: {
            (* TODO extract a lemma *)
            destruct Hhist' as [Hst_history' Hst_prop'].
            destruct Hst_history'.
            {
              simpl. right. split;[reflexivity|].
              simpl in Hst_prop'. subst C'.
              specialize (HCES' erefl).
              destruct HCES' as [Hevs' Hsvs']. subst.
              repeat split; reflexivity.
            }
            {
              left. simpl. simpl in Hst_prop'.
              destruct Hst_prop' as [HC' [Hevs' [Hsvs' Hst_prop']]].
              subst. repeat split; reflexivity.
            }
          }
        }
        destruct Heqo as [C'' [evs'' [svs'' [hg'' [HC''qp [Hsubseteq'' [HCES'' [Hccp'' [Hsp'' [Hdng'' Hcall'']]]]]]]]]].
        rewrite -Hcall''.
        simpl. rewrite HC''qp.


        (*clear Hcachepqp.*)
        repeat case_match; subst; invert_tuples; simpl; simpl in Heqo';
        repeat case_match; subst; invert_tuples; simpl in *.
        {
          rewrite HC''qp in Heqo0. inversion Heqo0.
        }
        {
          rewrite HC'notcached in Heqo. inversion Heqo.
        }
        {
          rewrite HC''qp in Heqo1. inversion Heqo1.
        }
        {
          rewrite Heqp14 in Heqp7. inversion Heqp7. subst. clear Heqp7.
          rewrite Heqo0 in Heqo'. inversion Heqo'. subst. clear Heqo'.
          clear HC''qp. (*duplicate of Heqo.*)
          pose proof (H' := Hsubp (patt_imp p (patt_imp q p)) (npatt_imp n (npatt_imp n5 n2)) Hcachepqp).
          simpl in H'.
          destruct H' as [Hbocp Hbocqp].
          destruct Hbocqp as [Hbqp|Hcqp].
          {
            simpl in Hbqp. inversion Hbqp.
          }
          destruct Hcqp as [nqp Hnqp].
          assert (Hnp1: exists np1, cache !! p = Some np1).
          {
            apply cached_anyway.
            {
              eapply dangling_vars_cached_imp_proj1.
              eassumption.
            }
            assumption.
          }
          assert (Hbocq: bound_or_cached cache q).
          {
            pose proof (Htmp := Hsubp (patt_imp q p) nqp Hnqp).
            simpl in Htmp.
            destruct Htmp as [Hbocq _].
            exact Hbocq.
          }
          assert (Hnq1: exists nq1, cache !! q = Some nq1).
          {
            apply cached_anyway.
            {
              eapply dangling_vars_cached_imp_proj1.
              eapply dangling_vars_cached_imp_proj2.
              eassumption.
            }
            assumption.
          }

          destruct Hnp1 as [np1 Hnp1].
          destruct Hnq1 as [nq1 Hnq1].

          destruct (decide (is_bound_var p)) as [Hboundp|Hnboundp].
          {
            assert (Hpcached: dangling_vars_cached cache p).
            {
              apply dangling_vars_cached_imp_proj1 in Hdngcached.
              exact Hdngcached.
            }
            unfold dangling_vars_cached in Hpcached.
            destruct Hpcached as [Hpcachede Hpcacheds].
            unfold dangling_evars_cached in Hpcachede.
          }
          pose proof (H := Hisp (patt_imp p (patt_imp q p)) (npatt_imp n (npatt_imp n5 n2)) Hcachepqp).
          simpl in H.
          pose proof (Htmp := H _ _ Hnp1 Hnqp).
          inversion Htmp; subst. clear Htmp.
          clear H.

          
          pose proof (H := Hisp (patt_imp q p) (npatt_imp n5 n2) Hnqp).
          simpl in H.
          pose proof (Htmp := H  _ _ Hnq1 Hnp1).
          inversion Htmp. subst. clear Htmp.
          exists np1, nq1.
          reflexivity.
      }
      {
        rewrite HC''qp in Heqo1. inversion Heqo1.
      }
      {
        rewrite Heqp7 in Heqp23. inversion Heqp23. subst. clear Heqp23.
        rewrite Heqo0 in Heqo'. inversion Heqo'.
      }
    }
    {
      case_match; simpl in *.
      {
        rewrite Heqo0 in HC'notcached. inversion HC'notcached.
      }
      {
        assert (Hgp: g !! p = Some n).
        {
          epose proof (Hensures := to_NamedPattern2'_ensures_present _ _ _ _).
          erewrite Heqp1 in Hensures. simpl in Hensures.
          exact Hensures.
        }
        assert (Hg2p: g2 !! p = Some n).
        {
          epose proof (Htmp := to_NamedPattern2'_extends_cache _ _ _ _).
          erewrite Heqp10 in Htmp. simpl in Htmp.
          eapply lookup_weaken. exact Hgp. exact Htmp.
        }
        epose proof (Htmp := to_NamedPattern2'_lookup _ _ _ _ _ Hg2p).
        erewrite Heqp13 in Htmp. inversion Htmp. subst. clear Htmp.
        exists n,n2. reflexivity.
      }
    }


  
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
