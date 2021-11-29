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
      | patt_bott => True
      | patt_imp p' q' => exists np' nq', C !! p' = Some np' /\ C !! q' = Some nq'
      | _ => True
      end.

  Lemma sub_prop_empty: sub_prop ∅.
  Proof.
    unfold sub_prop; intros; inversion H.
  Qed.

  Lemma sub_prop_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet):
    sub_prop C ->
    sub_prop (to_NamedPattern2' p C evs svs).1.1.2.
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
  Definition history_generator (C : Cache) :=
    forall (p : @Pattern signature) (np : @NamedPattern signature),
      C !! p = Some np ->
      { history : list (@Pattern signature * ((@NamedPattern signature) * Cache * (@EVarSet signature) * (@SVarSet signature)))
                  &
                    match history with
                    | [] => False
                    | (x::xs) =>
                        x.1 = p /\ x.2.1.1.1 = np /\
(*                        x.2.1.1.2 !! p = None /\ *)
                          (match (last (x::xs)) with
                          | None => False
                          | Some (p_l, x_l) => x_l = (to_NamedPattern2' p_l ∅ ∅ ∅)
                          end) /\
                          forall (i:nat),
                            match xs!!i with
                            | None => True
                            | Some (p_Si, (np_Si, c_Si, evs_Si, svs_Si)) =>
                                exists p_i,
                                c_Si !! p_i = None /\
                                ((x::xs)!!i) = Some (p_i,(to_NamedPattern2' p_i c_Si evs_Si svs_Si))
                            end
                    end
      }.

  Lemma history_generator_subseteq (C₁ C₂ : Cache) :
    C₁ ⊆ C₂ ->
    history_generator C₂ ->
    history_generator C₁.
  Proof.
    intros Hsub Hc.
    unfold history_generator in *.
    intros p np Hp.
    specialize (Hc p np).
    feed specialize Hc.
    { eapply lookup_weaken. 2: apply Hsub. apply Hp. }
    exact Hc.
  Defined. (* I think this should not be opaque. *)
  
  Lemma history_generator_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet):
    history_generator C ->
    history_generator (to_NamedPattern2' p C evs svs).1.1.2.
  Proof.
    intros cpC.
    move: C evs svs cpC.
    induction p; intros C evs svs cpC; simpl; case_match.

    (* [p] was in cache -> the history function stays the same. Solves 10 subgoals *)
    all: try (solve[unfold history_generator; intros p' np' Hp'; simpl in Hp'; specialize (cpC p' np' Hp'); exact cpC]).
    (* 10 subgoals remain - the pattern p' was not found in cache. *)
    (* Base cases *)
    1,2,3,4,5,7: simpl; intros p' np' Hp';
    lazymatch type of Hp' with
    | (<[?q:=?nq]> _ !! p' = _ ) =>
        destruct (decide (p' = q));
        [(subst p'; rewrite lookup_insert in Hp'; inversion Hp'; clear Hp'; subst np';
          apply (existT [(q, (to_NamedPattern2' q ∅ ∅ ∅))]); simpl;
          split;[reflexivity|]; case_match;[inversion Heqo0|];
          split;[|auto];reflexivity
         )
        |(rewrite lookup_insert_ne in Hp';[(apply not_eq_sym; assumption)|idtac];
         unfold history_generator in cpC; specialize (cpC p' np' Hp'); apply cpC)
        ]
    end.

    (* Inductive cases *)
    - repeat case_match. subst.
      inversion Heqp. subst. clear Heqp.
      simpl.

      unfold history_generator. intros p' np' Hp'.
      
      
      destruct (decide (p' = patt_app p1 p2)).
      + subst p'.

        pose proof (Htmp := Heqp0).
        apply (f_equal fst) in Htmp.
        apply (f_equal fst) in Htmp.
        pose proof (Htmp' := Htmp).
        apply (f_equal fst) in Htmp.
        apply (f_equal snd) in Htmp'.
        assert (g !! p1 = Some n).
        { simpl in Htmp. simpl in Htmp'. rewrite -Htmp. rewrite -Htmp'.          
          apply to_NamedPattern2'_ensures_present.
        }
        clear Htmp Htmp'.
        pose proof (Htmp := Heqp1).
        apply (f_equal fst) in Htmp.
        apply (f_equal fst) in Htmp.
        pose proof (Htmp' := Htmp).
        apply (f_equal fst) in Htmp.
        apply (f_equal snd) in Htmp'.
        assert (g1 !! p2 = Some n0).
        { simpl in Htmp,Htmp'. rewrite -Htmp -Htmp'.
          apply to_NamedPattern2'_ensures_present.
        }
        clear Htmp Htmp'.

        pose proof (IH1 := IHp1 C evs svs cpC).
        rewrite Heqp0 in IH1. simpl in IH1.
        pose proof (IH2 := IHp2 g e s0 IH1).
        rewrite Heqp1 in IH2. simpl in IH2.


        unfold history_generator in IH2.
        pose proof (IH2' := IH2 p2 n0 H0).
        destruct IH2' as [hist Hhist].
        destruct hist as [|h hist];[inversion Hhist|].
        destruct_and!; subst.

        eapply (existT ((patt_app p1 h.1, (np', g1, e1, s))::h::hist)).
        split_and!; auto.
        intros i.
        destruct i.
        * simpl. clear H2. repeat case_match. simpl.
          exists (patt_app p1 p).
          simpl in *. subst.
          split. admit.
          repeat f_equal.
          case_match.
          Search c.
        * simpl. apply H5.
        
        admit.
      +
        pose proof (IH1 := IHp1 C evs svs cpC).
        rewrite Heqp0 in IH1. simpl in IH1.
        pose proof (IH2 := IHp2 g e s0 IH1).
        rewrite Heqp1 in IH2. simpl in IH2.
      
        unfold history_generator in IH2.
        specialize (IH2 p' np').
      
        rewrite lookup_insert_ne in Hp'.
        { apply not_eq_sym. assumption. }
        specialize (IH2 Hp').
        destruct IH2 as [hist Hhist].
        destruct hist as [| h hist] ;[inversion Hhist|].
        destruct_and!. subst.
        apply (existT (h::hist)).
        simpl. split_and!; auto; simpl.

      
      destruct (decide (p' = patt_app p1 p2)).
      + (subst p'; rewrite lookup_insert in Hp'; inversion Hp'; clear Hp'; subst np';
          apply (existT [(patt_app p1 p2, (to_NamedPattern2' (patt_app p1 p2) C evs svs))]); simpl; split;[reflexivity|]
        ).
        repeat case_match;(split;[|auto]); simpl.
        * inversion Heqo1.
        * inversion Heqo1.
        * inversion Heqo.
        * inversion Heqo.
        * inversion Heqo1.
        * inversion Heqo1.
        * inversion Heqp10; clear Heqp10; subst.
          inversion Heqp; clear Heqp; subst.
          inversion Heqp0; clear Heqp0; subst.
          rewrite Heqp1 in Heqp5. inversion Heqp5.
          reflexivity.
        * subst. inversion Heqp10; clear Heqp10; subst.
          inversion Heqp; clear Heqp; subst.
          inversion Heqp0; clear Heqp0; subst.
          rewrite Heqp1 in Heqp5. inversion Heqp5; clear Heqp5; subst.
          
          
        
      + (rewrite lookup_insert_ne in Hp';[(apply not_eq_sym; assumption)|idtac]).
        specialize (IHp1 C evs svs cpC).
        rewrite Heqp0 in IHp1. simpl in IHp1.
        specialize (IHp2 g e s0 IHp1).
        rewrite Heqp1 in IHp2. simpl in IHp2.
        specialize (IHp2 p' np' Hp'). apply IHp2.
    - repeat case_match. subst.
      inversion Heqp. subst. clear Heqp.
      simpl.
      unfold history_generator. intros p' np' Hp'.
      destruct (decide (p' = patt_imp p1 p2)).
      + (subst p'; rewrite lookup_insert in Hp'; inversion Hp'; clear Hp'; subst np';
          apply (existT [(patt_imp p1 p2, (to_NamedPattern2' (patt_imp p1 p2) ∅ ∅ ∅))]); simpl; split;[reflexivity|]
        ).
        repeat case_match;(split;[|auto]); reflexivity.
        
      + (rewrite lookup_insert_ne in Hp';[(apply not_eq_sym; assumption)|idtac]).
        specialize (IHp1 C evs svs cpC).
        rewrite Heqp0 in IHp1. simpl in IHp1.
        specialize (IHp2 g e s0 IHp1).
        rewrite Heqp1 in IHp2. simpl in IHp2.
        specialize (IHp2 p' np' Hp'). apply IHp2.
    - repeat case_match. subst.

      match type of Heqp1 with
      | (to_NamedPattern2' _ ?C ?evs ?svs = _) => specialize (IHp C evs svs)
      end.
      
      rewrite -> Heqp1 in IHp. simpl in IHp.
      feed specialize IHp.
      {
        unfold history_generator. intros p' np' Hp'.
        inversion Heqp0. subst. clear Heqp0.
        (* So what does the cache = ∅ mean here? 
           Recall that we start with empty cache when translating pattern.
           My intuition tells me that we behave here the same way as if we
           just started. In other words, history behaves as if we started from
           the nested existential and mu patterns.
         *)
        apply (existT [(p', (to_NamedPattern2' p' ∅ ∅ ∅))]).
        simpl. repeat split; auto.
      }
      unfold history_generator. intros p' np' Hp'.
      destruct (decide (p' = patt_exists p)).
      + (subst p'; rewrite lookup_insert in Hp'; inversion Hp'; clear Hp'; subst np';
          apply (existT [(patt_exists p, (to_NamedPattern2' (patt_exists p) ∅ ∅ ∅))]); simpl; split; auto
        ).
        
      +
        inversion Heqp0. subst. clear Heqp0.
        simpl in Hp'.
        destruct (decide (is_bound_evar p')).
        * apply (existT [(p', (to_NamedPattern2' p' ∅ ∅ ∅))]).
          simpl. repeat split; auto.
        * 
          unfold history_generator in IHp.
          specialize (IHp p' np').
          feed specialize IHp.
          {
            simpl in Hp'.
            rewrite lookup_insert_ne in Hp'. apply not_eq_sym. assumption.
            rewrite lookup_union_Some in Hp'.
            destruct Hp' as [Hp'|Hp'].
            -- unfold remove_bound_evars in Hp'.
               rewrite map_filter_lookup_Some in Hp'.
               destruct Hp' as [This _]. exact This.
            -- rewrite map_filter_lookup_Some in Hp'.
               destruct Hp' as [_ Hp'].
               unfold is_bound_evar_entry in Hp'. simpl in Hp'.
               contradiction.
            -- unfold remove_bound_evars,keep_bound_evars.
               intros x. unfold option_relation.
               repeat case_match; try exact I.
               rewrite map_filter_lookup_Some in Heqo0.
               rewrite map_filter_lookup_Some in Heqo1.
               destruct Heqo0 as [HH1 HH2].               
               destruct Heqo1 as [HH3 HH4].
               contradiction.
          }
          apply IHp.
    - repeat case_match. subst.

      match type of Heqp1 with
      | (to_NamedPattern2' _ ?C ?evs ?svs = _) => specialize (IHp C evs svs)
      end.
      
      rewrite -> Heqp1 in IHp. simpl in IHp.
      feed specialize IHp.
      {
        unfold history_generator. intros p' np' Hp'.
        inversion Heqp0. subst. clear Heqp0.
        (* So what does the cache = ∅ mean here? 
           Recall that we start with empty cache when translating pattern.
           My intuition tells me that we behave here the same way as if we
           just started. In other words, history behaves as if we started from
           the nested existential and mu patterns.
         *)
        apply (existT [(p', (to_NamedPattern2' p' ∅ ∅ ∅))]).
        simpl. repeat split; auto.
      }
      unfold history_generator. intros p' np' Hp'.
      destruct (decide (p' = patt_mu p)).
      + (subst p'; rewrite lookup_insert in Hp'; inversion Hp'; clear Hp'; subst np';
          apply (existT [(patt_mu p, (to_NamedPattern2' (patt_mu p) ∅ ∅ ∅))]); simpl; split; auto
        ).
      +
        inversion Heqp0. subst. clear Heqp0.
        simpl in Hp'.
        destruct (decide (is_bound_svar p')).
        * apply (existT [(p', (to_NamedPattern2' p' ∅ ∅ ∅))]).
          simpl. repeat split; auto.
        * 
          unfold history_generator in IHp.
          specialize (IHp p' np').
          feed specialize IHp.
          {
            simpl in Hp'.
            rewrite lookup_insert_ne in Hp'. apply not_eq_sym. assumption.
            rewrite lookup_union_Some in Hp'.
            destruct Hp' as [Hp'|Hp'].
            -- unfold remove_bound_evars in Hp'.
               rewrite map_filter_lookup_Some in Hp'.
               destruct Hp' as [This _]. exact This.
            -- rewrite map_filter_lookup_Some in Hp'.
               destruct Hp' as [_ Hp'].
               unfold is_bound_svar_entry in Hp'. simpl in Hp'.
               contradiction.
            -- unfold remove_bound_svars,keep_bound_svars.
               intros x. unfold option_relation.
               repeat case_match; try exact I.
               rewrite map_filter_lookup_Some in Heqo0.
               rewrite map_filter_lookup_Some in Heqo1.
               destruct Heqo0 as [HH1 HH2].               
               destruct Heqo1 as [HH3 HH4].
               contradiction.
          }
          apply IHp.
  Defined.

  Lemma consistency_pqp
        (p q : Pattern)
        (np' nq' np'' : NamedPattern)
        (cache : Cache)
        (evs : EVarSet)
        (svs : SVarSet):
    history_generator cache ->
    (to_NamedPattern2' (patt_imp p (patt_imp q p)) cache evs svs).1.1.1
    = npatt_imp np' (npatt_imp nq' np'') ->
    np'' = np'.
  Proof.
    intros Hg H. Search to_NamedPattern2'.
    remember (patt_imp p (patt_imp q p)) as pqp.
    pose proof (Hpresent := to_NamedPattern2'_ensures_present pqp cache evs svs).
    rewrite H in Hpresent.
    match type of H with
    | (?e.1.1.1 = _) => remember e as Call
    end.
    remember (Call.1.1.2) as cache'.
    
    pose proof (Hg' := history_generator_step cache pqp evs svs Hg).
    rewrite -HeqCall in Hg'. rewrite -Heqcache' in Hg'.
    apply Hg' in Hpresent.
    destruct Hpresent as [history Hhistory].
    destruct history;[inversion Hhistory|].
    
    induction history; simpl in *.
    - subst. clear Hg'. simpl in *.
      case_match.
      + simpl in *. subst.
    
    simpl in H.
    case_match.
    - admit.
    - (* cache miss on p ---> (q ---> p) *)
      repeat case_match; simpl in *; subst.
      + (* cache hit on q ---> p *)
        inversion Heqp0. subst. clear Heqp0.
        inversion Heqp6. subst. clear Heqp6.

        (* assert(cache !! patt_imp q p = Some (npatt_imp nq' np'')). *)
        
        (* Now [q ---> p] is in [g]. But it follows that [q ---> p] is also in [cache] (and has the same value).
           Therefore, also [p] and [q] are in [cache].
           It follows that [np' = cache !!! p].
           By monotonicity (Lemma ???), ???
         *)
        simpl.
        Check history_generator_step. About history_generator_step.
        pose proof (Hcorr_g := history_generator_step cache p evs svs Hcorr_cache).
        rewrite Heqp3 in Hcorr_g. simpl in Hcorr_g.
        (* pose proof (Hcorr_g _ _ Heqo0).
        destruct X as [[[cache' evs'] svs'] [Hnone [H Hsub]]]. simpl in H.
        rewrite Hnone in H. repeat case_match.
        simpl in *. inversion Heqp0. subst. clear Heqp0.
        inversion H1. subst. clear H1. *)

        (* Now compare Heqp3 with Heqp7 *)
        
  Abort.
  
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
  Check False_rect. Check eq_refl.
  Obligation Tactic := idtac.
  Equations? translation' (G : Theory) (phi : Pattern) (prf : G ⊢ phi)
           (cache : Cache) (pfsub : sub_prop cache) (pfcorr : history_generator cache)
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
