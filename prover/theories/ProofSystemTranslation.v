From Coq Require Import ssreflect.

From Coq Require Import Strings.String.
From Equations Require Import Equations.

From stdpp Require Export base.
From MatchingLogic Require Import Syntax Semantics SignatureHelper ProofSystem Helpers.FOL_helpers.
From MatchingLogicProver Require Import Named NamedProofSystem.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset.

Import ProofSystem.Notations.

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

  Lemma named_pattern_imp (phi psi : Pattern) :
    npatt_imp (to_NamedPattern2 phi) (to_NamedPattern2 psi) =
    to_NamedPattern2 (patt_imp phi psi).
  Proof.
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
  Admitted.

  Lemma sub_prop_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet):
    sub_prop C ->
    sub_prop (to_NamedPattern2' p C evs svs).1.1.2.
  Admitted.
    

  About to_NamedPattern2'.
  (* A correspondence property of the cache: any named pattern it contains is a translation
     of the locally nameless pattern that is its key, under some unspecified parameters.
     This should ensure that the named pattern has the same structure as the key. *)
  Definition corr_prop (C : Cache) :=
    forall (p : Pattern) (np : NamedPattern),
      C !! p = Some np ->
      exists cache evs svs,
        cache !! p = None /\
        np = (to_NamedPattern2' p cache evs svs).1.1.1. (* and cache \subseteq C *)

  Lemma corr_prop_empty: corr_prop ∅.
  Admitted.

  Lemma corr_prop_step (C : Cache) (p : Pattern) (evs : EVarSet) (svs : SVarSet):
    corr_prop C ->
    corr_prop (to_NamedPattern2' p C evs svs).1.1.2.
  Admitted.
  

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
  

  Lemma consistency_pqp
        (p q : Pattern)
        (np' nq' np'' : NamedPattern)
        (cache : Cache)
        (evs : EVarSet)
        (svs : SVarSet):
    corr_prop cache ->
    (to_NamedPattern2' (patt_imp p (patt_imp q p)) cache evs svs).1.1.1
    = npatt_imp np' (npatt_imp nq' np'') ->
    np'' = np'.
  Proof.
    intros Hcorr_cache H.
    simpl in H.
    case_match.
    - admit.
    - (* cache miss on p ---> (q ---> p) *)
      repeat case_match; simpl in *; subst.
      + (* cache hit on q ---> p *)
        inversion Heqp0. subst. clear Heqp0.
        inversion Heqp6. subst. clear Heqp6.

        assert(cache !! patt_imp q p = Some (npatt_imp nq' np'')).
        {
          
        }
        
        
        (* Now [q ---> p] is in [g]. But it follows that [q ---> p] is also in [cache] (and has the same value).
           Therefore, also [p] and [q] are in [cache].
           It follows that [np' = cache !!! p].
           By monotonicity (Lemma ???), ???
         *)
        simpl.
        Check corr_prop_step. About corr_prop_step.
        pose proof (Hcorr_g := corr_prop_step cache p evs svs Hcorr_cache).
        rewrite Heqp3 in Hcorr_g. simpl in Hcorr_g.
        pose proof (Hcorr_g _ _ Heqo0) as [cache' [evs' [svs' [Hnone H]]]].
        simpl in H. rewrite Hnone in H. repeat case_match.
        simpl in *. inversion Heqp0. subst. clear Heqp0.
        inversion H1. subst. clear H1.

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
  
Print NamedPattern.
  Equations? translation' (G : Theory) (phi : Pattern) (prf : G ⊢ phi)
           (cache : Cache) (pfsub : sub_prop cache) (pfcorr : corr_prop cache)
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
      | Some pqp_named with pqp_named => {
          | npatt_imp p' (npatt_imp q' p'')
          := _ ;
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
        | Some qp_named := _ (* TODO *)
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
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
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
