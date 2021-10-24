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

  Definition PfCache (G : NamedTheory)
    := gmap Pattern { p : NamedPattern & NP_ML_proof_system G p }.

  Definition to_NPCache (G : NamedTheory) (C : PfCache G) : gmap Pattern NamedPattern :=
    fmap (@projT1 NamedPattern (fun np => NP_ML_proof_system G np)) C.
    

  Check False_rect.
  Equations? translation' (G : Theory) (phi : Pattern) (prf : G ⊢ phi)
           (pfcache : PfCache (theory_translation G))
           (used_evars : EVarSet) (used_svars : SVarSet)
    : (NP_ML_proof_system (theory_translation G)
                          (to_NamedPattern2' phi (to_NPCache (theory_translation G) pfcache)
                                             used_evars used_svars).1.1.1
       * (PfCache (theory_translation G)) * EVarSet * SVarSet)%type by struct prf :=
    translation' G phi (hypothesis wfa inG) _ _ _
      := let: tn := to_NamedPattern2' phi (to_NPCache _ pfcache) used_evars used_svars in
         let: (_, cache', used_evars', used_svars') := tn in
         let: named_prf := N_hypothesis (theory_translation G) tn.1.1.1 _ _ in
         (named_prf, pfcache, used_evars', used_svars') ;

    translation' G phi (P1 psi wfphi wfpsi) _ _ _
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
    translation' _ _ _ _ _ _ := _.

  Proof.
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
