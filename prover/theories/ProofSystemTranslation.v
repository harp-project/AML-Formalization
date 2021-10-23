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

  Equations? translation (G : Theory) (phi : Pattern) (prf : G ⊢ phi)
    : (NP_ML_proof_system (theory_translation G) (to_NamedPattern2 phi)) by struct prf :=
    translation G phi (hypothesis wfa inG)
      := N_hypothesis (theory_translation G)
                      (to_NamedPattern2 phi)
                      (well_formed_translation phi wfa) _ ;
    translation G phi (P1 psi wfphi wfpsi)
      := eq_rect _ _
                 (N_P1 (theory_translation G)
                       (to_NamedPattern2 phi0)
                       (to_NamedPattern2 psi)
                       (well_formed_translation phi0 wfphi)
                       (well_formed_translation psi wfpsi))
                 _ _ ;
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
    translation _ _ _ := _.

  Proof.
  Abort.

End proof_system_translation.
