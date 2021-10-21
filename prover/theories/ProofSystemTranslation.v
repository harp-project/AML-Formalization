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
  Check hypothesis.
  Equations translation (G : Theory) (phi : Pattern) (prf : G ⊢ phi)
    : (NP_ML_proof_system (theory_translation G) (to_NamedPattern2 phi)) by struct prf :=
    translation G phi (hypothesis wfa inG)
    := N_hypothesis (theory_translation G) (to_NamedPattern2 phi) _ _ ;
    translation _ _ _ := _.

End proof_system_translation.
