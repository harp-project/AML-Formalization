From MatchingLogic Require Import Logic.
From MatchingLogic.Evaluation Require Import
  Firstorder
  Complex
  Propositional
  Rewrite
  Revert_size.

Extraction Language Haskell.

From Coq Require Extraction.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellString.
(* Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellNatNum.
Require Import ExtrHaskellNatInt. *)

Fixpoint proof_size {Σ : Signature} {φ : Pattern} {Γ}
   (pf : ML_proof_system Γ φ) : nat :=
match pf with
 | Modus_ponens _ phi1 phi2 x x0 => 1 + proof_size x + proof_size x0
 | ProofSystem.Ex_gen _ phi1 phi2 x x0 x1 x2 x3 => 1 + proof_size x2
 | ProofSystem.Framing_left _ phi1 phi2 psi x x0 => 1 + proof_size x0
 | ProofSystem.Framing_right _ phi1 phi2 psi x x0 => 1 + proof_size x0
 | ProofSystem.Svar_subst _ phi psi X x x0 x1 => 1 + proof_size x1
 | ProofSystem.Knaster_tarski _ phi psi x x0 => 1 + proof_size x0
 | ProofSystem.Existence _ => 1
 | _ => 1
end.

Definition proof_size_info {Σ : Signature} {φ Γ i} (pf : derives_using Γ φ i) : nat :=
match pf with
 | exist _ x x0 => proof_size x
end.

Definition proof_prop_low : nat := proof_size_info proof1_low.
Definition proof_prop_pm1 : nat := proof_size_info proof1_pm.
Definition proof_prop_pm2 : nat := proof_size_info proof1_pm2.

Definition proof_rew_low : nat := proof_size_info proof2_low.
Definition proof_rew_pm1 : nat := proof_size_info proof2_pm.
Definition proof_rew_pm2 : nat := proof_size_info proof2_pm2.
Definition proof_rew_pm3 : nat := proof_size_info proof2_pm3.

Definition proof_fol_low : nat := proof_size_info proof3_low.
Definition proof_fol_pm1 : nat := proof_size_info proof3_fol_pm.
Definition proof_fol_pm2 : nat := proof_size_info proof3_pm.

Definition proof_derived_rev_small : nat := proof_size_info private_test_revert_1.
Definition proof_pm_rev_small : nat := proof_size_info private_test_revert_2.
Definition proof_derived_rev_big : nat := proof_size_info private_test_revert_3.
Definition proof_pm_rev_big : nat := proof_size_info private_test_revert_4.

Definition proof_complex_low : nat := proof_size_info proof_running_low.
Definition proof_complex_pm : nat := proof_size_info proof_running_pm.

Extraction "Test.hs" proof_prop_low proof_prop_pm1 proof_prop_pm2
                     proof_rew_low proof_rew_pm1 proof_rew_pm2 proof_rew_pm3
                     proof_fol_low proof_fol_pm1 proof_fol_pm2
                     proof_derived_rev_small proof_pm_rev_small
                     proof_derived_rev_big proof_pm_rev_big
                     proof_complex_low proof_complex_pm.
