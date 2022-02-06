From Coq Require Import ssreflect.
From Coq Require Extraction extraction.ExtrHaskellString.

From Coq Require Import Strings.String.
From Equations Require Import Equations.

From stdpp Require Export base.
From MatchingLogic Require Import Syntax SignatureHelper ProofSystem ProofMode.
From MatchingLogicProver Require Import MMProofExtractor Named.

From stdpp Require Import base finite gmap mapset listset_nodup numbers propset.

Section named_proof_system.

  Context {signature : Signature}.

  Definition NamedTheory := propset NamedPattern.
  
  Reserved Notation "theory ⊢N pattern" (at level 76).
  Inductive NP_ML_proof_system (theory : NamedTheory) :
    NamedPattern -> Set :=

  (* Hypothesis *)
  | N_hypothesis (axiom : NamedPattern) :
      named_well_formed axiom ->
      axiom ∈ theory -> theory ⊢N axiom
                                              
  (* FOL reasoning *)
  (* Propositional tautology *)
  | N_P1 (phi psi : NamedPattern) :
      named_well_formed phi -> named_well_formed psi ->
      theory ⊢N npatt_imp phi (npatt_imp psi phi)
  | N_P2 (phi psi xi : NamedPattern) :
      named_well_formed phi -> named_well_formed psi -> named_well_formed xi ->
      theory ⊢N npatt_imp (npatt_imp phi (npatt_imp psi xi))
                          (npatt_imp (npatt_imp phi psi) (npatt_imp phi xi))
  | N_P3 (phi : NamedPattern) :
      named_well_formed phi ->
      theory ⊢N npatt_imp (npatt_imp (npatt_imp phi npatt_bott) npatt_bott) phi

  (* Modus ponens *)
  | N_Modus_ponens (phi1 phi2 : NamedPattern) :
      named_well_formed phi1 -> named_well_formed (npatt_imp phi1 phi2) ->
      theory ⊢N phi1 ->
      theory ⊢N npatt_imp phi1 phi2 ->
      theory ⊢N phi2

  (* Existential quantifier *)
  | N_Ex_quan (phi : NamedPattern) (x y : evar) :
      theory ⊢N npatt_imp (named_evar_subst phi (npatt_evar y) x) (npatt_exists x phi)

  (* Existential generalization *)
  | N_Ex_gen (phi1 phi2 : NamedPattern) (x : evar) :
      named_well_formed phi1 -> named_well_formed phi2 ->
      theory ⊢N npatt_imp phi1 phi2 ->
      x ∉ named_free_evars phi2 ->
      theory ⊢N npatt_imp (npatt_exists x phi1) phi2

  (* Frame reasoning *)
  (* Propagation bottom *)
  | N_Prop_bott_left (phi : NamedPattern) :
      named_well_formed phi ->
      theory ⊢N npatt_imp (npatt_app npatt_bott phi) npatt_bott

  | N_Prop_bott_right (phi : NamedPattern) :
      named_well_formed phi ->
      theory ⊢N npatt_imp (npatt_app phi npatt_bott) npatt_bott

  (* Propagation disjunction *)
  | N_Prop_disj_left (phi1 phi2 psi : NamedPattern) :
      named_well_formed phi1 -> named_well_formed phi2 -> named_well_formed psi ->
      theory ⊢N npatt_imp (npatt_app (npatt_or phi1 phi2) psi)
                          (npatt_or (npatt_app phi1 psi) (npatt_app phi2 psi))

  | N_Prop_disj_right (phi1 phi2 psi : NamedPattern) :
      named_well_formed phi1 -> named_well_formed phi2 -> named_well_formed psi ->
      theory ⊢N npatt_imp (npatt_app psi (npatt_or phi1 phi2))
                          (npatt_or (npatt_app psi phi1) (npatt_app psi phi2))

  (* Propagation exist *)
  | N_Prop_ex_left (phi psi : NamedPattern) (x : evar) :
      named_well_formed (npatt_exists x phi) -> named_well_formed psi ->
      x ∉ named_free_evars psi ->
      theory ⊢N npatt_imp (npatt_app (npatt_exists x phi) psi)
                          (npatt_exists x (npatt_app phi psi))

  | N_Prop_ex_right (phi psi : NamedPattern) (x : evar) :
      named_well_formed (npatt_exists x phi) -> named_well_formed psi ->
      x ∉ named_free_evars psi ->
      theory ⊢N npatt_imp (npatt_app psi (npatt_exists x phi))
                          (npatt_exists x (npatt_app psi phi))

  (* Framing *)
  | N_Framing_left (phi1 phi2 psi : NamedPattern) :
      theory ⊢N npatt_imp phi1 phi2 ->
      theory ⊢N npatt_imp (npatt_app phi1 psi) (npatt_app phi2 psi)

  | N_Framing_right (phi1 phi2 psi : NamedPattern) :
      theory ⊢N npatt_imp phi1 phi2 ->
      theory ⊢N npatt_imp (npatt_app psi phi1) (npatt_app psi phi2)

  (* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | N_Svar_subst (phi psi : NamedPattern) (X : svar) :
      named_well_formed phi -> named_well_formed psi ->
      theory ⊢N phi -> theory ⊢N named_svar_subst phi psi X

  (* Pre-Fixpoint *)
  | N_Pre_fixp (phi : NamedPattern) (X : svar) :
      theory ⊢N npatt_imp (named_svar_subst phi (npatt_mu X phi) X) (npatt_mu X phi)

  (* Knaster-Tarski *)
  | N_Knaster_tarski (phi psi : NamedPattern) (X : svar) :
      theory ⊢N npatt_imp (named_svar_subst phi psi X) psi ->
      theory ⊢N npatt_imp (npatt_mu X phi) psi

  (* Technical rules *)
  (* Existence *)
  | N_Existence (x : evar) :
      theory ⊢N npatt_exists x (npatt_evar x)

  (* Singleton *)
  | N_Singleton_ctx (C1 C2 : Named_Application_context) (phi : NamedPattern) (x : evar) : 
      theory ⊢N npatt_not (npatt_and
                             (named_subst_ctx C1 (npatt_and (npatt_evar x) phi))
                             (named_subst_ctx C2 (npatt_and (npatt_evar x) (npatt_not phi))))

  where "theory ⊢N pattern" := (NP_ML_proof_system theory pattern).

End named_proof_system.
