From stdpp Require Import base.
From MatchingLogic Require Import Syntax ProofSystem extralibrary.

Class VariablesMorphism (V₁ V₂ : MLVariables) := mkVariablesMorphism
{
  vm_evar : @evar V₁ -> @evar V₂ ;
  vm_svar : @svar V₁ -> @svar V₂ ;
}.

Class InjVariableMorphism (V₁ V₂ : MLVariables) (VM : VariablesMorphism V₁ V₂) := mkInjVariableMorphism
{
  ivm_evar :> Inj eq eq vm_evar ;
  ivm_svar :> Inj eq eq vm_evar ;
}.

Class SignatureMorphism (Σ₁ Σ₂ : Signature) := mkSignatureMorphism
{
  sm_vars :> VariablesMorphism (@variables Σ₁) (@variables Σ₂) ;
  sm_symbols : @symbols Σ₁ -> @symbols Σ₂ ;
}.

Class InjSignatureMorphism (Σ₁ Σ₂ : Signature) (SM : SignatureMorphism Σ₁ Σ₂) := mkInjSignatureMorphism
{
  ism_vars :> InjVariableMorphism (@variables Σ₁) (@variables Σ₂) (@sm_vars Σ₁ Σ₂ SM) ;
  ism_symbols :> Inj eq eq (@sm_symbols Σ₁ Σ₂ SM) ;
}.

Fixpoint SMϕ {Σ₁ Σ₂ : Signature} (SM : SignatureMorphism Σ₁ Σ₂) (ϕ : @Pattern Σ₁) : (@Pattern Σ₂) :=
  match ϕ with
  | patt_free_evar x
    => @patt_free_evar Σ₂ (vm_evar x)
  | patt_free_svar X
    => @patt_free_svar Σ₂ (vm_svar X)
  | patt_bound_evar n
    => @patt_bound_evar Σ₂ n
  | patt_bound_svar n
    => @patt_bound_svar Σ₂ n
  | patt_bott
    => @patt_bott Σ₂
  | patt_sym s
    => @patt_sym Σ₂ (sm_symbols s)
  | patt_imp ϕ₁ ϕ₂
    => @patt_imp Σ₂ (@SMϕ Σ₁ Σ₂ SM ϕ₁) (@SMϕ Σ₁ Σ₂ SM ϕ₂)
  | patt_app ϕ₁ ϕ₂
    => @patt_app Σ₂ (@SMϕ Σ₁ Σ₂ SM ϕ₁) (@SMϕ Σ₁ Σ₂ SM ϕ₂)
  | patt_exists ϕ'
    => @patt_exists Σ₂ (@SMϕ Σ₁ Σ₂ SM ϕ')
  | patt_mu ϕ'
    => @patt_mu Σ₂ (@SMϕ Σ₁ Σ₂ SM ϕ')
  end.

Definition SMΓ (Σ₁ Σ₂ : Signature) (SM : SignatureMorphism Σ₁ Σ₂) (Γ : @Theory Σ₁) : (@Theory Σ₂)
  := fmap (SMϕ SM) Γ.


Check @no_negative_occurrence_db_b.
Lemma SM_nno (Σ₁ Σ₂ : Signature) (SM : SignatureMorphism Σ₁ Σ₂) (ϕ : @Pattern Σ₁) (dbi : nat) :
  no_negative_occurrence_db_b dbi ϕ = true ->
  no_negative_occurrence_db_b dbi (SMϕ SM ϕ) = true
with SM_npo (Σ₁ Σ₂ : Signature) (SM : SignatureMorphism Σ₁ Σ₂) (ϕ : @Pattern Σ₁) (dbi : nat) :
  no_positive_occurrence_db_b dbi ϕ = true ->
  no_positive_occurrence_db_b dbi (SMϕ SM ϕ) = true.
Proof.
  - intros H.
    induction ϕ; simpl in *; auto;
      unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b;
      unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b in H;
      simpl in *;
      try fold no_negative_occurrence_db_b; try fold no_positive_occurrence_db_b;
      try fold no_negative_occurrence_db_b in H; try fold no_positive_occurrence_db_b in H;
      destruct_and?;
      split_and?; auto.
  - intros H.
    induction ϕ; simpl in *; auto;
      unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b;
      unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b in H;
      simpl in *;
      try fold no_negative_occurrence_db_b; try fold no_positive_occurrence_db_b;
      try fold no_negative_occurrence_db_b in H; try fold no_positive_occurrence_db_b in H;
      destruct_and?;
      split_and?; auto.
Qed.

Lemma SM_well_formed_positive (Σ₁ Σ₂ : Signature) (SM : SignatureMorphism Σ₁ Σ₂) (ϕ : @Pattern Σ₁) :
  well_formed_positive ϕ = true ->
  well_formed_positive (SMϕ SM ϕ) = true.
Proof.
  intros H.
  induction ϕ; simpl in *; destruct_and?; split_and?; auto.
Qed.

Check @ML_proof_system.
Lemma SMpf (Σ₁ Σ₂ : Signature) (SM : SignatureMorphism Σ₁ Σ₂)
      {SM_inj : InjSignatureMorphism Σ₁ Σ₂ SM}
      (Γ : @Theory Σ₁) (ϕ : @Pattern Σ₁) (pf : @ML_proof_system Σ₁ Γ ϕ)
: @ML_proof_system Σ₂ (SMΓ Σ₁ Σ₂ SM Γ) (SMϕ Σ₁ Σ₂ SM ϕ).
Proof.
  induction pf.
  - constructor.




Abort.
