From MatchingLogic.ProofMode Require Import FixPoint Misc.
From MatchingLogic Require Import ContextualImplication.
From MatchingLogic Require Export Definedness_ProofSystem.
From MatchingLogic.ProofMode Require Import FixpointRules.

Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

(* TODO: use the Matching μ-logic paper's lemma 91 proof to prove wrap and unwrap *)
(* source: https://www.ideals.illinois.edu/items/109286 *)
(* wrap is the "only if" way, unwrap is the "if" way *)

(* note: lemma 91's 'base equality': set_builder_full_iff *)
(*  Γ ⊢ ϕ = ∃x.(x ∧ (x ∈ ϕ)) *)

Section WrapUnwrap.

  Context {Σ : Signature} {definedness_syntax : Definedness_Syntax.Syntax}.

  Lemma step_FOL (Γ : Theory) (C : StructureContext) φ ψ (x : evar):
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed ψ ->
    well_formed (sc_pred C) ->
    Γ ⊢ exists_quantify x ((sc_plug C (patt_free_evar x)) and (patt_free_evar x ∈ml φ)) ---> ψ ->
    Γ ⊢ (patt_free_evar x) ∈ml φ ---> (sc_plug C (patt_free_evar x) ---> ψ).
   Proof.
    intros Ht wfphi wfpsi wfscpred H.
    toMLGoal; simpl in *.
    - wf_auto2.
    - 
   Admitted.

   Lemma step_C_property (Γ : Theory) (C : StructureContext) φ ψ (x: evar):
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed φ ->
    well_formed ψ ->
    well_formed (sc_pred C) ->
    Γ ⊢ (sc_plug C (exists_quantify x (patt_free_evar x and patt_free_evar x ∈ml φ)) ---> ψ) ->
    Γ ⊢ (exists_quantify x (sc_plug C (patt_free_evar x) and patt_free_evar x ∈ml φ) ---> ψ).
    Proof.
      intros wft wfphi wfpsi wfpatx H.
      toMLGoal; simpl in *.
      + admit.
    Admitted.

    Lemma exists_quantify_set_builder (Γ : Theory) (C : StructureContext) φ (x : evar):
    evar_is_fresh_in x φ ->
    exists_quantify x (patt_free_evar x and patt_free_evar x ∈ml φ) =
     (ex , b0 and b0 ∈ml φ).
    Proof.
      intros freshx.
      unfold exists_quantify in *.
      f_equal.
      simpl.
      rewrite (evar_quantify_fresh x 0 φ freshx).
      destruct (decide (x = x)).
      + reflexivity.
      + congruence.
    Qed.

    (* TODO give this a more descriptive name as base_eq is also used *)
    Lemma base (Γ : Theory) (C : StructureContext) φ ψ (x : evar):
    Definedness_Syntax.theory ⊆ Γ ->
    evar_is_fresh_in x φ ->
    well_formed φ ->
    Γ ⊢ sc_plug C φ ---> ψ ->
    Γ ⊢ (patt_free_evar x) ∈ml φ ---> (sc_plug C (patt_free_evar x) ---> ψ).
    Proof.
      intros hft freshx wfphi H.
      
      pose proof (exists_quantify_set_builder Γ C φ x freshx) as H0.

      apply (step_FOL Γ C φ ψ x); [exact hft | wf_auto2 | wf_auto2 | wf_auto2 |].

      apply (step_C_property Γ C φ ψ x); [exact hft | wf_auto2 | wf_auto2 | wf_auto2 |].

      rewrite H0.
      Check set_builder_full_iff.
      pose proof set_builder_full_iff as base_eq.
      specialize (base_eq Γ φ hft wfphi). unfold patt_set_builder in base_eq.
      
      pose proof (pf_iff_proj1 Γ φ (ex, b0 and b0 ∈ml φ)).
      
      eapply (syllogism_meta (B := sc_plug C φ)); [wf_auto2 | wf_auto2 | wf_auto2 | |].
      + apply (Framing_StructureContext Γ C _ φ AnyReasoning); [wf_auto2 |].
        apply (pf_iff_proj2 Γ φ (ex , b0 and b0 ∈ml φ)).
        { wf_auto2. }
        { wf_auto2. }
        exact base_eq.
      + exact H.
    Qed.
    
    Lemma step_total (Γ : Theory) (C : StructureContext) φ ψ (x : evar):
    Definedness_Syntax.theory ⊆ Γ ->
    Γ ⊢ (patt_free_evar x) ∈ml φ ---> (sc_plug C (patt_free_evar x) ---> ψ) ->
    Γ ⊢ (patt_free_evar x) ∈ml φ ---> patt_total (sc_plug C (patt_free_evar x) ---> ψ).
    Proof. Admitted.
    
    Lemma wrap_FOL_step (Γ : Theory) (C : StructureContext) φ ψ (x : evar):
    Definedness_Syntax.theory ⊆ Γ ->
    Γ ⊢ (patt_free_evar x) ∈ml φ ---> patt_total (sc_plug C (patt_free_evar x) ---> ψ) ->
    Γ ⊢ (exists_quantify x (patt_free_evar x and patt_free_evar x ∈ml φ)) --->
      exists_quantify x (patt_free_evar x and patt_total ((sc_plug C (patt_free_evar x)) ---> ψ)).
    Proof.
      intros Ht H.
      
    Admitted.
    
    (* layer 1 lemma for wrap *)
    Lemma wrap
      (Γ : Theory)
      (C : StructureContext) φ ψ:
      Definedness_Syntax.theory ⊆ Γ ->
      well_formed φ ->
      well_formed (sc_plug C φ ---> ψ) ->
      well_formed (sc_pred C) ->
      Γ ⊢i φ ---> (contextual_implication C ψ) using AnyReasoning ->
      Γ ⊢i sc_plug C φ ---> ψ using AnyReasoning.
    Proof.
      intros Ht wfphi wfplugimp wfscpred H.
      mlFreshEvar as x.
      
      pose proof set_builder_full_iff as base_eq.
      
      specialize (base_eq Γ φ Ht wfphi).
      unfold patt_set_builder in base_eq.
      
    Admitted.
  
  (* layer 1 unwrap lemma: *)
  Lemma unwrap
    (Γ : Theory)
    (C : StructureContext) φ ψ i :
    Γ ⊢i sc_plug C φ ---> ψ using i ->
    Γ ⊢i φ ---> (contextual_implication C ψ) using i.
  Proof.
    intros.
    toMLGoal. simpl in *.
    + admit.
    + admit.
  Admitted.
  
  (* layer 2 lemmas for wrap and unwrap*)
  Lemma MLGoal_unwrap
     Γ i φ ψ (C : StructureContext):
    well_formed (sc_plug C φ ---> ψ) ->
    well_formed (φ ---> contextual_implication C ψ) ->
    well_formed ψ ->
    of_MLGoal (mkMLGoal Σ Γ [] (sc_plug C φ ---> ψ) i) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (contextual_implication C ψ)) i).
  Proof.
    intros wfscp wfimp wfpsi H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    specialize (H wfscp wfl).

    apply unwrap.
    + exact H.
  Qed.
  
  Lemma MLGoal_wrap
     Γ φ ψ (C : StructureContext):
    Definedness_Syntax.theory ⊆ Γ ->
    well_formed (sc_plug C φ ---> ψ) ->
    well_formed (sc_pred C) ->
    well_formed (φ ---> contextual_implication C ψ) ->
    well_formed (sc_plug C (contextual_implication C ψ) ---> ψ) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (contextual_implication C ψ)) AnyReasoning) ->
    of_MLGoal (mkMLGoal Σ Γ [] (sc_plug C φ ---> ψ) AnyReasoning).
  Proof.
    intros wft wfplug wfp wfscimp wf H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    apply wrap.
    + exact wft.
    + wf_auto2.
    + exact wfplug.
    + exact wfp.
    + specialize (H wfscimp wfl).
      exact H.
  Qed.

End WrapUnwrap.

Tactic Notation "mlWrap" := _ensureProofMode; apply MLGoal_wrap; [try assumption | wf_auto2 | wf_auto2 | wf_auto2 | wf_auto2 |].
Tactic Notation "mlUnwrap" := _ensureProofMode; apply MLGoal_unwrap; [wf_auto2 | wf_auto2 | wf_auto2 | ].

Section WrapUnwrapExamples.

  Lemma example_unwrap1 {Σ : Signature}
     {definedness_syntax : Definedness_Syntax.Syntax}
     Γ a b (C : StructureContext) :
    well_formed (sc_plug C a ---> b) ->
    well_formed (a ---> contextual_implication C b) ->
     Γ ⊢ sc_plug C a ---> b ->
     Γ ⊢ a ---> (contextual_implication C b).
  Proof.
    intros.
    mlUnwrap.
    fromMLGoal.
    exact H1.
  Qed.

  Lemma example_wrap1 {Σ : Signature}
    {definedness_syntax: Definedness_Syntax.Syntax}
    Γ a b (C : StructureContext) :
     well_formed (a ---> contextual_implication C b) ->
     well_formed (sc_plug C a ---> b) ->
     well_formed (sc_pred C) ->
     well_formed (sc_plug C (contextual_implication C b) ---> b) ->
     Definedness_Syntax.theory ⊆ Γ ->
    Γ ⊢ a ---> (contextual_implication C b) ->
    Γ ⊢ sc_plug C a ---> b.
  Proof.
    intros.
    mlWrap.
    fromMLGoal. assumption.
  Qed.
  
End WrapUnwrapExamples.
