From MatchingLogic.ProofMode Require Import FixPoint Misc.
From MatchingLogic Require Import ContextualImplication.
From MatchingLogic Require Export Definedness_ProofSystem.

Import MatchingLogic.Logic.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

(* TODO: check how we could rephrase the layer 2 lemmas to use arbitiary l instead of [] *)
(* note: this might not be needed for the actual automation but would probably be the proper way to do it *)

Section Frame.

  Context {Σ : Signature} {definedness_syntax : Definedness_Syntax.Syntax}.
    
  Lemma Framing_StructureContext (Γ : Theory) (C : StructureContext)
    (A B : Pattern) (i : ProofInfo):
    well_formed (sc_pred C) -> 
    Γ ⊢i (A ---> B) using i ->
    Γ ⊢i ((sc_plug C A) ---> (sc_plug C B)) using i.
  Proof.
    intros wfpred H.

    destruct C.
    unfold sc_plug; simpl.
    
    assert (HC: Γ ⊢i sc_ac.[□↦A] ---> sc_ac.[□↦B] using i).
    + Check Framing.
      apply Framing.
      - try_solve_pile.
      - exact H.

    + toMLGoal; simpl in *.
      - wf_auto2.
      - mlIntro "H0".
        mlDestructAnd "H0" as "Hac" "Hpred".
        mlSplitAnd.
        * mlApplyMeta HC. mlExact "Hac".
        * mlExact "Hpred".
  Qed.
  
  Lemma MLGoal_frame
    Γ i φ ψ (C : StructureContext) :
    well_formed (sc_pred C) ->
    well_formed (φ ---> ψ) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> ψ) i) -> 
    of_MLGoal (mkMLGoal Σ Γ [] (sc_plug C φ ---> sc_plug C ψ) i).
  Proof.
    intros wfc wfimp H.

    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    specialize (H wfimp wfl).

    apply Framing_StructureContext.
    - wf_auto2.
    - exact H.
  Qed.

End Frame.

Tactic Notation "mlFrame" constr(C) :=
  apply (MLGoal_frame _ _ _ _ C); [ try wf_auto2 | try wf_auto2 |].

(* Note: This implementation of unfoldr is for unparametric sorts, the paper uses recursive parametrics sorts
The UnfoldR section will likely need to be restated when we introduce parametric sorts properly.
This should be treated as an expirements for now on unparametric sorts.
*)
Section UnfoldR.
  Context {Σ : Signature} {definedness_syntax : Definedness_Syntax.Syntax}.

  (*
    prefix point:
    φ [ μ X . φ \ X ] -> μ X . φ
  *)
  
  (* layer 1 lemma *)
  Lemma unfold_r
    Γ ψ φ C i:
    well_formed (sc_pred C) ->
    well_formed (patt_mu ψ) ->
    well_formed φ ->
    Γ ⊢i φ ---> sc_plug C (instantiate (patt_mu ψ) (patt_mu ψ)) using i ->
    Γ ⊢i φ ---> sc_plug C (patt_mu ψ) using i.
  Proof.
    intros.

    assert (Γ ⊢i sc_plug C (instantiate (patt_mu ψ) (patt_mu ψ)) --->
            sc_plug C (patt_mu ψ) using i).
    + useBasicReasoning.
      pose proof (Framing_StructureContext Γ C (instantiate (patt_mu ψ) (patt_mu ψ)) (patt_mu ψ) _ H (Pre_fixp Γ ψ H0)).
      exact H3.
    + mlIntro "H".
      mlApplyMeta H3.
      mlApplyMeta H2.
      mlExact "H".
  Qed.

  (* layer 2 lemma *)
  Lemma MLGoal_UnfoldR
    Γ (C: StructureContext) φ ψ i :
    well_formed (sc_pred C) ->
    well_formed (patt_mu ψ) ->
    well_formed (φ) ->
    well_formed (φ ---> sc_plug C (instantiate (patt_mu ψ) (patt_mu ψ))) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> sc_plug C (instantiate (patt_mu ψ) (patt_mu ψ))) i) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> sc_plug C (patt_mu ψ)) i).
  Proof.
    intros wfpred wfmu wfphi wfunf H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.
    specialize (H wfunf wfl).
    apply unfold_r; [wf_auto2 | wf_auto2 | wf_auto2 |].
    + exact H.
  Qed.
  
End UnfoldR.

(* helper tactic for getting the context in which we the patt_mu (μ), returns a term *)
Ltac find_mu_appctx_ctx p :=
  match p with
  | patt_mu _ => constr:(box)
  | patt_app ?a ?b =>
    let C := find_mu_appctx_ctx b in constr:(ctx_app_r a C ltac:(wf_auto2))
  | patt_app ?a ?b =>
    let C := find_mu_appctx_ctx a in constr:(ctx_app_l C b ltac:(wf_auto2))
  | _ =>
    let p' := eval hnf in p in
    match p' with
      | patt_mu _ => constr:(box)
      | _         => fail "no mu ctx found using find_mu_ctx"
    end
  end.

Ltac find_mu_appctx_body p :=
  match p with
  | patt_mu ?a => a
  | patt_app _ ?b => find_mu_appctx_body b
  | patt_app ?a _ => find_mu_appctx_body a
  | _ =>
    let p' := eval hnf in p in
    match p' with
    | patt_mu ?a => a
    | _          => fail "no mu body found using find_mu_body"
    end
  end.

Ltac find_mu_sc_ctx p :=
  match p with
    | patt_and ?a ?pred =>
      let AppCtx := find_mu_appctx_ctx a in
      constr:({| sc_ac := AppCtx ; sc_pred := pred |})
    | _ => fail "find_mu_sc_ctx failed"
  end.
  
Ltac find_mu_sc_body p :=
  match p with
    | patt_and ?a ?pred => find_mu_appctx_body a
    | _ => fail "find_mu_sc_ctx failed"
  end.

Ltac mlUnfoldR :=
  _ensureProofMode;
  lazymatch goal with
  | [ |- @of_MLGoal _ (@mkMLGoal _ ?Ctx _ (patt_imp ?a ?b) ?i) ] =>
      let C := find_mu_sc_ctx b in
      let φ := find_mu_sc_body b in
      apply (MLGoal_UnfoldR Ctx C a φ i);
      [ try wf_auto2 | try wf_auto2 | try wf_auto2 | try wf_auto2 | ]
  | _ => fail "mlUnfoldR failed"
  end.

Ltac mlChangeConcl p :=
  lazymatch goal with
  | |- @of_MLGoal ?Sg (@mkMLGoal ?Sg ?G ?l _ ?i) =>
      change (@of_MLGoal Sg (@mkMLGoal Sg G l p i))
  end.

Section UnfoldRExamples.

  Context {Σ : Signature} {definedness_syntax : Definedness_Syntax.Syntax} (zero succ: symbols) (Γ : Theory).
  
  (* nat is a recusively defined symbol: (B0) *)
  Definition NatPattern := patt_mu (patt_sym zero or patt_sym succ ⋅ B0).

  Example unfoldr_no_context_example : 
    Γ ⊢i patt_sym succ ⋅ NatPattern and patt_top --->
     NatPattern and patt_top using AnyReasoning.
  Proof.

    toMLGoal. simpl in *; try wf_auto2.

    mlUnfoldR.

    mlChangeConcl (patt_sym succ ⋅ NatPattern and patt_top ---> 
              (patt_sym zero or patt_sym succ ⋅ NatPattern) and patt_top).

    mlIntro "H".
    
    mlSplitAnd.
    - mlDestructAnd "H". mlRight. mlAssumption.
    - mlDestructAnd "H". mlAssumption.
  Qed.
  
  Example unfoldr_in_context_example : 
    Γ ⊢i  patt_sym succ ⋅ (patt_sym succ ⋅ NatPattern) and Top ---> patt_sym succ ⋅ NatPattern and Top using AnyReasoning.
  Proof.

    toMLGoal. simpl in *; try wf_auto2.
    mlUnfoldR.
    mlChangeConcl (patt_sym succ ⋅ (patt_sym succ ⋅ NatPattern) and patt_top ---> 
      patt_sym succ ⋅ (patt_sym zero or patt_sym succ ⋅ NatPattern) and patt_top).
    mlFrame {| sc_ac := ctx_app_r (patt_sym succ) box ltac:(wf_auto2) ;
            sc_pred := Top |}.
    mlIntro "H".
    mlRight.
    mlAssumption.
  Qed.

End UnfoldRExamples.


Section ElimExists.
  (* layer 1 lemma: Ex_gen *)

  (* layer 2 lemma *)
  (* maybe we can tighten the proofinfo we use here? *)
  Lemma MLGoal_elim_exists {Σ : Signature}
    Γ φ ψ x:
    well_formed (φ ---> ψ) ->
    x ∉ free_evars ψ ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> ψ) AnyReasoning) ->
    of_MLGoal (mkMLGoal Σ Γ [] (exists_quantify x φ ---> ψ) AnyReasoning).
  Proof.
    intros wfimp Hx H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    apply Ex_gen.
    + try_solve_pile.
    + exact Hx.
    + specialize (H wfimp wfl).
      exact H.
  Qed.

End ElimExists.
 
Tactic Notation "mlElimExists" := apply MLGoal_elim_exists.

Section ElimForall.

  Context {Σ : Signature} {definedness_syntax: Definedness_Syntax.Syntax}.

  (* layer 1 lemma: forall_gen *)

  (* layer 2 lemma for elim-∀ *)
  Lemma MLGoal_Elim_Forall
    ψ φ Γ (C : StructureContext) y:
    well_formed (φ ---> contextual_implication C ψ) ->
    y ∉ free_evars φ ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (contextual_implication C ψ)) AnyReasoning) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (forall_quantify y (contextual_implication C ψ))) AnyReasoning).
  Proof.
    intros wfimp Hx H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    apply (forall_gen Γ φ (contextual_implication C ψ) _ AnyReasoning).
    + unfold evar_is_fresh_in. exact Hx.
    + try_solve_pile.
    + specialize (H wfimp wfl).
      exact H.
  Qed.

End ElimForall.

Tactic Notation "mlElimForall" := _ensureProofMode; apply MLGoal_Elim_Forall; try assumption.

Lemma example_ml_elim_forall_1 {Σ : Signature} {definedness_syntax: Definedness_Syntax.Syntax}
    a b Γ (C : StructureContext) x:
 well_formed a ->
 well_formed (contextual_implication C b) ->
 well_formed (a ---> contextual_implication C b) ->
 well_formed (all, contextual_implication C b) ->
 x ∉ free_evars a ->
 Γ ⊢ a ---> (contextual_implication C b) ->
 Γ ⊢ a ---> (forall_quantify x (contextual_implication C b)).
Proof.
  intros.
  mlElimForall. 
  fromMLGoal.
  exact H4.
Qed.

Section IntroForall.

  Context {Σ : Signature} {definedness_syntax: Definedness_Syntax.Syntax}.

  (* maybe TODO: how to express the recursive structure instead of φ + add the sidecondition *)
  Lemma intro_forall
    φ ψ Γ i (C : StructureContext) x :
  well_formed φ ->
  well_formed (contextual_implication C ψ) ->
  Γ ⊢i φ ---> (forall_quantify x (contextual_implication C ψ)) using i ->
  Γ ⊢i φ ---> contextual_implication C ψ using i.
  Proof.
    intros wfphi wfci H.
    assert (HRhs: Γ ⊢i (forall_quantify x (contextual_implication C ψ) --->
           contextual_implication C ψ) using i).
    + useBasicReasoning.
      unfold forall_quantify.
      Check forall_variable_substitution.
      pose proof (Hs := forall_variable_substitution Γ
        ((contextual_implication C ψ)^{{evar:x↦0}})
        x ltac:(wf_auto2)).
      assert (Heq : (contextual_implication C ψ)^{{evar:x↦0}}^{evar:0↦x} = contextual_implication C ψ).
      - apply evar_open_evar_quantify.
        wf_auto2.
      - rewrite Heq in Hs.
        exact Hs.
    + mlIntro "H".
      mlApplyMeta HRhs.
      mlApplyMeta H.
      mlExact "H".
  Qed.
  
  (* layer 2 lemma for intro-∀ *)
  Lemma MLGoal_Intro_Forall
    ψ φ Γ (C : StructureContext) i x:
    well_formed (φ ---> forall_quantify x (contextual_implication C ψ)) ->
    well_formed φ ->
    well_formed (contextual_implication C ψ) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (forall_quantify x (contextual_implication C ψ))) i) ->
    of_MLGoal (mkMLGoal Σ Γ [] (φ ---> (contextual_implication C ψ)) i).
  Proof.
    intros wfimp wfphi wfctximpl H.
    unfold of_MLGoal in *. simpl in *.

    intros _ wfl.

    specialize (H wfimp wfl).

    apply (intro_forall _ _ _ _ _ x).
    + wf_auto2.
    + wf_auto2.
    + exact H.
  Qed.
  
End IntroForall.

Tactic Notation "mlIntroForall" constr(x) := _ensureProofMode; apply (MLGoal_Intro_Forall _ _ _ _ _ x).

Lemma intro_forall_example1 {Σ : Signature} {definedness_syntax: Definedness_Syntax.Syntax}
  ψ φ Γ (C : StructureContext) x:
  well_formed φ ->
  well_formed (contextual_implication C ψ) ->
  well_formed (φ ---> forall_quantify x (contextual_implication C ψ)) ->
  Γ ⊢ φ ---> forall_quantify x (contextual_implication C ψ) ->
  Γ ⊢ φ ---> contextual_implication C ψ.
Proof.
  intros wfphi wfctximp wfimp2 H. 
  mlIntroForall x.
  + exact wfimp2.
  + exact wfphi.
  + exact wfctximp.
  + fromMLGoal. exact H.
Qed.

(* TODO Introduce recursive paramtetric symbols using product sorts so we can state lfp
  to become an actually recursive parametric lemma*)
  
(* TODO: lfp *)

(* TODO: kt *)
(* KT: sequential composition of wrap, intro-∀, lfp, elim-∀ and unwrap *)
(* sequential compositon ~= applied after each other, building the 'proof tree' upwards *)
(* paper's examples explicitly write the parts instead of an aggregated kt *)
(* maybe we don't need to create any lemmas / tactics here, we can just use the parts after all *)

(* TODO after kt: match-ctx, pm *)

(* TODO after match-ctx + pm: proof search algo *)
