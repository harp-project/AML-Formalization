(* In this module we define the definedness symbol and use it to build derived notions
   like totality and equality.
 *)
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Syntax Semantics DerivedOperators.
From MatchingLogic Require ProofSystem Helpers.FOL_helpers.
From MatchingLogic.Utils Require Import stdpp_ext.

From stdpp Require Import base fin_sets sets propset proof_irrel option list.

Import extralibrary.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.

Close Scope equations_scope. (* Because of [!] *)
Open Scope ml_scope.

(* We have only one symbol *)
Inductive Symbols := definedness.

Instance Symbols_eqdec : EqDecision Symbols.
Proof. unfold EqDecision. intros x y. unfold Decision. destruct x. decide equality. (*solve_decision.*) Defined.

  Class Syntax {Σ : Signature} :=
    {
    (* 'Symbols' are a 'subset' of all the symbols from the Σnature *)
    inj: Symbols -> symbols;
    (* TODO make it injective? *)
    (* for convenience *)
    }.

Section definedness.
  
  Context {Σ : Signature}.

  Context {syntax : Syntax}.

  Definition patt_defined (phi : Pattern) : Pattern :=
    patt_sym (inj definedness) $ phi.
  
  Definition patt_total (phi: Pattern) : Pattern :=
    patt_not (patt_defined (patt_not phi)).

  Definition patt_subseteq (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 ---> phi2).
  
  Definition patt_equal (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 <---> phi2).

  Definition patt_in (phi1 phi2 : Pattern) : Pattern :=
    patt_defined (patt_and phi1 phi2).

  Definition AC_patt_defined : Application_context :=
    @ctx_app_r _ (patt_sym (inj definedness)) box ltac:(auto).

  Definition is_predicate_pattern ψ : Pattern :=
    (patt_equal ψ patt_bott) or (patt_equal ψ patt_top).
End definedness.

Module Notations.
  Import Syntax.

  Notation "⌈ p ⌉" := (patt_defined p) : ml_scope.
  Notation "⌊ p ⌋" := (patt_total p) : ml_scope.
  Notation "p =ml q" := (patt_equal p q) (at level 67) : ml_scope.
  Notation "p ⊆ml q" := (patt_subseteq p q) (at level 67) : ml_scope.
  Notation "p ∈ml q" := (patt_in p q) (at level 67) : ml_scope.
  
End Notations.

Import Notations.

Section definedness.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .

  Lemma well_formed_defined ϕ:
    well_formed ϕ = true ->
    well_formed ⌈ ϕ ⌉ = true.
  Proof.
    intros Hwfϕ.
    unfold patt_defined.
    auto.
  Qed.

  #[local]
   Hint Resolve well_formed_defined : core.

  Lemma well_formed_total ϕ:
    well_formed ϕ = true ->
    well_formed ⌊ ϕ ⌋ = true.
  Proof.
    intros Hwfϕ.
    unfold patt_total.
    auto.
  Qed.

  #[local]
   Hint Resolve well_formed_total : core.
  
  Lemma well_formed_equal (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 =ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "=ml". auto.
  Qed.

  #[local]
   Hint Resolve well_formed_equal : core.
  
  Lemma well_formed_subseteq (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 ⊆ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "⊆ml". auto.
  Qed.

  #[local]
   Hint Resolve well_formed_subseteq : core.

  Lemma well_formed_in (phi1 phi2 : Pattern) :
    well_formed phi1 = true ->
    well_formed phi2 = true ->
    well_formed (phi1 ∈ml phi2) = true.
  Proof.
    intros wfphi1 wfphi2. unfold "∈ml". auto.
  Qed.

  #[local]
   Hint Resolve well_formed_in : core.

  
  Let sym (s : Symbols) : Pattern :=
    @patt_sym Σ (inj s).

  Definition ev_x := (evar_fresh []).
  Definition p_x := patt_free_evar ev_x.
  
  Inductive AxiomName := AxDefinedness.

  Definition axiom(name : AxiomName) : Pattern :=
    match name with
    | AxDefinedness => patt_defined p_x
    end.

  Definition named_axioms : NamedAxioms := {| NAName := AxiomName; NAAxiom := axiom; |}.

  Definition theory := theory_of_NamedAxioms named_axioms.
  
  Lemma definedness_model_application :
    forall (M : @Model Σ) (evar_val : @EVarVal Σ M) (svar_val : @SVarVal (Σ) M),
      M ⊨ᵀ theory ->
      forall (m: Domain M),
                 (app_ext (pattern_interpretation evar_val svar_val (sym definedness)) {[m]}) = ⊤.
  Proof.
    intros.
    unfold app_ext.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq.
    intros x _.
    unfold theory in H.
    pose proof (H' := proj1 (satisfies_theory_iff_satisfies_named_axioms named_axioms M)).
    specialize (H' H AxDefinedness).
    simpl in H'.
    clear H. rename H' into H.
    unfold satisfies_model in H.
    remember (update_evar_val ev_x m evar_val) as evar_val'.
    specialize (H evar_val' svar_val).
    rewrite -> set_eq_subseteq in H.
    destruct H as [_ H].
    rewrite -> elem_of_subseteq in H.
    specialize (H x).
    feed specialize H.
    { apply elem_of_top'. }
    unfold patt_defined in H.
    rewrite -> pattern_interpretation_app_simpl in H.
    rewrite -> pattern_interpretation_sym_simpl in H.
    unfold sym.
    unfold p_x in H.
    rewrite -> pattern_interpretation_free_evar_simpl in H.
    rewrite -> Heqevar_val' in H.
    unfold update_evar_val in H. simpl in H.
    destruct (decide (ev_x = ev_x)).
    2: { contradiction. }
    unfold app_ext in H. unfold In in H.
    destruct H as [m1 [m2 Hm1m2]].
    destruct Hm1m2. destruct H0.
    inversion H0. clear H0. simpl in H2. subst.
    exists m1. exists m2. split. 2: { split. 2: { apply H1. } constructor. }
    rewrite -> pattern_interpretation_sym_simpl. apply H.
  Qed.

  Lemma definedness_not_empty_1 : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        (@pattern_interpretation (Σ) M evar_val svar_val phi) <> ∅ ->
        (@pattern_interpretation (Σ) M evar_val svar_val (patt_defined phi)) = ⊤.
  Proof.
    intros.
    pose (H' := stdpp_ext.Not_Empty_Contains_Elements (pattern_interpretation evar_val svar_val phi) H0).
    destruct H'.
    unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    
    pose proof (H'' := @definedness_model_application M evar_val svar_val H x).
    unfold sym in H''.
    rewrite -> set_eq_subseteq in H''.
    destruct H'' as [_ H''].
    assert (Hincl: {[x]} ⊆ (pattern_interpretation evar_val svar_val phi) ).
    { rewrite -> elem_of_subseteq. intros.  inversion H2. subst. assumption. }

    pose proof (Hincl' := @app_ext_monotonic_r
                            Σ
                            M
                            (pattern_interpretation evar_val svar_val (patt_sym (inj definedness)))
                            {[x]}
                            (pattern_interpretation evar_val svar_val phi)
                            Hincl
               ).

    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    eapply transitivity.
    apply H''.
    assumption.
  Qed.

  Lemma definedness_empty_1 : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation Σ M evar_val svar_val phi = Semantics.Empty ->
        @pattern_interpretation Σ M evar_val svar_val (patt_defined phi) = Semantics.Empty.
  Proof.
    intros M H phi evar_val svar_val H0. unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    rewrite -> H0.
    apply app_ext_bot_r.
  Qed.

  Theorem modus_tollens: forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
  Proof. auto. Qed.

  Lemma definedness_empty_2 : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation Σ M evar_val svar_val (patt_defined phi) = Semantics.Empty ->
        @pattern_interpretation Σ M evar_val svar_val phi = Semantics.Empty.
  Proof.
    intros M H phi evar_val svar_val H0.
    pose proof (H1 := @empty_impl_not_full Σ M _ H0).
    pose proof (H2 := @modus_tollens _ _ (@definedness_not_empty_1 M H phi evar_val svar_val) H1).
    apply NNPP in H2. apply H2.
  Qed.

  Lemma definedness_not_empty_2 : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_defined phi) = Full ->
        @pattern_interpretation (Σ) M evar_val svar_val phi <> Semantics.Empty.
  Proof.
    intros M H phi evar_val svar_val H0.
    pose proof (H1 := full_impl_not_empty H0).
    exact (@modus_tollens _ _ (@definedness_empty_1 M H phi evar_val svar_val) H1).
  Qed.

  Lemma totality_not_full : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val phi <> ⊤ ->
        @pattern_interpretation (Σ) M evar_val svar_val (patt_total phi) = ∅.
  Proof.
    intros.
    assert (Hnonempty : pattern_interpretation evar_val svar_val (patt_not phi) <> ∅).
    { unfold not. unfold not in H0. intros. rewrite -> pattern_interpretation_not_simpl in H1.
      apply H0. clear H0.
      rewrite -> set_eq_subseteq.
      split.
      { apply top_subseteq. }
      rewrite -> complement_empty_iff_full in H1.
      rewrite H1.
      apply top_subseteq.
    }
    unfold patt_total. rewrite -> pattern_interpretation_not_simpl.
    rewrite -> complement_empty_iff_full.

    apply definedness_not_empty_1.
    { apply H. }
    apply Hnonempty.
  Qed.

  Lemma totality_full : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val phi = ⊤ ->
        @pattern_interpretation (Σ) M evar_val svar_val (patt_total phi) = ⊤.
  Proof.
    intros M H phi evar_val svar_val H0.
    unfold patt_total.
    rewrite -> pattern_interpretation_not_simpl.
    assert(H1: pattern_interpretation evar_val svar_val (patt_not phi) = ∅).
    { rewrite -> pattern_interpretation_not_simpl.
      rewrite -> H0.
      clear. set_solver.
    }

    pose proof (H2 := @definedness_empty_1 M H (patt_not phi) evar_val svar_val H1).
    rewrite -> H2.
    clear. set_solver.
  Qed.

  Lemma totality_result_empty : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_total phi) = ∅ ->
        @pattern_interpretation (Σ) M evar_val svar_val phi <> ⊤.
  Proof.
    intros M H phi evar_val svar_val H0.
    pose proof (H1 := empty_impl_not_full H0).
    pose proof (H2 := @modus_tollens _ _ (@totality_full M H phi evar_val svar_val) H1).
    apply H2.
  Qed.

  Lemma totality_result_nonempty : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_total phi) <> ∅ ->
        @pattern_interpretation (Σ) M evar_val svar_val phi = ⊤.
  Proof.
    intros M H phi evar_val svar_val H0.
    pose proof (H2 := @modus_tollens _ _ (@totality_not_full M H phi evar_val svar_val) H0).
    apply NNPP in H2. apply H2.
  Qed.
  
  Lemma equal_iff_both_subseteq : forall (M : @Model (Σ)),        
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_equal phi1 phi2) = ⊤ <->
        (
          @pattern_interpretation (Σ) M evar_val svar_val (patt_subseteq phi1 phi2) = ⊤ /\
          @pattern_interpretation (Σ) M evar_val svar_val (patt_subseteq phi2 phi1) = ⊤).
  Proof.
    intros M H phi1 phi2 evar_val svar_val.
    split.
    - intros H0.
      unfold patt_equal in H0.
      apply full_impl_not_empty in H0.
      apply (@totality_result_nonempty _ H) in H0.
      unfold "<--->" in H0.
      rewrite -> pattern_interpretation_and_simpl in H0.
      rewrite -> intersection_full_iff_both_full in H0.
      destruct H0 as [H1 H2].
      unfold patt_subseteq.
      apply (@totality_full _ H) in H1.
      apply (@totality_full _ H) in H2.
      split; assumption.
    - intros [H0 H1].
      unfold patt_subseteq.
      apply full_impl_not_empty in H0.
      apply full_impl_not_empty in H1.
      apply (@totality_result_nonempty _ H) in H0.
      apply (@totality_result_nonempty _ H) in H1.
      unfold patt_equal.
      apply (@totality_full _ H).
      unfold "<--->".
      rewrite -> pattern_interpretation_and_simpl.
      rewrite -> H0.
      rewrite -> H1.
      clear. set_solver.
  Qed.

  Lemma subseteq_iff_interpr_subseteq : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_subseteq phi1 phi2) = ⊤ <->
        (@pattern_interpretation (Σ) M evar_val svar_val phi1)
          ⊆ (@pattern_interpretation (Σ) M evar_val svar_val phi2).
  Proof.
    intros M H phi1 phi2 evar_val svar_val.
    split.
    - intros H0.
      unfold patt_subseteq in H0.
      apply full_impl_not_empty in H0.
      apply (@totality_result_nonempty _ H) in H0.
      rewrite -> pattern_interpretation_imp_simpl in H0.
      rewrite -> set_eq_subseteq in H0.
      destruct H0 as [_ H0].
      rewrite -> elem_of_subseteq in H0.
      intros x H1. specialize (H0 x).
      feed specialize H0.
      { apply elem_of_top'. }
      remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
      remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
      clear -H0 H1.
      set_solver.
    - intros H0.
      unfold patt_subseteq.
      apply (@totality_full _ H).
      rewrite -> pattern_interpretation_imp_simpl.
      rewrite -> set_eq_subseteq.
      split.
      { apply top_subseteq. }
      rewrite -> elem_of_subseteq.
      intros x _. specialize (H0 x).
      destruct (classic (x ∈ (pattern_interpretation evar_val svar_val phi1))).
      + right. auto.
      + left. apply elem_of_compl. assumption.
  Qed.
  
  Lemma equal_iff_interpr_same : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_equal phi1 phi2) = Full <->
        @pattern_interpretation (Σ) M evar_val svar_val phi1
        = @pattern_interpretation (Σ) M evar_val svar_val phi2.
  Proof.
    intros M H phi1 phi2 evar_val svar_val.
    split.
    - intros H0.
      apply (@equal_iff_both_subseteq _ H) in H0.
      destruct H0 as [Hsub1 Hsub2].
      apply (@subseteq_iff_interpr_subseteq _ H) in Hsub1.
      apply (@subseteq_iff_interpr_subseteq _ H) in Hsub2.
      rewrite -> set_eq_subseteq.
      split; assumption.
    - intros H0.
      rewrite -> set_eq_subseteq in H0.
      destruct H0 as [Hincl1 Hincl2].
      apply (@subseteq_iff_interpr_subseteq _ H) in Hincl1.
      apply (@subseteq_iff_interpr_subseteq _ H) in Hincl2.
      apply equal_iff_both_subseteq. auto. split; auto.
  Qed.

  Lemma equal_refl : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_equal phi phi) = Full.
  Proof.
    intros M H phi evar_val svar_val.
    apply (@equal_iff_interpr_same _ H).
    auto.
  Qed.

  Lemma equal_sym : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_equal phi1 phi2) = Full ->
        @pattern_interpretation (Σ) M evar_val svar_val (patt_equal phi2 phi1) = Full.
  Proof.
    intros M H phi1 phi2 evar_val svar_val H0.
    apply (@equal_iff_interpr_same _ H).
    apply (@equal_iff_interpr_same _ H) in H0.
    symmetry. auto.
  Qed.

  Lemma equal_trans : forall (M : @Model (Σ)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 phi3 : Pattern) (evar_val : @EVarVal (Σ) M) (svar_val : @SVarVal (Σ) M),
        @pattern_interpretation (Σ) M evar_val svar_val (patt_equal phi1 phi2) = Full ->
        @pattern_interpretation (Σ) M evar_val svar_val (patt_equal phi2 phi3) = Full ->
        @pattern_interpretation (Σ) M evar_val svar_val (patt_equal phi1 phi3) = Full.
  Proof.
    intros M H phi1 phi2 phi3 evar_val svar_val H0 H1.
    apply (@equal_iff_interpr_same _ H).
    apply (@equal_iff_interpr_same _ H) in H0.
    apply (@equal_iff_interpr_same _ H) in H1.
    rewrite -> H0. auto.
  Qed.

  Lemma free_evar_in_patt : forall (M : @Model Σ),
      M ⊨ᵀ theory ->
      forall (x : evar)(phi : Pattern) (evar_val : @EVarVal Σ M) (svar_val : @SVarVal Σ M),
        ((evar_val x) ∈ (@pattern_interpretation Σ M evar_val svar_val phi)) <->
        @pattern_interpretation Σ M evar_val svar_val (patt_in (patt_free_evar x) phi) = ⊤.
  Proof.
    intros M H x phi evar_val svar_val.
    split.
    - intros H0.
      unfold patt_in.
      apply (@definedness_not_empty_1 _ H).
      intros Contra.
      apply Contains_Elements_Not_Empty in Contra. exact Contra.
      exists (evar_val x).
      rewrite -> pattern_interpretation_and_simpl.
      split.
      + rewrite -> pattern_interpretation_free_evar_simpl. constructor.
      + assumption.
    - intros H0.
      unfold patt_in in H0.
      apply (@definedness_not_empty_2 _ H) in H0.
      unfold not in H0.
      assert (H0': (pattern_interpretation evar_val svar_val (patt_free_evar x and phi)) = ∅ -> False).
      { intros Contra. apply H0. auto. }
      apply Not_Empty_Contains_Elements in H0'.
      destruct H0' as [x0 H0'].
      rewrite -> pattern_interpretation_and_simpl in H0'.
      destruct H0'.
      rewrite -> pattern_interpretation_free_evar_simpl in H1.
      inversion H1. subst. assumption.
  Qed.
  
  Lemma T_predicate_defined : forall ϕ, T_predicate theory (patt_defined ϕ).
  Proof.
    intros ϕ. unfold T_predicate. intros. unfold M_predicate. intros.
    pose proof (Hlr := classic ( pattern_interpretation ρₑ ρ ϕ = Semantics.Empty )).
    destruct Hlr.
    + apply definedness_empty_1 in H0. right. apply H0. apply H.
    + apply definedness_not_empty_1 in H0. left. apply H0. apply H.
  Qed.

  Hint Resolve T_predicate_defined : core.

  Lemma T_predicate_total : forall ϕ, T_predicate theory (patt_total ϕ).
  Proof.
    intros ϕ. unfold patt_total.
    apply T_predicate_not.
    apply T_predicate_defined.
  Qed.

  Hint Resolve T_predicate_total : core.

  Lemma T_predicate_subseteq : forall ϕ₁ ϕ₂, T_predicate theory (patt_subseteq ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂. unfold patt_subseteq. apply T_predicate_total.
  Qed.

  Hint Resolve T_predicate_subseteq : core.
  
  Lemma T_predicate_equals : forall ϕ₁ ϕ₂, T_predicate theory (patt_equal ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂. unfold patt_equal. apply T_predicate_total.
  Qed.

  Hint Resolve T_predicate_equals : core.

  Lemma T_predicate_in : forall ϕ₁ ϕ₂, T_predicate theory (patt_in ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂. unfold patt_equal. apply T_predicate_defined.
  Qed.

  Hint Resolve T_predicate_in : core.

  (* defined, total, subseteq, equal, in *)
  Lemma bevar_subst_defined ψ x ϕ : bevar_subst (patt_defined ϕ) ψ x = patt_defined (bevar_subst ϕ ψ x).
  Proof. unfold patt_defined. cbn. auto. Qed.
  Lemma bsvar_subst_defined ψ x ϕ : bsvar_subst (patt_defined ϕ) ψ x = patt_defined (bsvar_subst ϕ ψ x).
  Proof. unfold patt_defined. cbn. auto. Qed.

  #[global]
   Instance Unary_defined : Unary patt_defined :=
    {| unary_bevar_subst := bevar_subst_defined ;
       unary_bsvar_subst := bsvar_subst_defined ;
    |}.
  

  Lemma bevar_subst_total ψ x ϕ : bevar_subst (patt_total ϕ) ψ x = patt_total (bevar_subst ϕ ψ x).
  Proof. unfold patt_total. rewrite !simpl_bevar_subst. reflexivity. Qed.
  Lemma bsvar_subst_total ψ x ϕ : bsvar_subst (patt_total ϕ) ψ x = patt_total (bsvar_subst ϕ ψ x).
  Proof. unfold patt_total. rewrite !simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Unary_total : Unary patt_total :=
    {| unary_bevar_subst := bevar_subst_total ;
       unary_bsvar_subst := bsvar_subst_total ;
    |}.
  
  
  Lemma bevar_subst_equal ψ x ϕ₁ ϕ₂ :
    bevar_subst (patt_equal ϕ₁ ϕ₂) ψ x = patt_equal (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
  Proof. unfold patt_equal. rewrite !simpl_bevar_subst. reflexivity. Qed.

  Lemma bsvar_subst_equal ψ x ϕ₁ ϕ₂ :
    bsvar_subst (patt_equal ϕ₁ ϕ₂) ψ x = patt_equal (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
  Proof. unfold patt_equal. rewrite !simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Binary_equal : Binary patt_equal :=
    {| binary_bevar_subst := bevar_subst_equal ;
       binary_bsvar_subst := bsvar_subst_equal ;
    |}.
  
  Lemma bevar_subst_subseteq ψ x ϕ₁ ϕ₂ :
    bevar_subst (patt_subseteq ϕ₁ ϕ₂) ψ x = patt_subseteq (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
  Proof. unfold patt_subseteq. rewrite !simpl_bevar_subst. reflexivity. Qed.

  Lemma bsvar_subst_subseteq ψ x ϕ₁ ϕ₂ :
    bsvar_subst (patt_subseteq ϕ₁ ϕ₂) ψ x = patt_subseteq (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
  Proof. unfold patt_subseteq. rewrite !simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Binary_subseteq : Binary patt_subseteq :=
    {| binary_bevar_subst := bevar_subst_subseteq ;
       binary_bsvar_subst := bsvar_subst_subseteq ;
    |}.
  

  Lemma bevar_subst_in ψ x ϕ₁ ϕ₂ :
    bevar_subst (patt_in ϕ₁ ϕ₂) ψ x = patt_in (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
  Proof. unfold patt_in. rewrite !simpl_bevar_subst. reflexivity. Qed.

  Lemma bsvar_subst_in ψ x ϕ₁ ϕ₂ :
    bsvar_subst (patt_in ϕ₁ ϕ₂) ψ x = patt_in (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
  Proof. unfold patt_in. rewrite !simpl_bsvar_subst. reflexivity. Qed.

  #[global]
   Instance Binary_in : Binary patt_in :=
    {| binary_bevar_subst := bevar_subst_in ;
       binary_bsvar_subst := bsvar_subst_in ;
    |}.

  (* Defines ϕ₁ to be an inversion of ϕ₂ *)
  (* ∀ x. ϕ₁ x = ∃ y. y ∧ (x ∈ ϕ₂ y)  *)
  Definition patt_eq_inversion_of ϕ₁ ϕ₂
    := patt_forall
         (patt_equal
            (patt_app (nest_ex ϕ₁) (patt_bound_evar 0))
            (patt_exists (patt_and (patt_bound_evar 0)
                                   (patt_in (patt_bound_evar 1)
                                            (patt_app (nest_ex (nest_ex ϕ₂)) (patt_bound_evar 0)))))).

  Lemma T_predicate_eq_inversion : forall ϕ₁ ϕ₂, T_predicate theory (patt_eq_inversion_of ϕ₁ ϕ₂).
  Proof.
    intros ϕ₁ ϕ₂ M Hm.
    unfold patt_eq_inversion_of.
    apply M_predicate_forall.
    match goal with
    | |- context G [fresh_evar ?t] => remember (fresh_evar t) as X
    end.
    
    unfold evar_open.
    rewrite simpl_bevar_subst.
    apply T_predicate_equals.
    apply Hm.
  Qed.

  Lemma pattern_interpretation_eq_inversion_of ϕ₁ ϕ₂ M ρₑ ρₛ :
    M ⊨ᵀ theory ->
    @pattern_interpretation Σ M ρₑ ρₛ (patt_eq_inversion_of ϕ₁ ϕ₂) = ⊤
    <-> (forall m₁ m₂,
            m₂ ∈ rel_of ρₑ ρₛ ϕ₁ m₁ <-> m₁ ∈ rel_of ρₑ ρₛ ϕ₂ m₂ (* TODO make rel_of take one more parameter. *)
        ).
  Proof.
    intros Htheory.
    rewrite pattern_interpretation_forall_predicate.
    2: { unfold evar_open. rewrite simpl_bevar_subst. apply T_predicate_equals. apply Htheory. }
    apply all_iff_morphism. intros m₁.
    remember ((fresh_evar
          (patt_equal (nest_ex ϕ₁ $ BoundVarSugar.b0)
             (ex ,
              (BoundVarSugar.b0
                 and patt_in BoundVarSugar.b1 (nest_ex (nest_ex ϕ₂) $ BoundVarSugar.b0)))))) as x.
    unfold evar_open.
    rewrite !simpl_bevar_subst.
    rewrite equal_iff_interpr_same.
    2: { apply Htheory. }

    rewrite pattern_interpretation_set_builder.
    { unfold evar_open. rewrite !simpl_bevar_subst. apply T_predicate_in. apply Htheory. }

    assert (Hpi: ∀ M ev sv phi rhs,
               @pattern_interpretation _ M ev sv phi = rhs
               <-> (∀ m, m ∈ @pattern_interpretation _ M ev sv phi <-> m ∈ rhs)).
    { split; intros H.
      + rewrite H. auto.
      + rewrite -> set_eq_subseteq. repeat rewrite elem_of_subseteq.
        split.
        * intros x0. specialize (H x0). destruct H as [H1 H2].
          apply H1.
        * intros x0. specialize (H x0). destruct H as [H1 H2].
          apply H2.
    }
    rewrite Hpi.
    apply all_iff_morphism. intros m₂.
    rewrite pattern_interpretation_app_simpl.

    rewrite pattern_interpretation_evar_open_nest_ex.
    {
      subst x.
      eapply evar_is_fresh_in_richer.
      2: { apply set_evar_fresh_is_fresh. }
      solve_free_evars_inclusion 5.
    }
    unfold evar_open.
    rewrite !simpl_bevar_subst. simpl.
(*
    do 3 rewrite evar_open_bound_evar.
    repeat case_match; try lia.
*)
    remember (fresh_evar (patt_in (patt_free_evar x) (bevar_subst (nest_ex (nest_ex ϕ₂)) (patt_free_evar x) 1 $ b0))) as y.
(*
    rewrite simpl_evar_open.
    rewrite evar_open_free_evar.
*)
    repeat rewrite elem_of_PropSet.
    rewrite <- free_evar_in_patt.
    2: { apply Htheory. }
    rewrite pattern_interpretation_free_evar_simpl.
    rewrite update_evar_val_same.
    fold (m₂ ∈ rel_of ρₑ ρₛ ϕ₁ m₁).

    (*rewrite simpl_evar_open.*)
    rewrite pattern_interpretation_app_simpl.
    (*rewrite [evar_open 0 y b0]/=.*)
    rewrite pattern_interpretation_free_evar_simpl.
    rewrite update_evar_val_same.
    
    fold (evar_open 1 x (nest_ex (nest_ex ϕ₂))).
    rewrite evar_open_nest_ex_aux_comm.
    destruct (extralibrary.compare_nat 1 0); try lia. clear g.
    rewrite [1 - 1]/=.

    rewrite pattern_interpretation_evar_open_nest_ex'.
    {
      rewrite evar_open_nest_ex_aux_comm.
      destruct (extralibrary.compare_nat 0 0); try lia.
      unfold evar_is_fresh_in.
      rewrite free_evars_nest_ex_aux.
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'.
      simpl.
      solve_free_evars_inclusion 5.
    }

    rewrite pattern_interpretation_evar_open_nest_ex'.
    {
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'.
      solve_free_evars_inclusion 5.
    }

    rewrite pattern_interpretation_free_evar_independent.
    {
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'.
      solve_free_evars_inclusion 5.
    }

    rewrite pattern_interpretation_free_evar_independent.
    {
      subst.
      eapply evar_is_fresh_in_richer'.
      2: apply set_evar_fresh_is_fresh'.
      solve_free_evars_inclusion 5.
    }

    rewrite update_evar_val_comm.
    { solve_fresh_neq. }

    rewrite update_evar_val_same.
    unfold app_ext.
    rewrite elem_of_PropSet.
    fold (rel_of ρₑ ρₛ ϕ₂ m₂).
    auto.
  Qed.

  Lemma single_element_definedness_impl_satisfies_definedness (M : @Model Σ) :
    (exists (hashdef : Domain M),
        sym_interp M (inj definedness) = {[hashdef]}
        /\ forall x, app_interp hashdef x = ⊤
    ) ->
        satisfies_model M (axiom AxDefinedness).
  Proof.
    intros [hashdef [Hhashdefsym Hhashdeffull]].
    unfold satisfies_model. intros.
    unfold axiom.
    unfold sym.
    unfold patt_defined.
    unfold p_x.
    rewrite -> pattern_interpretation_app_simpl.
    rewrite -> pattern_interpretation_sym_simpl.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq.
    intros x _.
    intros.
    unfold Ensembles.In.
    unfold app_ext.
    exists hashdef.
    rewrite Hhashdefsym.
    rewrite -> pattern_interpretation_free_evar_simpl.
    exists (evar_val ev_x).
    split.
    { constructor. }
    split.
    { constructor. }
    rewrite Hhashdeffull.
    constructor.
  Qed.

End definedness.
  
#[export]
 Hint Resolve well_formed_defined : core.
#[export]
 Hint Resolve well_formed_total : core.
#[export]
 Hint Resolve well_formed_equal : core.
#[export]
 Hint Resolve well_formed_subseteq : core.
#[export]
 Hint Resolve well_formed_in : core.


Section ProofSystemTheorems.

  Context
    {Σ : Signature}
    {syntax : Syntax}
  .

  
  Import ProofSystem ProofSystem.Notations Helpers.FOL_helpers.

  Lemma patt_iff_implies_equal :
    forall (φ1 φ2 : Pattern) Γ, well_formed φ1 -> well_formed φ2 ->
                                Γ ⊢ (φ1 <---> φ2) -> Γ ⊢ φ1 =ml φ2.
  Proof.
    intros φ1 φ2 Γ WF1 WF2 H.
    epose proof (ANNA := @A_implies_not_not_A_ctx Σ Γ (φ1 <---> φ2) (ctx_app_r box _)). 
    apply ANNA; auto.
    Unshelve.
    auto.
  Defined.

  Lemma patt_equal_refl :
    forall φ Γ, well_formed φ ->
                Γ ⊢ φ =ml φ.
  Proof.
    intros φ Γ WF. pose proof (IFF := @pf_iff_equiv_refl Σ Γ φ WF).
    apply patt_iff_implies_equal in IFF; auto.
  Qed.

  Lemma use_defined_axiom Γ:
    theory ⊆ Γ ->
    Γ ⊢ patt_defined p_x.
  Proof.
    intros HΓ.
    apply hypothesis; auto. unfold theory,theory_of_NamedAxioms in HΓ. simpl in HΓ.
    eapply elem_of_weaken.
    2: { apply HΓ. }
    unfold axiom.
    apply elem_of_PropSet.
    exists AxDefinedness.
    reflexivity.
  Defined.

  Lemma defined_evar Γ x:
    theory ⊆ Γ ->
    Γ ⊢ ⌈ patt_free_evar x ⌉.
  Proof.
    intros HΓ.
    assert(S1: Γ ⊢ patt_defined p_x) by (auto using use_defined_axiom).

    pose proof (S1' := S1).
    apply universal_generalization with (x0 := ev_x) in S1'; auto.
    replace (evar_quantify ev_x 0 ( @patt_defined Σ syntax p_x))
      with (evar_quantify x 0 ⌈ patt_free_evar x ⌉) in S1'.
    2: { simpl. repeat case_match; auto; contradiction. }
    
    eapply Modus_ponens.
    4: apply forall_variable_substitution.
    3: apply S1'.
    all: auto; simpl; case_match; auto.
  Defined.
  
    
  Lemma in_context_impl_defined Γ AC ϕ:
    theory ⊆ Γ ->
    well_formed ϕ ->
    Γ ⊢ (subst_ctx AC ϕ) ---> ⌈ ϕ ⌉.
  Proof.
    intros HΓ Hwfϕ.
    assert(S1: Γ ⊢ patt_defined p_x) by (auto using use_defined_axiom).

    pose proof (S1' := S1).
    apply universal_generalization with (x := ev_x) in S1'; auto.
    remember (evar_fresh (elements (free_evars ϕ ∪ AC_free_evars AC ))) as x'.

    assert (Hx1': evar_is_fresh_in x' ϕ).
    { rewrite Heqx'.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: { apply set_evar_fresh_is_fresh'. }
      clear. set_solver.
    }

    assert (Hx'2: x' ∉ AC_free_evars AC).
    { rewrite Heqx'.
      eapply not_elem_of_larger_impl_not_elem_of.
      2: apply set_evar_fresh_is_fresh'.
      clear.
      set_solver.
    }
    
    assert (S1'' : Γ ⊢ ⌈ patt_free_evar x' ⌉).
    {
      (* For some reason, Coq cannot infer the implicit argument 'syntax' automatically *)
      replace (evar_quantify ev_x 0 ( @patt_defined Σ syntax p_x))
        with (evar_quantify x' 0 ⌈ patt_free_evar x' ⌉) in S1'.
      2: { simpl. repeat case_match; auto; contradiction. }
          
      eapply Modus_ponens.
      4: apply forall_variable_substitution.
      3: apply S1'.
      all: auto; simpl; case_match; auto. (* For some reason, [auto] is not enough here *)
    }
    
    assert(S2: Γ ⊢ ⌈ patt_free_evar x' ⌉ or ⌈ ϕ ⌉).
    {
      toMyGoal. mgLeft; auto.
    }

    assert(S3: Γ ⊢ ⌈ patt_free_evar x' or ϕ ⌉).
    {
      pose proof (Htmp := (prf_prop_or_iff Γ AC_patt_defined) (patt_free_evar x') ϕ ltac:(auto) ltac:(auto)).
      simpl in Htmp.
      apply pf_conj_elim_r_meta in Htmp; auto.
      eapply Modus_ponens. 4: apply Htmp.
      all: auto.
    }

    assert(S4: Γ ⊢ ⌈ ((patt_free_evar x') and (! ϕ)) or ϕ ⌉).
    {
      assert(Htmp1: Γ ⊢ (patt_free_evar x' or ϕ) ---> (patt_free_evar x' and ! ϕ or ϕ)).
      {
        toMyGoal. mgIntro.
        mgAdd (@A_or_notA Σ Γ ϕ Hwfϕ); auto.
        mgDestruct 0; auto.
        - mgRight; auto. mgExactn 0; auto.
        - mgLeft; auto. mgIntro.
          mgDestruct 1; auto 10.
          + mgDestruct 2; auto.
            * mgApply 2; auto 10. mgExactn 1; auto 10.
            * mgApply 2; auto 10. mgExactn 0; auto 10.
          + mgApply 0; auto 10.
            mgExactn 1; auto 10.
      }
      
      assert(Htmp2: Γ ⊢ (⌈ patt_free_evar x' or ϕ ⌉) ---> (⌈ patt_free_evar x' and ! ϕ or ϕ ⌉)).
      {
        apply Framing_right. apply Htmp1.
      }
      
      eapply Modus_ponens.
      4: apply Htmp2.
      all: auto 10.
    }

    assert(S5: Γ ⊢ ⌈ (patt_free_evar x' and (! ϕ)) ⌉ or ⌈ ϕ ⌉).
    {
      pose proof (Htmp := (prf_prop_or_iff Γ AC_patt_defined) (patt_free_evar x' and ! ϕ) ϕ ltac:(auto) ltac:(auto)).
      simpl in Htmp.
      apply pf_conj_elim_l_meta in Htmp; auto 10.
      eapply Modus_ponens. 4: apply Htmp.
      all: auto 10.
    }

    assert(S6: Γ ⊢ subst_ctx AC (patt_free_evar x' and ϕ) ---> ! ⌈ patt_free_evar x' and ! ϕ ⌉).
    {
      pose proof (Htmp := Singleton_ctx Γ AC AC_patt_defined ϕ x').
      simpl in Htmp.
      unfold patt_and in Htmp at 1.
      apply not_not_elim_meta in Htmp; auto 10.
      replace (patt_sym (inj definedness) $ (patt_free_evar x' and ! ϕ))
        with (patt_defined (patt_free_evar x' and ! ϕ)) in Htmp by reflexivity.
      
      toMyGoal. mgIntro. mgAdd Htmp; auto 10.
      mgApply 0; auto 10. mgIntro. mgApply 2; auto 10.
      mgExactn 1; auto 10.
    }

    pose proof (S7 := S5). unfold patt_or in S7.

    assert(S8: Γ ⊢ subst_ctx AC (patt_free_evar x' and ϕ) ---> ⌈ ϕ ⌉).
    {
      eapply syllogism_intro.
      5: apply S7.
      all: auto 10.
    }
    assert (S9: Γ ⊢ all, (subst_ctx AC (patt_bound_evar 0 and ϕ) ---> ⌈ ϕ ⌉)).
    {
      eapply universal_generalization with (x := x') in S8; auto.
      simpl in S8.
      
      rewrite evar_quantify_subst_ctx in S8;[assumption|].

      simpl in S8.
      case_match; try contradiction.
      rewrite evar_quantify_fresh in S8; [assumption|].
      apply S8.
    }

    assert(S10: Γ ⊢ (ex, subst_ctx AC (b0 and ϕ)) ---> ⌈ ϕ ⌉).
    {
      unfold patt_forall in S9.
      unfold patt_not in S9 at 1.

      assert (Heq: evar_quantify x' 0 (subst_ctx AC (patt_free_evar x' and ϕ)) = subst_ctx AC (b0 and ϕ)).
      {
        rewrite evar_quantify_subst_ctx;[assumption|].
        f_equal.
        simpl.
        case_match; [|congruence].
        rewrite evar_quantify_fresh; [assumption|].
        reflexivity.
      }
      rewrite <- Heq.
      apply Ex_gen.
      4: {simpl. unfold evar_is_fresh_in in Hx1'. clear -Hx1'. set_solver. }
      1,2: auto.
      assumption.
    }

    assert (S11: Γ ⊢ ϕ ---> ((ex, patt_bound_evar 0) and ϕ)).
    {
      toMyGoal. mgIntro.
      mgAdd (@conj_intro Σ Γ (ex, b0) ϕ ltac:(auto) ltac:(auto)); auto.
      
      mgAssert ((ϕ ---> ex , b0 and ϕ)); auto 10.
      {  mgApply 0; auto 10.  mgAdd (Existence Γ); auto 10.
         mgExactn 0; auto 10.
      }
      mgApply 2; auto 10. mgExactn 1; auto 10.
    }

    assert (well_formed (ex , (b0 and ϕ))).
    {
      unfold well_formed,well_formed_closed in *.
      destruct_and!.
      simpl; split_and!; auto.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    }
    
    assert (S12: Γ ⊢ ϕ ---> ex, (b0 and ϕ)).
    {

      assert(well_formed (ex , (evar_quantify x' 0 (patt_free_evar x') and ϕ))).
      {
        unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!. split_and!; auto.
        all: repeat case_match; auto.
      }
      
      assert(Htmp: Γ ⊢ ((ex, b0) and ϕ ---> (ex, (b0 and ϕ)))).
      {
        toMyGoal. mgIntro. mgDestructAnd 0; auto. fromMyGoal.
        replace b0 with (evar_quantify x' 0 (patt_free_evar x')).
        2: { simpl. case_match;[reflexivity|congruence]. }
        apply Ex_gen; auto.
        2: { simpl. case_match;[|congruence]. simpl.
             unfold evar_is_fresh_in in Hx1'. clear -Hx1'. set_solver.
        }
        toMyGoal. do 2 mgIntro.
        mgAssert ((patt_free_evar x' and ϕ)) using first 2.
        { unfold patt_and. unfold patt_not at 1. mgIntro.
          mgDestruct 2; auto.
          - mgApply 2; auto 10. mgExactn 0; auto.
          - mgApply 2; auto 10. mgExactn 1; auto 10.
        }
        mgClear 1; auto. mgClear 0; auto.
        fromMyGoal.
        case_match;[|congruence].

        replace (patt_free_evar x' and ϕ)
          with (instantiate (ex, (patt_bound_evar 0 and ϕ)) (patt_free_evar x')).
        2: {
          simpl. rewrite bevar_subst_not_occur.
          { apply wfc_ex_aux_implies_not_bevar_occur. unfold well_formed, well_formed_closed in *.
            destruct_and!. auto.
          }
          reflexivity.
        }
        apply Ex_quan.
      }
      eapply syllogism_intro.
      5: { apply Htmp. }
      all: auto.
    }

    assert(S13: Γ ⊢ (subst_ctx AC ϕ) ---> (subst_ctx AC (ex, (b0 and ϕ)))).
    {
      apply Framing; auto.
    }

    assert(S14: Γ ⊢ (subst_ctx AC (ex, (b0 and ϕ))) ---> (⌈ ϕ ⌉)).
    {
      Check prf_prop_ex_iff.
      pose proof (Htmp := @prf_prop_ex_iff Σ Γ AC (b0 and ϕ) x').
      feed specialize Htmp.
      { unfold evar_is_fresh_in in *.
        rewrite free_evars_subst_ctx. clear -Hx1' Hx'2. simpl. set_solver.
      }
      { auto. }
      unfold exists_quantify in Htmp.
      rewrite evar_quantify_subst_ctx in Htmp.
      { assumption. }

      assert (well_formed (ex , subst_ctx AC (b0 and ϕ))).
      {
        unfold well_formed,well_formed_closed in *. destruct_and!.
        split_and!; simpl; auto.
        3: { apply wcex_sctx.
             simpl. split_and!; auto.
             eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
        }
        2: {
          apply wcmu_sctx.
          simpl. split_and!; auto.
        }
        1: {
          apply wp_sctx. simpl. split_and!; auto.
        }
      }
      
      rewrite -> evar_quantify_evar_open in Htmp.
      2: { simpl. unfold evar_is_fresh_in in Hx1'. clear -Hx1'. set_solver. }
      apply pf_iff_proj1 in Htmp; auto.
      eapply syllogism_intro.
      5: apply S10.
      all: auto.
    }

    eapply syllogism_intro.
    5: apply S14.
    all: auto.
    Unshelve. all: auto 10.
    
  Defined.

  Lemma phi_impl_defined_phi Γ ϕ:
    theory ⊆ Γ ->
    well_formed ϕ ->
    Γ ⊢ ϕ ---> ⌈ ϕ ⌉.
  Proof.
    intros HΓ wfϕ.
    replace ϕ with (subst_ctx box ϕ) at 1 by reflexivity.
    apply in_context_impl_defined; assumption.
  Defined.

  Lemma total_phi_impl_phi Γ ϕ:
    theory ⊆ Γ ->
    well_formed ϕ ->
    Γ ⊢ ⌊ ϕ ⌋ ---> ϕ.
  Proof.
    intros HΓ wfϕ.
    unfold patt_total.
    pose proof (Htmp := @phi_impl_defined_phi Γ (! ϕ) HΓ ltac:(auto)).
    apply A_impl_not_not_B_meta; auto.
  Defined.
    
  
    Theorem deduction_theorem_noKT Γ ϕ ψ (pf : Γ ∪ {[ ψ ]} ⊢ ϕ) :
      well_formed ϕ ->
      well_formed ψ ->
      theory ⊆ Γ ->
      uses_ex_gen (free_evars ψ) pf = false ->
      uses_svar_subst (free_svars ψ) pf = false ->
      uses_kt pf = false ->
      Γ ⊢ ⌊ ψ ⌋ ---> ϕ.
    Proof.
      intros wfϕ wfψ HΓ HnoExGen HnoSvarSubst HnoKT.
      induction pf.
      - (* hypothesis *)
        (* We could use [apply elem_of_union in e; destruct e], but that would be analyzing Prop
           when building Set, which is prohibited. *)
        destruct (decide (axiom0 = ψ)).
        + subst. apply total_phi_impl_phi; auto.
        + assert (axiom0 ∈ Γ).
          { set_solver. }
          toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
          apply (hypothesis Γ axiom0 i H).
      - (* P1 *)
        toMyGoal. do 3 mgIntro. mgExactn 1; auto 10.
      - (* P2 *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply P2; auto.
      - (* P3 *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply P3; auto.
      - (* Modus Ponens *)
        assert (well_formed phi2).
        { unfold well_formed, well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto.
        }
        simpl in HnoExGen. apply orb_false_iff in HnoExGen.
        destruct HnoExGen as [HnoExGen1 HnoExGen2].
        simpl in HnoSvarSubst. apply orb_false_iff in HnoSvarSubst.
        destruct HnoSvarSubst as [HnoSvarSubst1 HnoSvarSubst2].
        simpl in HnoKT. apply orb_false_iff in HnoKT.
        destruct HnoKT as [HnoKT1 HnoKT2].
        specialize (IHpf1 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        specialize (IHpf2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        
        toMyGoal. mgIntro.
        mgAdd IHpf2; auto.
        mgAssert ((phi1 ---> phi2)).
        { mgApply 0; auto 10. mgExactn 1; auto 10. }
        mgApply 2; auto 10.
        mgAdd IHpf1; auto.
        mgApply 0; auto 10.
        mgExactn 2; auto 10.
      - (* Existential Quantifier *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Ex_quan.
      - (* Existential Generalization *)
        simpl in HnoExGen.
        case_match;[congruence|].
        feed specialize IHpf.
        { auto. }
        { exact HnoExGen. }
        { simpl in HnoSvarSubst. exact HnoSvarSubst. }
        { simpl in HnoKT. exact HnoKT. }

        apply reorder_meta in IHpf; auto.
        apply reorder_meta; auto.
        { wf_auto2. }
        apply Ex_gen with (x0 := x) in IHpf; auto.
        { simpl. clear -n n0. set_solver. }
      - (* Propagation of ⊥, left *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_bott_left; assumption.
      - (* Propagation of ⊥, right *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_bott_right; assumption.
      - (* Propagation of 'or', left *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_disj_left; assumption.
      - (* Propagation of 'or', right *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_disj_right; assumption.
      - (* Propagation of 'exists', left *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_ex_left; assumption.
      - (* Propagation of 'exists', right *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_ex_right; assumption.
      - (* Framing left *)
        assert (well_formed (phi1)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }

        assert (well_formed (phi2)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }

        assert (well_formed (psi)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }
        
        assert (well_formed (phi1 ---> phi2)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }
        simpl in HnoExGen. simpl in HnoSvarSubst. simpl in HnoKT.
        specialize (IHpf ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        assert (S2: Γ ⊢ phi1 ---> (phi2 or ⌈ ! ψ ⌉)).
        { toMyGoal. mgAdd IHpf; auto 10. mgIntro.
          mgAdd (@A_or_notA Σ Γ (⌈ ! ψ ⌉) ltac:(auto)); auto 10.
          mgDestruct 0; auto.
          - mgRight; auto 10. mgExactn 0; auto 10.
          - mgLeft; auto 10.
            mgAssert((phi1 ---> phi2)).
            { mgApply 1; auto 10. mgExactn 0; auto 10. }
            mgApply 3; auto 10. mgExactn 2; auto 10.
        }

        assert (S3: Γ ⊢ (⌈ ! ψ ⌉ $ psi) ---> ⌈ ! ψ ⌉).
        {
          replace (⌈ ! ψ ⌉ $ psi)
            with (subst_ctx (@ctx_app_l _ AC_patt_defined psi ltac:(assumption)) (! ψ))
            by reflexivity.
          apply in_context_impl_defined; auto.
        }

        assert (S4: Γ ⊢ (phi1 $ psi) ---> ((phi2 or ⌈ ! ψ ⌉) $ psi)).
        { apply Framing_left. exact S2. }

        assert (S5: Γ ⊢ (phi1 $ psi) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
        {
          pose proof (Htmp := @prf_prop_or_iff Σ Γ (@ctx_app_l _ box psi ltac:(assumption)) phi2 (⌈! ψ ⌉)).
          feed specialize Htmp.
          { auto. }
          { auto. }
          simpl in Htmp.
          apply pf_iff_proj1 in Htmp; auto.
          eapply syllogism_intro.
          5: apply Htmp.
          all: auto 10.
        }
        
        assert (S6: Γ ⊢ ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉))).
        {
          toMyGoal. mgIntro. mgAdd S3; auto 10.
          mgAdd (@A_or_notA Σ Γ (phi2 $ psi) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          - mgLeft; auto 10. mgExactn 0; auto 10.
          - mgRight; auto 10. mgApply 1; auto 10. mgApply 2; auto 10. mgExactn 0; auto 10.
        }

        assert (S7: Γ ⊢ (phi1 $ psi) ---> ((phi2 $ psi)  or ⌈ ! ψ ⌉)).
        {
          toMyGoal. mgAdd S5; auto 10. mgAdd S6; auto 10. mgIntro.
          mgAssert (((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
          { mgApply 1; auto 10. mgExactn 2; auto 10. }
          mgDestruct 3; auto 10.
          - mgLeft; auto 10. mgExactn 3; auto 10.
          - mgApply 0; auto 10. mgRight; auto 10. mgExactn 3; auto 15.
        }

        toMyGoal. do 2 mgIntro. mgAdd S7; auto 10.
        mgAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
        { mgApply 0; auto 10. mgExactn 2; auto 10. }
        mgDestruct 3; auto 10.
        + mgExactn 3; auto 10.
        + mgAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
          { mgApply 0; auto 10. mgExactn 2; auto 10. }
          mgAdd (@A_or_notA Σ Γ (phi2 $ psi) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          * mgExactn 0; auto 15.
          * mgAdd (@bot_elim Σ Γ (phi2 $ psi) ltac:(auto)); auto 15.
            mgApply 0; auto 15.
            mgApply 3; auto 15.
            mgExactn 5; auto 15.
      - (* Framing right *)
        assert (well_formed (phi1)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }

        assert (well_formed (phi2)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }

        assert (well_formed (psi)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }
        
        assert (well_formed (phi1 ---> phi2)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }
        simpl in HnoExGen. simpl in HnoSvarSubst. simpl in HnoKT.
        specialize (IHpf ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        assert (S2: Γ ⊢ phi1 ---> (phi2 or ⌈ ! ψ ⌉)).
        { toMyGoal. mgAdd IHpf; auto 10. mgIntro.
          mgAdd (@A_or_notA Σ Γ (⌈ ! ψ ⌉) ltac:(auto)); auto 10.
          mgDestruct 0; auto.
          - mgRight; auto 10. mgExactn 0; auto 10.
          - mgLeft; auto 10.
            mgAssert((phi1 ---> phi2)).
            { mgApply 1; auto 10. mgExactn 0; auto 10. }
            mgApply 3; auto 10. mgExactn 2; auto 10.
        }

        assert (S3: Γ ⊢ (psi $ ⌈ ! ψ ⌉) ---> ⌈ ! ψ ⌉).
        {
          replace (psi $ ⌈ ! ψ ⌉)
            with (subst_ctx (@ctx_app_r _ psi AC_patt_defined ltac:(assumption)) (! ψ))
            by reflexivity.
          apply in_context_impl_defined; auto.
        }

        assert (S4: Γ ⊢ (psi $ phi1) ---> (psi $ (phi2 or ⌈ ! ψ ⌉))).
        { apply Framing_right. exact S2. }

        assert (S5: Γ ⊢ (psi $ phi1) ---> ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
        {
          pose proof (Htmp := @prf_prop_or_iff Σ Γ (@ctx_app_r _ psi box ltac:(assumption)) phi2 (⌈! ψ ⌉)).
          feed specialize Htmp.
          { auto. }
          { auto. }
          simpl in Htmp.
          apply pf_iff_proj1 in Htmp; auto.
          eapply syllogism_intro.
          5: apply Htmp.
          all: auto 10.
        }
        
        assert (S6: Γ ⊢ ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) ---> ((psi $ phi2) or (⌈ ! ψ ⌉))).
        {
          toMyGoal. mgIntro. mgAdd S3; auto 10.
          mgAdd (@A_or_notA Σ Γ (psi $ phi2) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          - mgLeft; auto 10. mgExactn 0; auto 10.
          - mgRight; auto 10. mgApply 1; auto 10. mgApply 2; auto 10. mgExactn 0; auto 10.
        }

        assert (S7: Γ ⊢ (psi $ phi1) ---> ((psi $ phi2)  or ⌈ ! ψ ⌉)).
        {
          toMyGoal. mgAdd S5; auto 10. mgAdd S6; auto 10. mgIntro.
          mgAssert (((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
          { mgApply 1; auto 10. mgExactn 2; auto 10. }
          mgDestruct 3; auto 10.
          - mgLeft; auto 10. mgExactn 3; auto 10.
          - mgApply 0; auto 10. mgRight; auto 10. mgExactn 3; auto 15.
        }

        toMyGoal. do 2 mgIntro. mgAdd S7; auto 10.
        mgAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
        { mgApply 0; auto 10. mgExactn 2; auto 10. }
        mgDestruct 3; auto 10.
        + mgExactn 3; auto 10.
        + mgAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
          { mgApply 0; auto 10. mgExactn 2; auto 10. }
          mgAdd (@A_or_notA Σ Γ (psi $ phi2) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          * mgExactn 0; auto 15.
          * mgAdd (@bot_elim Σ Γ (psi $ phi2) ltac:(auto)); auto 15.
            mgApply 0; auto 15.
            mgApply 3; auto 15.
            mgExactn 5; auto 15.
      - (* Set variable substitution *)
        simpl in HnoExGen. simpl in HnoSvarSubst. simpl in IHpf.
        case_match.
        { congruence. }
        specialize (IHpf ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        replace (⌊ ψ ⌋ ---> free_svar_subst phi psi X)
          with (free_svar_subst (⌊ ψ ⌋ ---> phi) psi X).
        2: { unfold free_svar_subst. simpl.
             rewrite [free_svar_subst' 0 ψ psi X]free_svar_subst_fresh.
             { assumption. }
             reflexivity.
        }
        apply Svar_subst; auto.
      - (* Prefixpoint *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Pre_fixp.
      - (* Knaster-Tarski *)
        simpl in HnoKT. congruence.
      - (* Existence *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Existence.
      - (* Singleton *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Singleton_ctx.

        Unshelve. all: auto 10.
    Defined.

    Lemma membership_introduction Γ ϕ:
      well_formed ϕ ->
      theory ⊆ Γ ->
      Γ ⊢ ϕ ->
      Γ ⊢ all, ((patt_bound_evar 0) ∈ml ϕ).
    Proof.
      intros wfϕ HΓ Hϕ.

      remember (fresh_evar ϕ) as x.

      replace ϕ with (evar_quantify x 0 ϕ).
      2: {
        rewrite evar_quantify_fresh.
        subst; auto. reflexivity.
      }
      
      
      assert (S2: Γ ⊢ (ϕ ---> (patt_free_evar x ---> ϕ))).
      {
        apply P1; auto.
      }

      assert(S3: Γ ⊢ patt_free_evar x ---> ϕ).
      {
        eapply Modus_ponens. 4: apply S2. all: auto.
      }

      assert(S4: Γ ⊢ patt_free_evar x ---> patt_free_evar x).
      {
        apply A_impl_A; auto.
      }

      assert(S5: Γ ⊢ patt_free_evar x ---> (patt_free_evar x and ϕ)).
      {
        toMyGoal. mgIntro. unfold patt_and. mgIntro.
        mgAssert ((! ϕ)).
        { mgApply 1; auto 10. mgIntro. mgApply 2; auto 10. mgExactn 0; auto 10.  }
        mgApply 2; auto 10.
        mgAdd Hϕ; auto 10. mgExactn 0; auto 10.
      }

      assert(S6: Γ ⊢ ⌈ patt_free_evar x ⌉ ---> ⌈ (patt_free_evar x and ϕ) ⌉).
      {
        apply Framing_right. assumption.
      }
      
      assert(S7: Γ ⊢ ⌈ patt_free_evar x ⌉).
      {
        apply defined_evar; assumption.
      }

      assert(S9: Γ ⊢ (patt_free_evar x) ∈ml ϕ).
      {
        eapply Modus_ponens. 4: apply S6. all: auto 15.
      }

      eapply universal_generalization with (x0 := x) in S9; auto.
      simpl in S9. case_match;[|congruence]. exact S9.
      Unshelve. all: auto 10.
    Defined.

    Lemma membership_elimination Γ ϕ:
      well_formed ϕ ->
      theory ⊆ Γ ->
      Γ ⊢ all, ((patt_bound_evar 0) ∈ml ϕ) ->
      Γ ⊢ ϕ.
    Proof.
      intros wfϕ HΓ H.

      remember (fresh_evar ϕ) as x.
      assert(S1: Γ ⊢ all, ((patt_bound_evar 0) ∈ml (evar_quantify x 0 ϕ))).
      {
        rewrite evar_quantify_fresh.
        { subst x.  apply set_evar_fresh_is_fresh'. }
        assumption.
      }
      
      assert(S2: Γ ⊢ (all, ((patt_bound_evar 0) ∈ml (evar_quantify x 0 ϕ))) ---> (patt_free_evar x ∈ml ϕ)).
      {
        replace (b0 ∈ml evar_quantify x 0 ϕ)
          with (evar_quantify x 0 (patt_free_evar x ∈ml ϕ))
        .
        2: {
          simpl. case_match;[|congruence]. reflexivity.
        }
        apply forall_variable_substitution; auto.
      }

      assert(well_formed (all , b0 ∈ml evar_quantify x 0 ϕ)).
      {
        unfold well_formed,well_formed_closed in *. simpl.
        destruct_and!. split_and!; auto.
      }
      
      
      assert(S3: Γ ⊢ patt_free_evar x ∈ml ϕ).
      {
        eapply Modus_ponens. 4: apply S2. all: auto.
      }

      pose proof (S5 := Singleton_ctx Γ AC_patt_defined box ϕ x).
      simpl in S5.

      assert (S6: Γ ⊢ ⌈ patt_free_evar x and ϕ ⌉ ---> (patt_free_evar x ---> ϕ) ).
      {
        toMyGoal. mgIntro. mgIntro.
        mgAdd S5; auto 10. unfold patt_and at 1. unfold patt_or at 1.
        mgAssert((! ! patt_sym (inj definedness) $ (patt_free_evar x and ϕ) ---> ! (patt_free_evar x and ! ϕ)))
        using first 1.
        {
          remember ((! ! patt_sym (inj definedness) $ (patt_free_evar x and ϕ) ---> ! (patt_free_evar x and ! ϕ)))
            as A.
          fromMyGoal. apply not_not_elim; subst; auto 10.
        }
        mgClear 0; auto 10.

        mgAssert((! (patt_free_evar x and ! ϕ))) using first 2.
        {
          mgApply 0; auto 10. mgClear 0; auto 10.
          fromMyGoal. apply not_not_intro; auto 10.
        }
        mgClear 0; auto 10. mgClear 0; auto 10.

        unfold patt_and.
        mgAssert ((! patt_free_evar x or ! ! ϕ)) using first 1.
        {
          fromMyGoal. apply not_not_elim; auto 10.
        }
        mgClear 0; auto 10.

        unfold patt_or.
        mgApplyMeta (@not_not_elim Σ _ _ _); auto 10.
        mgApply 0; auto 10.
        mgApplyMeta (@not_not_intro Σ _ _ _); auto 10.
        mgExactn 1.
        Unshelve. all: auto 15.
      }

      assert (S7: Γ ⊢ patt_free_evar x ---> ϕ).
      {
        eapply Modus_ponens. 4: apply S6. all: auto.
      }

      pose proof (S8 := S7).
      apply universal_generalization with (x0 := x) in S8; auto.

      assert (S9: Γ ⊢ (ex, patt_bound_evar 0) ---> ϕ).
      {
        unfold patt_forall in S8.
        simpl in S8.
        case_match; [|congruence].
        
        replace b0 with (evar_quantify x 0 (patt_free_evar x)).
        2: { simpl. case_match; [|congruence]. reflexivity. }
        
        apply Ex_gen; auto.
      }

      eapply Modus_ponens.
      4: apply S9.
      3: apply Existence.
      all: auto.
    Defined.

    Lemma membership_not_1 Γ ϕ x:
      well_formed ϕ ->
      theory ⊆ Γ ->
      Γ ⊢ ((patt_free_evar x) ∈ml (! ϕ)) ---> ! ((patt_free_evar x) ∈ml ϕ).
    Proof.
      intros Hwf HΓ.
      
      pose proof (S1 := Singleton_ctx Γ AC_patt_defined AC_patt_defined ϕ x).
      simpl in S1.

      assert (S2: Γ ⊢ ⌈ patt_free_evar x and ! ϕ ⌉ ---> ! ⌈ patt_free_evar x and ϕ ⌉).
      {

        replace (patt_sym (inj definedness) $ (patt_free_evar x and ϕ))
          with (⌈ patt_free_evar x and ϕ ⌉) in S1 by reflexivity.

        replace (patt_sym (inj definedness) $ (patt_free_evar x and ! ϕ))
          with (⌈ patt_free_evar x and ! ϕ ⌉) in S1 by reflexivity.
        
        toMyGoal. mgIntro. mgAdd S1; auto 10.
        unfold patt_and at 1.
        mgAssert ((! ⌈ patt_free_evar x and ϕ ⌉ or ! ⌈ patt_free_evar x and ! ϕ ⌉))
                 using first 1.
        
        {
          fromMyGoal.
          apply not_not_elim; auto 10.
        }
        mgClear 0; auto 10.

        (* Symmetry of Or *)
        mgAssert ((! ⌈ patt_free_evar x and ! ϕ ⌉ or ! ⌈ patt_free_evar x and ϕ ⌉))
                 using first 1.
        {
          mgAdd (@A_or_notA Σ Γ (! ⌈ patt_free_evar x and ϕ ⌉) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          - mgRight; auto 10. mgExactn 0; auto 10.
          - mgLeft; auto 10. mgApply 1; auto 10. mgExactn 0; auto 10.
        }
        mgClear 0; auto 10.

        mgApply 0; auto 10. mgClear 0; auto 10. fromMyGoal.
        apply not_not_intro; auto 10.
      }
      apply S2.
      Unshelve. all: auto 15.
    Qed.

    Lemma membership_not_2 Γ (ϕ : Pattern) x:
      well_formed ϕ = true ->
      theory ⊆ Γ ->
      Γ ⊢ ((!(patt_free_evar x ∈ml ϕ)) ---> (patt_free_evar x ∈ml (! ϕ)))%ml.
    Proof.
      intros wfϕ HΓ.
      pose proof (S1 := @defined_evar Γ x HΓ).
      assert (S2: Γ ⊢ ⌈ (patt_free_evar x and ϕ) or (patt_free_evar x and (! ϕ)) ⌉).
      {
        assert(H: Γ ⊢ (patt_free_evar x ---> ((patt_free_evar x and ϕ) or (patt_free_evar x and (! ϕ))))).
        {
          toMyGoal. mgIntro. mgAdd (@A_or_notA Σ Γ ϕ ltac:(auto)); auto.
          mgDestruct 0; auto.
          - mgLeft; auto 10. unfold patt_and. mgIntro. unfold patt_or.
            mgAssert ((! ϕ)).
            {
              mgApply 2; auto 10. mgClear 0; auto 10. mgClear 1; auto. fromMyGoal.
              apply not_not_intro; auto.
            }
            mgApply 3; auto 10. mgExactn 0; auto 10.
          - mgRight; auto 10. unfold patt_and. mgIntro. unfold patt_or.
            mgApply 0; auto 10. mgApplyMeta (@not_not_elim Σ Γ ϕ ltac:(auto)); auto 10.
            mgApply 2; auto 10. mgIntro. mgApply 3; auto 10. mgExactn 1; auto 10.
        }
        eapply Framing_right in H.
        eapply Modus_ponens. 4: apply H. all: auto 10.
      }

      pose proof (Htmp := @prf_prop_or_iff Σ Γ AC_patt_defined (patt_free_evar x and ϕ) (patt_free_evar x and ! ϕ)
                                          ltac:(auto) ltac:(auto)).
      simpl in Htmp.
      apply pf_iff_proj1 in Htmp; auto 10.
      eapply Modus_ponens.
      4: apply Htmp.
      all: auto 10.
      Unshelve. all: auto 10.
    Defined.

    Lemma membership_not_iff Γ ϕ x:
      well_formed ϕ ->
      theory ⊆ Γ ->
      Γ ⊢ ((patt_free_evar x) ∈ml (! ϕ)) <---> ! ((patt_free_evar x) ∈ml ϕ).
    Proof.
      intros Hwf HΓ.
      apply pf_iff_split; auto 10.
      - apply membership_not_1; auto 10.
      - apply membership_not_2; auto 10.
    Defined.
    
    Lemma membership_or_1 Γ x ϕ₁ ϕ₂:
      well_formed ϕ₁ ->
      well_formed ϕ₂ ->
      theory ⊆ Γ ->
      Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ or ϕ₂)) ---> ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂)).
    Proof.
      intros wfϕ₁ wfϕ₂ HΓ.
      unfold patt_in.
      eapply syllogism_intro.
      5: apply Prop_disj_right; auto 10.
      all: auto 10.
      apply Framing_right.
      toMyGoal. mgIntro. mgDestructAnd 0; auto 10.
      mgDestruct 1; auto 10.
      - mgLeft; auto 10. unfold patt_and. mgIntro.
        mgDestruct 2; auto 10.
        + mgApply 2; auto 10. mgExactn 0; auto 10.
        + mgApply 2; auto 10. mgExactn 1; auto 10.
      - mgRight; auto 10. unfold patt_and. mgIntro.
        mgDestruct 2; auto 10.
        + mgApply 2; auto 10. mgExactn 0; auto 10.
        + mgApply 2; auto 10. mgExactn 1; auto 10.
    Defined.

    Lemma membership_or_2 Γ x ϕ₁ ϕ₂:
      well_formed ϕ₁ ->
      well_formed ϕ₂ ->
      theory ⊆ Γ ->
      Γ ⊢ ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂)) ---> (patt_free_evar x ∈ml (ϕ₁ or ϕ₂)).
    Proof.
      intros wfϕ₁ wfϕ₂ HΓ.
      unfold patt_in.
      pose proof (H1 := @prf_prop_or_iff Σ Γ AC_patt_defined (patt_free_evar x and ϕ₁) (patt_free_evar x and ϕ₂)
                                        ltac:(auto) ltac:(auto)).
      apply pf_iff_proj2 in H1; auto 10.
      eapply syllogism_intro.
      4: apply H1.
      all: auto.
      simpl.
      apply Framing_right.

      toMyGoal. mgIntro. mgDestruct 0; auto 10; mgDestructAnd 0; auto 10.
      - unfold patt_and. mgIntro. mgDestruct 2; auto 10.
        + mgApply 2; auto 10. mgExactn 0; auto 10.
        + mgApply 2; auto 10. mgLeft; auto 10. mgExactn 1; auto 10.
      - unfold patt_and. mgIntro. mgDestruct 2; auto 10.
        + mgApply 2; auto 10. mgExactn 0; auto 10.
        + mgApply 2; auto 10. mgRight; auto 10. mgExactn 1; auto 10.
    Defined.

    Lemma membership_or_iff Γ x ϕ₁ ϕ₂:
      well_formed ϕ₁ ->
      well_formed ϕ₂ ->
      theory ⊆ Γ ->
      Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ or ϕ₂)) <---> ((patt_free_evar x ∈ml ϕ₁) or (patt_free_evar x ∈ml ϕ₂)).
    Proof.
      intros wfϕ₁ wfϕ₂ HΓ.
      apply pf_iff_split; auto.
      + apply membership_or_1; auto 10.
      + apply membership_or_2; auto 10.
    Defined.

    Lemma membership_and_1 Γ x ϕ₁ ϕ₂:
      well_formed ϕ₁ ->
      well_formed ϕ₂ ->
      theory ⊆ Γ ->
      Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ and ϕ₂)) ---> ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂)).
    Proof.
      intros wfϕ₁ wfϕ₂ HΓ.
      unfold patt_and.
      toMyGoal. mgIntro.
      mgApplyMeta (membership_not_1 _ _ _) in 0; auto 10.
      mgIntro. mgApply 0; auto 10. mgClear 0; auto 10.
      mgApplyMeta (membership_or_2 _ _ _ _); auto 10.
      mgDestruct 0; auto 10.
      - mgLeft; auto 10.
        mgApplyMeta (membership_not_2 _ _ _) in 0; auto 10.
        mgExactn 0; auto.
      - mgRight; auto 10.
        mgApplyMeta (membership_not_2 _ _ _) in 0; auto 10.
        mgExactn 0; auto.
    Defined.
    
    Lemma membership_and_2 Γ x ϕ₁ ϕ₂:
      well_formed ϕ₁ ->
      well_formed ϕ₂ ->
      theory ⊆ Γ ->
      Γ ⊢ ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂)) ---> (patt_free_evar x ∈ml (ϕ₁ and ϕ₂)).
    Proof.
      intros wfϕ₁ wfϕ₂ HΓ.
      toMyGoal. mgIntro.
      mgDestructAnd 0; auto 10.
      unfold patt_and.
      mgApplyMeta (@membership_not_2 _ _ _ _ _); auto 10.
      mgIntro.
      mgApplyMeta (membership_or_1 _ _ _ _) in 2; auto 10.
      mgDestruct 2; auto 10.
      - mgApplyMeta (membership_not_1 _ _ _) in 2; auto 10.
        mgApply 2; auto 10. mgExactn 0; auto 10.
      - mgApplyMeta (membership_not_1 _ _ _) in 2; auto 10.
        mgApply 2; auto 10. mgExactn 1; auto 10.
    Defined.

    Lemma membership_and_iff Γ x ϕ₁ ϕ₂:
      well_formed ϕ₁ ->
      well_formed ϕ₂ ->
      theory ⊆ Γ ->
      Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ and ϕ₂)) <---> ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂)).
    Proof.
      intros wfϕ₁ wfϕ₂ HΓ.
      apply pf_iff_split; auto.
      + apply membership_and_1; auto 10.
      + apply membership_and_2; auto 10.
    Defined.

    Lemma membership_imp_1 Γ x ϕ₁ ϕ₂:
      well_formed ϕ₁ ->
      well_formed ϕ₂ ->
      theory ⊆ Γ ->
      Γ ⊢ (patt_free_evar x ∈ml (ϕ₁ ---> ϕ₂)) ---> ((patt_free_evar x ∈ml ϕ₁) and (patt_free_evar x ∈ml ϕ₂)).
    Proof.
      intros wfϕ₁ wfϕ₂ HΓ.
    Abort.
         
    
    Theorem deduction_theorem_general Γ ϕ ψ (pf : Γ ∪ {[ ψ ]} ⊢ ϕ) :
      well_formed ϕ ->
      well_formed ψ ->
      theory ⊆ Γ ->
      uses_ex_gen (free_evars ψ) pf = false ->
      uses_svar_subst (free_svars ψ) pf = false ->
      Γ ⊢ ⌊ ψ ⌋ ---> ϕ.
    Proof.
      intros wfϕ wfψ HΓ HnoExGen HnoSvarSubst.
      induction pf.
      - (* hypothesis *)
        (* We could use [apply elem_of_union in e; destruct e], but that would be analyzing Prop
           when building Set, which is prohibited. *)
        destruct (decide (axiom0 = ψ)).
        + subst. apply total_phi_impl_phi; auto.
        + assert (axiom0 ∈ Γ).
          { set_solver. }
          toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
          apply (hypothesis Γ axiom0 i H).
      - (* P1 *)
        toMyGoal. do 3 mgIntro. mgExactn 1; auto.
      - (* P2 *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply P2; auto.
      - (* P3 *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply P3; auto.
      - (* Modus Ponens *)
        assert (well_formed phi2).
        { unfold well_formed, well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto.
        }
        simpl in HnoExGen. apply orb_false_iff in HnoExGen.
        destruct HnoExGen as [HnoExGen1 HnoExGen2].
        simpl in HnoSvarSubst. apply orb_false_iff in HnoSvarSubst.
        destruct HnoSvarSubst as [HnoSvarSubst1 HnoSvarSubst2].
        specialize (IHpf1 ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        specialize (IHpf2 ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        
        toMyGoal. mgIntro.
        mgAdd IHpf2; auto.
        mgAssert ((phi1 ---> phi2)).
        { mgApply 0; auto 10. mgExactn 1; auto. }
        mgApply 2; auto 10.
        mgAdd IHpf1; auto.
        mgApply 0; auto 10.
        mgExactn 2; auto 10.
      - (* Existential Quantifier *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Ex_quan.
      - (* Existential Generalization *)
        simpl in HnoExGen.
        case_match;[congruence|].
        feed specialize IHpf.
        { auto. }
        { exact HnoExGen. }
        { simpl in HnoSvarSubst. exact HnoSvarSubst. }

        apply reorder_meta in IHpf; auto.
        apply reorder_meta; auto.
        { wf_auto2. }
        apply Ex_gen with (x0 := x) in IHpf; auto.
        { simpl. clear -n n0. set_solver. }
      - (* Propagation of ⊥, left *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_bott_left; assumption.
      - (* Propagation of ⊥, right *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_bott_right; assumption.
      - (* Propagation of 'or', left *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_disj_left; assumption.
      - (* Propagation of 'or', right *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_disj_right; assumption.
      - (* Propagation of 'exists', left *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_ex_left; assumption.
      - (* Propagation of 'exists', right *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Prop_ex_right; assumption.
      - (* Framing left *)
        assert (well_formed (phi1)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }

        assert (well_formed (phi2)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }

        assert (well_formed (psi)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }
        
        assert (well_formed (phi1 ---> phi2)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }
        simpl in HnoExGen. simpl in HnoSvarSubst.
        specialize (IHpf ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        assert (S2: Γ ⊢ phi1 ---> (phi2 or ⌈ ! ψ ⌉)).
        { toMyGoal. mgAdd IHpf; auto 10. mgIntro.
          mgAdd (@A_or_notA Σ Γ (⌈ ! ψ ⌉) ltac:(auto)); auto 10.
          mgDestruct 0; auto.
          - mgRight; auto 10. mgExactn 0; auto 10.
          - mgLeft; auto 10.
            mgAssert((phi1 ---> phi2)).
            { mgApply 1; auto 10. mgExactn 0; auto 10. }
            mgApply 3; auto 10. mgExactn 2; auto 10.
        }

        assert (S3: Γ ⊢ (⌈ ! ψ ⌉ $ psi) ---> ⌈ ! ψ ⌉).
        {
          replace (⌈ ! ψ ⌉ $ psi)
            with (subst_ctx (@ctx_app_l _ AC_patt_defined psi ltac:(assumption)) (! ψ))
            by reflexivity.
          apply in_context_impl_defined; auto.
        }

        assert (S4: Γ ⊢ (phi1 $ psi) ---> ((phi2 or ⌈ ! ψ ⌉) $ psi)).
        { apply Framing_left. exact S2. }

        assert (S5: Γ ⊢ (phi1 $ psi) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
        {
          pose proof (Htmp := @prf_prop_or_iff Σ Γ (@ctx_app_l _ box psi ltac:(assumption)) phi2 (⌈! ψ ⌉)).
          feed specialize Htmp.
          { auto. }
          { auto. }
          simpl in Htmp.
          apply pf_iff_proj1 in Htmp; auto.
          eapply syllogism_intro.
          5: apply Htmp.
          all: auto 10.
        }
        
        assert (S6: Γ ⊢ ((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi)) ---> ((phi2 $ psi) or (⌈ ! ψ ⌉))).
        {
          toMyGoal. mgIntro. mgAdd S3; auto 10.
          mgAdd (@A_or_notA Σ Γ (phi2 $ psi) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          - mgLeft; auto 10. mgExactn 0; auto 10.
          - mgRight; auto 10. mgApply 1; auto 10. mgApply 2; auto 10. mgExactn 0; auto 10.
        }

        assert (S7: Γ ⊢ (phi1 $ psi) ---> ((phi2 $ psi)  or ⌈ ! ψ ⌉)).
        {
          toMyGoal. mgAdd S5; auto 10. mgAdd S6; auto 10. mgIntro.
          mgAssert (((phi2 $ psi) or (⌈ ! ψ ⌉ $ psi))).
          { mgApply 1; auto 10. mgExactn 2; auto 10. }
          mgDestruct 3; auto 10.
          - mgLeft; auto 10. mgExactn 3; auto 10.
          - mgApply 0; auto 10. mgRight; auto 10. mgExactn 3; auto 15.
        }

        toMyGoal. do 2 mgIntro. mgAdd S7; auto 10.
        mgAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
        { mgApply 0; auto 10. mgExactn 2; auto 10. }
        mgDestruct 3; auto 10.
        + mgExactn 3; auto 10.
        + mgAssert ((phi2 $ psi or ⌈ ! ψ ⌉)).
          { mgApply 0; auto 10. mgExactn 2; auto 10. }
          mgAdd (@A_or_notA Σ Γ (phi2 $ psi) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          * mgExactn 0; auto 15.
          * mgAdd (@bot_elim Σ Γ (phi2 $ psi) ltac:(auto)); auto 15.
            mgApply 0; auto 15.
            mgApply 3; auto 15.
            mgExactn 5; auto 15.
      - (* Framing right *)
        assert (well_formed (phi1)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }

        assert (well_formed (phi2)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }

        assert (well_formed (psi)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }
        
        assert (well_formed (phi1 ---> phi2)).
        { unfold well_formed,well_formed_closed in *. simpl in *.
          destruct_and!. split_and!; auto. }
        simpl in HnoExGen. simpl in HnoSvarSubst.
        specialize (IHpf ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        assert (S2: Γ ⊢ phi1 ---> (phi2 or ⌈ ! ψ ⌉)).
        { toMyGoal. mgAdd IHpf; auto 10. mgIntro.
          mgAdd (@A_or_notA Σ Γ (⌈ ! ψ ⌉) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          - mgRight; auto 10. mgExactn 0; auto 10.
          - mgLeft; auto 10.
            mgAssert((phi1 ---> phi2)).
            { mgApply 1; auto 10. mgExactn 0; auto 10. }
            mgApply 3; auto 10. mgExactn 2; auto 10.
        }

        assert (S3: Γ ⊢ (psi $ ⌈ ! ψ ⌉) ---> ⌈ ! ψ ⌉).
        {
          replace (psi $ ⌈ ! ψ ⌉)
            with (subst_ctx (@ctx_app_r _ psi AC_patt_defined ltac:(assumption)) (! ψ))
            by reflexivity.
          apply in_context_impl_defined; auto.
        }

        assert (S4: Γ ⊢ (psi $ phi1) ---> (psi $ (phi2 or ⌈ ! ψ ⌉))).
        { apply Framing_right. exact S2. }

        assert (S5: Γ ⊢ (psi $ phi1) ---> ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
        {
          pose proof (Htmp := @prf_prop_or_iff Σ Γ (@ctx_app_r _ psi box ltac:(assumption)) phi2 (⌈! ψ ⌉)).
          feed specialize Htmp.
          { auto. }
          { auto. }
          simpl in Htmp.
          apply pf_iff_proj1 in Htmp; auto.
          eapply syllogism_intro.
          5: apply Htmp.
          all: auto 10.
        }
        
        assert (S6: Γ ⊢ ((psi $ phi2) or (psi $ ⌈ ! ψ ⌉)) ---> ((psi $ phi2) or (⌈ ! ψ ⌉))).
        {
          toMyGoal. mgIntro. mgAdd S3; auto 10.
          mgAdd (@A_or_notA Σ Γ (psi $ phi2) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          - mgLeft; auto 10. mgExactn 0; auto 10.
          - mgRight; auto 10. mgApply 1; auto 10. mgApply 2; auto 10. mgExactn 0; auto 10.
        }

        assert (S7: Γ ⊢ (psi $ phi1) ---> ((psi $ phi2)  or ⌈ ! ψ ⌉)).
        {
          toMyGoal. mgAdd S5; auto 10. mgAdd S6; auto 10. mgIntro.
          mgAssert (((psi $ phi2) or (psi $ ⌈ ! ψ ⌉))).
          { mgApply 1; auto 10. mgExactn 2; auto 10. }
          mgDestruct 3; auto 10.
          - mgLeft; auto 10. mgExactn 3; auto 10.
          - mgApply 0; auto 10. mgRight; auto 10. mgExactn 3; auto 15.
        }

        toMyGoal. do 2 mgIntro. mgAdd S7; auto 10.
        mgAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
        { mgApply 0; auto 10. mgExactn 2; auto 10. }
        mgDestruct 3; auto 10.
        + mgExactn 3; auto 10.
        + mgAssert ((psi $ phi2 or ⌈ ! ψ ⌉)).
          { mgApply 0; auto 10. mgExactn 2; auto 10. }
          mgAdd (@A_or_notA Σ Γ (psi $ phi2) ltac:(auto)); auto 10.
          mgDestruct 0; auto 10.
          * mgExactn 0; auto 15.
          * mgAdd (@bot_elim Σ Γ (psi $ phi2) ltac:(auto)); auto 15.
            mgApply 0; auto 15.
            mgApply 3; auto 15.
            mgExactn 5; auto 15.
      - (* Set variable substitution *)
        simpl in HnoExGen. simpl in HnoSvarSubst. simpl in IHpf.
        case_match.
        { congruence. }
        specialize (IHpf ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        replace (⌊ ψ ⌋ ---> free_svar_subst phi psi X)
          with (free_svar_subst (⌊ ψ ⌋ ---> phi) psi X).
        2: { unfold free_svar_subst. simpl.
             rewrite [free_svar_subst' 0 ψ psi X]free_svar_subst_fresh.
             { assumption. }
             reflexivity.
        }
        apply Svar_subst; auto.
      - (* Prefixpoint *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Pre_fixp.
      - (* Knaster-Tarski *)
        (*Print ML_proof_system.*)
        admit.
      - (* Existence *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Existence.
      - (* Singleton *)
        toMyGoal. mgIntro. mgClear 0; auto. fromMyGoal.
        apply Singleton_ctx.

        Unshelve. all: auto 10.
    Abort.




    Lemma equality_elimination_basic Γ φ1 φ2 C :
      theory ⊆ Γ ->
      well_formed φ1 -> well_formed φ2 ->
      PC_wf C ->
      mu_free (pcPattern C) ->
      Γ ⊢ (φ1 =ml φ2) ---> (* somewhere "and" is here, somewhere meta-implication *)
        (emplace C φ1) <---> (emplace C φ2).
    Proof.
      intros HΓ WF1 WF2 WFC Hmf.

      unshelve(eapply deduction_theorem_noKT).
      remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
      assert (Γ' ⊢ (φ1 <---> φ2)). {
        apply hypothesis.
        - abstract (now apply well_formed_iff).
        - abstract (rewrite HeqΓ'; apply elem_of_union_r; constructor).
      }
      eapply prf_equiv_congruence.
      all: try assumption.
      all: try (abstract auto).
      { 
        abstract (
          apply well_formed_and; apply well_formed_imp; unfold emplace;
          apply well_formed_free_evar_subst_0; auto
        ).
      }
      3: {
        abstract(
          simpl; unfold prf_equiv_congruence; destruct C as [ψ E]; simpl;
          rewrite uses_kt_nomu_eq_prf_equiv_congruence;[apply Hmf|reflexivity|reflexivity]
        ).
      }
      2: {
        abstract (
          simpl;
          unfold prf_equiv_congruence; destruct C as [ψ E];
          simpl;
          match goal with
          | [ |- uses_svar_subst ?S _ = false ]
            => replace S with (free_svars φ1 ∪ free_svars φ2) by (clear; set_solver)
          end;
          rewrite uses_svar_subst_eq_prf_equiv_congruence;
          [(clear;set_solver)|reflexivity|reflexivity]
        ).
      }
      1: {
        abstract (
          simpl;
          unfold prf_equiv_congruence; destruct C as [ψ E];
          match goal with
          | [ |- uses_ex_gen ?e _ = false ]
            => replace e with (free_evars φ1 ∪ free_evars φ2) by (clear; set_solver)
          end;
          simpl;
          rewrite uses_ex_gen_eq_prf_equiv_congruence;
            [(clear; set_solver)|reflexivity|reflexivity]
        ).
      }
     
    Defined.
  

    Lemma equality_elimination_helper Γ φ1 φ2 ψ x :
      theory ⊆ Γ ->
      mu_free ψ ->
      well_formed φ1 -> well_formed φ2 -> well_formed ψ ->     
      Γ ⊢ (φ1 =ml φ2) ---> 
        (free_evar_subst ψ φ1 x) ---> (free_evar_subst ψ φ2 x).
    Proof.
      intros HΓ MF WF1 WF2 WFψ.
      unshelve (eapply (deduction_theorem_noKT)); try assumption.
      2,3: abstract(auto).

      remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
      assert (Γ' ⊢ (φ1 <---> φ2)). {
        apply hypothesis.
        - abstract (now apply well_formed_iff).
        - abstract (rewrite HeqΓ'; apply elem_of_union_r; constructor).
      }
      apply pf_iff_proj1; auto.

      apply (@eq_prf_equiv_congruence Σ Γ' φ1 φ2 WF1 WF2 (free_evars ψ ∪ free_evars φ1 ∪ free_evars φ2)
          (free_svars ψ ∪ free_svars φ1 ∪ free_svars φ2)); auto.
      3: {
        abstract (
          simpl; rewrite orbF;
          rewrite uses_kt_nomu_eq_prf_equiv_congruence;
          [apply MF|reflexivity|reflexivity]
        ).
      }
      2: {
        abstract (
          simpl; rewrite orbF;
          match goal with
          | [ |- uses_svar_subst ?S _ = false ]
            => replace S with (free_svars φ1 ∪ free_svars φ2) by (clear; set_solver)
          end;
          rewrite uses_svar_subst_eq_prf_equiv_congruence;
          [(clear;set_solver)|reflexivity|reflexivity]
       ).
      }
      1: {
        abstract (
          simpl; rewrite orbF;
          match goal with
          | [ |- uses_ex_gen ?e _ = false ]
            => replace e with (free_evars φ1 ∪ free_evars φ2) by (clear; set_solver)
          end;
          simpl;
          rewrite uses_ex_gen_eq_prf_equiv_congruence;
            [(clear; set_solver)|reflexivity|reflexivity]
        ).
      }
    Defined.


    Corollary equality_elimination2 Γ φ1 φ2 ψ:
      theory ⊆ Γ ->
      mu_free ψ ->
      well_formed φ1 -> well_formed φ2 -> wf_body_ex ψ ->
      Γ ⊢ (φ1 =ml φ2) ---> 
        (bevar_subst ψ φ1 0) ---> (bevar_subst ψ φ2 0).
    Proof.
      intros HΓ MF WF1 WF2 WFB. remember (fresh_evar ψ) as x.
      assert (x ∉ free_evars ψ) by now apply x_eq_fresh_impl_x_notin_free_evars.
      rewrite (@bound_to_free_variable_subst _ ψ x 1 0 φ1 0).
      { lia. }
      { unfold well_formed,well_formed_closed in *. destruct_and!. assumption. }
      { apply wf_body_ex_to_wf in WFB. unfold well_formed,well_formed_closed in *. destruct_and!. assumption. }
      { assumption. }
      rewrite (@bound_to_free_variable_subst _ ψ x 1 0 φ2 0).
      { lia. }
      { unfold well_formed,well_formed_closed in *. destruct_and!. assumption. }
      { apply wf_body_ex_to_wf in WFB. unfold well_formed,well_formed_closed in *. destruct_and!. assumption. }
      { assumption. }
      apply equality_elimination_helper; auto.
      { now apply mu_free_evar_open. }
    Defined.

    Lemma patt_eq_sym Γ φ1 φ2:
      theory ⊆ Γ ->
      well_formed φ1 -> well_formed φ2 ->
      Γ ⊢ φ1 =ml φ2 ---> φ2 =ml φ1.
    Proof.
      intros HΓ WF1 WF2.
      unshelve (eapply deduction_theorem_noKT).
      2,3,4: auto.
      remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
      assert (Γ' ⊢ (φ1 <---> φ2)). {
        apply hypothesis. apply well_formed_iff; auto.
        rewrite HeqΓ'. apply elem_of_union_r. constructor.
      }
      apply pf_iff_equiv_sym in H; auto.
      apply patt_iff_implies_equal; auto.
      all: reflexivity.
    Qed.

    Lemma evar_quantify_equal_simpl : forall φ1 φ2 x n,
        evar_quantify x n (φ1 =ml φ2) = (evar_quantify x n φ1) =ml (evar_quantify x n φ2).
    Proof. auto. Qed.

    Lemma exists_functional_subst φ φ' Γ :
      theory ⊆ Γ ->
      mu_free φ -> well_formed φ' -> wf_body_ex φ ->
      Γ ⊢ ((instantiate (patt_exists φ) φ') and (patt_exists (patt_equal φ' (patt_bound_evar 0)))) ---> (patt_exists φ).
    Proof.
      intros HΓ MF WF WFB.
      pose proof (WFϕ := wf_body_ex_to_wf WFB).
      remember (fresh_evar (φ $ φ')) as Zvar.
      remember (patt_free_evar Zvar) as Z.
      assert (well_formed Z) as WFZ. { rewrite HeqZ. auto. }
                                     assert (Γ ⊢ (patt_equal φ' Z <---> patt_equal Z φ')). {
        pose proof (SYM1 := @patt_eq_sym Γ φ' Z ltac:(auto) ltac:(auto) WFZ).
        pose proof (SYM2 := @patt_eq_sym Γ Z φ' ltac:(assumption) WFZ ltac:(auto)).
        apply pf_iff_split; auto. 
      }
      assert (well_formed (instantiate (ex , φ) φ')) as WF1. {
        unfold instantiate.
        unfold well_formed, well_formed_closed.
        apply andb_true_iff in WF as [E1 E2]. simpl in E1, E2.
        apply wf_body_ex_to_wf in WFB.
        apply andb_true_iff in WFB as [E3 E4]. simpl in E3, E4.
        unfold well_formed_closed in *. destruct_and!.
        erewrite bevar_subst_closed_mu, bevar_subst_positive, bevar_subst_closed_ex; auto.
      }
      assert (well_formed (instantiate (ex , φ) Z)) as WF2. {
        unfold instantiate.
        unfold well_formed, well_formed_closed.
        apply andb_true_iff in WF as [E1 E2]. simpl in E1, E2.
        apply wf_body_ex_to_wf in WFB.
        apply andb_true_iff in WFB as [E3 E4]. simpl in E3, E4.
        unfold well_formed_closed in *. destruct_and!.
        erewrite bevar_subst_closed_mu, bevar_subst_positive, bevar_subst_closed_ex; auto.
        all: rewrite HeqZ; auto.
      }
      pose proof (@equality_elimination2 Γ φ' Z φ HΓ MF WF WFZ WFB).
      apply pf_iff_iff in H. destruct H.
      pose proof (EQ := Ex_quan Γ φ Zvar).
      epose proof (PC := @prf_conclusion Σ Γ (patt_equal φ' Z) (instantiate (ex , φ) (patt_free_evar Zvar) ---> ex , φ) ltac:(apply well_formed_equal;auto) _ EQ).
      2-3: apply well_formed_equal;auto.
      assert (Γ
                ⊢ patt_equal φ' Z ---> instantiate (ex , φ) φ' ---> ex , φ) as HSUB. {
        pose proof (EE := @equality_elimination2 Γ φ' Z φ HΓ
                                                 ltac:(auto) ltac:(auto) ltac:(auto) WFB).
        unfold instantiate in EE.
        epose proof (PSP := @prf_strenghten_premise Σ Γ ((patt_equal φ' Z) and (instantiate (ex , φ) Z))
                                                   ((patt_equal φ' Z) and (instantiate (ex , φ) φ'))
                                                   (ex , φ) _ _ _).
        eapply Modus_ponens. 4: apply and_impl.
        all: auto.
        { wf_auto2. }
        eapply Modus_ponens. 4: eapply Modus_ponens.
        7: exact PSP.
        1,2,4,5: wf_auto2.
        * unshelve (epose proof (AI := @and_impl' Σ Γ (patt_equal φ' Z) (bevar_subst φ Z 0) (ex , φ) _ _ _)).
          1,2,3: auto.
          unfold instantiate. eapply Modus_ponens. 4: exact AI.
          1, 2: unfold patt_equal, patt_iff, patt_total, patt_defined; wf_auto2.
          rewrite <- HeqZ in PC.
          exact PC.
        * apply and_drop. 1-3: auto.
          unshelve(epose proof (AI := @and_impl' Σ Γ (patt_equal φ' Z) (instantiate (ex , φ) φ') (instantiate (ex , φ) Z) _ _ _)); auto.
          eapply Modus_ponens. 4: exact AI. 3: exact EE.
          1-2: auto 10.
      }
      eapply Modus_ponens. 4: apply and_impl'; auto.
      1,2,4: unfold instantiate,patt_equal,patt_total,patt_defined in *; wf_auto2.
      apply reorder_meta; auto.
      { wf_auto2. }
      eapply (Ex_gen Γ _ _ Zvar) in HSUB. unfold exists_quantify in HSUB.
      rewrite evar_quantify_equal_simpl in HSUB.
      rewrite -> HeqZ, -> HeqZvar in HSUB. simpl evar_quantify in HSUB.
      2-3: auto.
      2: {
        rewrite HeqZvar. unfold fresh_evar. simpl.
        apply not_elem_of_union.
        split.
        - eapply stdpp_ext.not_elem_of_larger_impl_not_elem_of.
          2: { apply set_evar_fresh_is_fresh'. }
          rewrite comm.
          apply free_evars_bevar_subst.
        - eapply stdpp_ext.not_elem_of_larger_impl_not_elem_of.
          2: { apply set_evar_fresh_is_fresh'. }
          clear. set_solver.

      }
      destruct (decide ((fresh_evar (φ $ φ')) = (fresh_evar (φ $ φ')))) in HSUB;
        simpl in HSUB. 2: congruence.
      rewrite evar_quantify_free_evar_subst in HSUB; auto.

      apply count_evar_occurrences_0.
      unfold fresh_evar. simpl.
      epose (NIN := not_elem_of_union (evar_fresh (elements (free_evars φ ∪ free_evars φ'))) (free_evars φ) (free_evars φ')). destruct NIN as [NIN1 NIN2].
      epose (NIN3 := NIN1 _). destruct NIN3. auto.
      Unshelve.
      5: { unfold instantiate. simpl.
           apply set_evar_fresh_is_fresh'.
      }
      1-4: wf_auto2.
    Qed.

    Corollary forall_functional_subst φ φ' Γ :
      theory ⊆ Γ ->
      mu_free φ -> well_formed φ' -> wf_body_ex φ -> 
      Γ ⊢ ((patt_forall φ) and (patt_exists (patt_equal φ' (patt_bound_evar 0)))) ---> (bevar_subst φ φ' 0).
    Proof.
      intros HΓ MF WF WFB. unfold patt_forall.
      assert (well_formed (bevar_subst φ φ' 0)) as BWF. {
        unfold well_formed, well_formed_closed in *.
        destruct_and!.
        split_and!.
        - apply well_formed_positive_bevar_subst; auto.
          apply wf_body_ex_to_wf, andb_true_iff in WFB as [E1 E2].
          simpl in *. assumption.
        - apply wfc_mu_aux_bevar_subst; auto.
          apply wf_body_ex_to_wf, andb_true_iff in WFB as [E1 E2].
          unfold well_formed_closed in *. simpl in *.
          destruct_and!; auto.
        - apply wfc_ex_aux_bevar_subst; auto.
          apply wf_body_ex_to_wf, andb_true_iff in WFB as [E1 E2].
          unfold well_formed_closed in *. simpl in *.
          destruct_and!; auto.
      }
      assert (well_formed (ex , patt_equal φ' b0)) as SWF. {
        unfold well_formed, well_formed_closed.
        apply andb_true_iff in WF as [E1 E2]. unfold well_formed_closed in E2.
        simpl. rewrite E1.
        unfold well_formed,well_formed_closed in *. destruct_and!.
        split_and!; auto.
        - eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
        - eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
      }
      assert (well_formed (ex , (φ ---> ⊥))) as NWF. {
        apply wf_body_ex_to_wf in WFB. unfold well_formed, well_formed_closed in *.
        clear BWF SWF.
        apply andb_true_iff in WFB as [E1 E2]. simpl in *.
        destruct_and!. split_and!; auto.
      }
      unshelve (epose proof (H := @exists_functional_subst (! φ) φ' Γ HΓ _ WF _)).
      { simpl. rewrite andbT. exact MF. }
      { apply wf_body_ex_to_wf in WFB; apply wf_ex_to_wf_body; auto. }
      simpl in H.
      epose proof (H0 := @and_impl Σ _ _ _ _ _ _ _).
      eapply Modus_ponens in H0. 4: exact H. 2-3: unfold patt_equal,patt_total,patt_defined;wf_auto2.
      apply reorder_meta in H0. 2-4: auto.
      
      epose proof (H1 := @and_impl' Σ _ _ _ _ _ _ _). eapply Modus_ponens in H1. exact H1.
      1-2: shelve.
      apply reorder_meta. 1-3: shelve.
      epose proof (H2 := @P4 Σ Γ (bevar_subst φ φ' 0) (! ex , patt_not (φ)) _ _).
      clear H H1.
      epose proof (H := @prf_weaken_conclusion Σ Γ (ex , patt_equal φ' b0) ((bevar_subst φ φ' 0 ---> ⊥) ---> ex , (! φ)) ((bevar_subst φ φ' 0 ---> ⊥) ---> ! ! ex , (! φ)) _ _ _).
      eapply Modus_ponens in H. eapply Modus_ponens in H; auto.
      2-4: shelve.
      2: {
        epose proof (H1 := @prf_weaken_conclusion Σ Γ (bevar_subst φ φ' 0 ---> ⊥) (ex , (! φ)) (! ! ex , (! φ)) _ _ _). eapply Modus_ponens. 4: exact H1. 1-2: shelve.
        apply not_not_intro. shelve.
      }
      eapply syllogism_intro in H2. exact H2. all: auto.
      Unshelve.
      all: unfold patt_not; auto.
      all: repeat apply well_formed_imp; auto.
    Qed.

End ProofSystemTheorems.


#[export]
 Hint Resolve T_predicate_defined : core.
#[export]
 Hint Resolve T_predicate_total : core.
#[export]
 Hint Resolve T_predicate_subseteq : core.
#[export]
 Hint Resolve T_predicate_equals : core.
#[export]
 Hint Resolve T_predicate_in : core.
