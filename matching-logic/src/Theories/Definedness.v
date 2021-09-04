(* In this module we define the definedness symbol and use it to build derived notions
   like totality and equality.
 *)
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Coq Require Import String Ensembles.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Syntax Semantics DerivedOperators.
From MatchingLogic Require ProofSystem Helpers.FOL_helpers.
From MatchingLogic.Utils Require Import stdpp_ext.

From stdpp Require Import base fin_sets sets propset.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.

Open Scope ml_scope.

(* We have only one symbol *)
Inductive Symbols := definedness.

Instance Symbols_eqdec : EqDecision Symbols.
Proof. solve_decision. Defined.

Section definedness.
  Context {sig : Signature}.

  Class Syntax(*(sig : Signature)*) :=
    { (*sig: Signature;*)
    (* 'Symbols' are a 'subset' of all the symbols from the signature *)
    inj: Symbols -> symbols;
    (* TODO make it injective? *)
    (* for convenience *)
    }.  

  Context {self : Syntax}.

  Let Pattern : Type := @MatchingLogic.Syntax.Pattern sig.

  Definition patt_defined (phi : Pattern) : Pattern :=
    patt_sym (inj definedness) $ phi.
  
  Definition patt_total (phi: Pattern) : Pattern :=
    patt_not (patt_defined (patt_not phi)).

  Definition patt_subseteq (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 ---> phi2).
  
  Definition patt_equal (phi1 phi2 : Pattern) : Pattern :=
    patt_total (phi1 <---> phi2).

  Lemma well_formed_equal (phi1 phi2 : Pattern) :
    well_formed phi1 ->
    well_formed phi2 ->
    well_formed (patt_equal phi1 phi2).
  Proof.
    unfold patt_equal, patt_iff, patt_and, patt_or, patt_not. intros H H0.
    unfold well_formed in *. simpl.
    unfold well_formed_closed in *. simpl.
    apply andb_prop in H. destruct H as [H11 H12].
    apply andb_prop in H0. destruct H0 as [H21 H22].
    rewrite !(H11,H12,H21,H22). simpl. auto.
  Qed.

  Definition patt_in (phi1 phi2 : Pattern) : Pattern :=
    patt_defined (patt_and phi1 phi2).

  Let sym (s : Symbols) : Pattern :=
    @patt_sym sig (inj s).

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
    forall (M : @Model sig) (evar_val : @EVarVal sig M) (svar_val : @SVarVal (sig) M),
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

  Lemma definedness_not_empty_1 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        (@pattern_interpretation (sig) M evar_val svar_val phi) <> ∅ ->
        (@pattern_interpretation (sig) M evar_val svar_val (patt_defined phi)) = ⊤.
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
                            sig
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

  Lemma definedness_empty_1 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation sig M evar_val svar_val phi = Semantics.Empty ->
        @pattern_interpretation sig M evar_val svar_val (patt_defined phi) = Semantics.Empty.
  Proof.
    intros M H phi evar_val svar_val H0. unfold patt_defined.
    rewrite -> pattern_interpretation_app_simpl.
    rewrite -> H0.
    apply app_ext_bot_r.
  Qed.

  Theorem modus_tollens: forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
  Proof. auto. Qed.

  Lemma definedness_empty_2 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation sig M evar_val svar_val (patt_defined phi) = Semantics.Empty ->
        @pattern_interpretation sig M evar_val svar_val phi = Semantics.Empty.
  Proof.
    intros M H phi evar_val svar_val H0.
    pose proof (H1 := @empty_impl_not_full sig M _ H0).
    pose proof (H2 := @modus_tollens _ _ (@definedness_not_empty_1 M H phi evar_val svar_val) H1).
    apply NNPP in H2. apply H2.
  Qed.

  Lemma definedness_not_empty_2 : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_defined phi) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val phi <> Semantics.Empty.
  Proof.
    intros M H phi evar_val svar_val H0.
    pose proof (H1 := full_impl_not_empty H0).
    exact (@modus_tollens _ _ (@definedness_empty_1 M H phi evar_val svar_val) H1).
  Qed.

  Lemma totality_not_full : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val phi <> ⊤ ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_total phi) = ∅.
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

  Lemma totality_full : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val phi = ⊤ ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_total phi) = ⊤.
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

  Lemma totality_result_empty : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_total phi) = ∅ ->
        @pattern_interpretation (sig) M evar_val svar_val phi <> ⊤.
  Proof.
    intros M H phi evar_val svar_val H0.
    pose proof (H1 := empty_impl_not_full H0).
    pose proof (H2 := @modus_tollens _ _ (@totality_full M H phi evar_val svar_val) H1).
    apply H2.
  Qed.

  Lemma totality_result_nonempty : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_total phi) <> ∅ ->
        @pattern_interpretation (sig) M evar_val svar_val phi = ⊤.
  Proof.
    intros M H phi evar_val svar_val H0.
    pose proof (H2 := @modus_tollens _ _ (@totality_not_full M H phi evar_val svar_val) H0).
    apply NNPP in H2. apply H2.
  Qed.
  
  Lemma equal_iff_both_subseteq : forall (M : @Model (sig)),        
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = ⊤ <->
        (
          @pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2) = ⊤ /\
          @pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi2 phi1) = ⊤).
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

  Lemma subseteq_iff_interpr_subseteq : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_subseteq phi1 phi2) = ⊤ <->
        (@pattern_interpretation (sig) M evar_val svar_val phi1)
          ⊆ (@pattern_interpretation (sig) M evar_val svar_val phi2).
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
  
  Lemma equal_iff_interpr_same : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = Full <->
        @pattern_interpretation (sig) M evar_val svar_val phi1
        = @pattern_interpretation (sig) M evar_val svar_val phi2.
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

  Lemma equal_refl : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi phi) = Full.
  Proof.
    intros M H phi evar_val svar_val.
    apply (@equal_iff_interpr_same _ H).
    auto.
  Qed.

  Lemma equal_sym : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi2 phi1) = Full.
  Proof.
    intros M H phi1 phi2 evar_val svar_val H0.
    apply (@equal_iff_interpr_same _ H).
    apply (@equal_iff_interpr_same _ H) in H0.
    symmetry. auto.
  Qed.

  Lemma equal_trans : forall (M : @Model (sig)),
      M ⊨ᵀ theory ->
      forall (phi1 phi2 phi3 : Pattern) (evar_val : @EVarVal (sig) M) (svar_val : @SVarVal (sig) M),
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi2) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi2 phi3) = Full ->
        @pattern_interpretation (sig) M evar_val svar_val (patt_equal phi1 phi3) = Full.
  Proof.
    intros M H phi1 phi2 phi3 evar_val svar_val H0 H1.
    apply (@equal_iff_interpr_same _ H).
    apply (@equal_iff_interpr_same _ H) in H0.
    apply (@equal_iff_interpr_same _ H) in H1.
    rewrite -> H0. auto.
  Qed.

  Lemma free_evar_in_patt : forall (M : @Model sig),
      M ⊨ᵀ theory ->
      forall (x : evar)(phi : Pattern) (evar_val : @EVarVal sig M) (svar_val : @SVarVal sig M),
        ((evar_val x) ∈ (@pattern_interpretation sig M evar_val svar_val phi)) <->
        @pattern_interpretation sig M evar_val svar_val (patt_in (patt_free_evar x) phi) = ⊤.
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
  Lemma evar_open_defined db x ϕ : evar_open db x (patt_defined ϕ) = patt_defined (evar_open db x ϕ).
  Proof. unfold patt_defined. cbn. auto. Qed.
  Lemma svar_open_defined db x ϕ : svar_open db x (patt_defined ϕ) = patt_defined (svar_open db x ϕ).
  Proof. unfold patt_defined. cbn. auto. Qed.

  #[global]
   Instance Unary_defined : Unary patt_defined :=
    {| unary_evar_open := evar_open_defined ;
       unary_svar_open := svar_open_defined ;
    |}.
  

  Lemma evar_open_total db x ϕ : evar_open db x (patt_total ϕ) = patt_total (evar_open db x ϕ).
  Proof. unfold patt_total. rewrite !simpl_evar_open. reflexivity. Qed.
  Lemma svar_open_total db x ϕ : svar_open db x (patt_total ϕ) = patt_total (svar_open db x ϕ).
  Proof. unfold patt_total. rewrite !simpl_svar_open. reflexivity. Qed.

  #[global]
   Instance Unary_total : Unary patt_total :=
    {| unary_evar_open := evar_open_total ;
       unary_svar_open := svar_open_total ;
    |}.
  
  
  Lemma evar_open_equal db x ϕ₁ ϕ₂ : evar_open db x (patt_equal ϕ₁ ϕ₂) = patt_equal (evar_open db x ϕ₁) (evar_open db x ϕ₂).
  Proof. unfold patt_equal. rewrite !simpl_evar_open. reflexivity. Qed.
  Lemma svar_open_equal db x ϕ₁ ϕ₂ : svar_open db x (patt_equal ϕ₁ ϕ₂) = patt_equal (svar_open db x ϕ₁) (svar_open db x ϕ₂).
  Proof. unfold patt_equal. rewrite !simpl_svar_open. reflexivity. Qed.

  #[global]
   Instance Binary_equal : Binary patt_equal :=
    {| binary_evar_open := evar_open_equal ;
       binary_svar_open := svar_open_equal ;
    |}.
  
  Lemma evar_open_subseteq db x ϕ₁ ϕ₂ : evar_open db x (patt_subseteq ϕ₁ ϕ₂) = patt_subseteq (evar_open db x ϕ₁) (evar_open db x ϕ₂).
  Proof. unfold patt_subseteq. rewrite !simpl_evar_open. reflexivity. Qed.
  Lemma svar_open_subseteq db x ϕ₁ ϕ₂ : svar_open db x (patt_subseteq ϕ₁ ϕ₂) = patt_subseteq (svar_open db x ϕ₁) (svar_open db x ϕ₂).
  Proof. unfold patt_subseteq. rewrite !simpl_svar_open. reflexivity. Qed.

  #[global]
   Instance Binary_subseteq : Binary patt_subseteq :=
    {| binary_evar_open := evar_open_subseteq ;
       binary_svar_open := svar_open_subseteq ;
    |}.
  

  Lemma evar_open_in db x ϕ₁ ϕ₂ : evar_open db x (patt_in ϕ₁ ϕ₂) = patt_in (evar_open db x ϕ₁) (evar_open db x ϕ₂).
  Proof. unfold patt_in. rewrite !simpl_evar_open. reflexivity. Qed.
  Lemma svar_open_in db x ϕ₁ ϕ₂ : svar_open db x (patt_in ϕ₁ ϕ₂) = patt_in (svar_open db x ϕ₁) (svar_open db x ϕ₂).
  Proof. unfold patt_in. rewrite !simpl_svar_open. reflexivity. Qed.

  #[global]
   Instance Binary_in : Binary patt_in :=
    {| binary_evar_open := evar_open_in ;
       binary_svar_open := svar_open_in ;
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
    
    rewrite simpl_evar_open.
    apply T_predicate_equals.
    apply Hm.
  Qed.

  Lemma pattern_interpretation_eq_inversion_of ϕ₁ ϕ₂ M ρₑ ρₛ :
    M ⊨ᵀ theory ->
    @pattern_interpretation sig M ρₑ ρₛ (patt_eq_inversion_of ϕ₁ ϕ₂) = ⊤
    <-> (forall m₁ m₂,
            m₂ ∈ rel_of ρₑ ρₛ ϕ₁ m₁ <-> m₁ ∈ rel_of ρₑ ρₛ ϕ₂ m₂ (* TODO make rel_of take one more parameter. *)
        ).
  Proof.
    intros Htheory.
    rewrite pattern_interpretation_forall_predicate.
    2: { rewrite simpl_evar_open. apply T_predicate_equals. apply Htheory. }
    apply all_iff_morphism. intros m₁.
    remember ((fresh_evar
          (patt_equal (nest_ex ϕ₁ $ BoundVarSugar.b0)
             (ex ,
              (BoundVarSugar.b0
                 and patt_in BoundVarSugar.b1 (nest_ex (nest_ex ϕ₂) $ BoundVarSugar.b0)))))) as x.
    rewrite !simpl_evar_open.
    rewrite equal_iff_interpr_same.
    2: { apply Htheory. }

    rewrite pattern_interpretation_set_builder.
    { rewrite !simpl_evar_open. apply T_predicate_in. apply Htheory. }

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
    rewrite [evar_open 0 x b0]/=.
    rewrite [evar_open 1 x b1]/=.
    rewrite [evar_open 1 x b0]/=.

    remember (fresh_evar (patt_in (patt_free_evar x) (evar_open 1 x (nest_ex (nest_ex ϕ₂)) $ b0))) as y.
    rewrite simpl_evar_open.
    rewrite [evar_open 0 y (patt_free_evar x)]/=.
    repeat rewrite elem_of_PropSet.
    rewrite <- free_evar_in_patt.
    2: { apply Htheory. }
    rewrite pattern_interpretation_free_evar_simpl.
    rewrite update_evar_val_same.
    fold (m₂ ∈ rel_of ρₑ ρₛ ϕ₁ m₁).

    rewrite simpl_evar_open.
    rewrite pattern_interpretation_app_simpl.
    rewrite [evar_open 0 y b0]/=.
    rewrite pattern_interpretation_free_evar_simpl.
    rewrite update_evar_val_same.
    
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

  Lemma single_element_definedness_impl_satisfies_definedness (M : @Model sig) :
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

  Section ProofSystemTheorems.
  
    Import ProofSystem Helpers.FOL_helpers.
    Notation "theory ⊢ pattern" := (@ML_proof_system sig theory pattern) (at level 95, no associativity).

    Lemma patt_iff_implies_equal :
    forall (φ1 φ2 : Pattern) Γ, well_formed φ1 -> well_formed φ2 ->
    Γ ⊢ (φ1 <---> φ2) -> Γ ⊢ (patt_equal φ1 φ2).
  Proof.
    intros φ1 φ2 Γ WF1 WF2 H.
    epose proof (ANNA := A_implies_not_not_A_ctx Γ (φ1 <---> φ2) (ctx_app_r box _)). 
    apply ANNA; auto. unfold patt_iff, patt_and, patt_or, patt_not.
    unfold well_formed, well_formed_closed in *.
    apply andb_true_iff in WF1 as [H0 H1]. apply andb_true_iff in WF2 as [H2 H3]. cbn.
    now rewrite -> H1, -> H2, -> H3, -> H0.
    Unshelve.
    auto.
  Qed.

  Lemma patt_equal_refl :
    forall φ Γ, well_formed φ ->
    Γ ⊢ patt_equal φ φ.
  Proof.
    intros φ Γ WF. pose proof (IFF := pf_iff_equiv_refl Γ φ WF).
    apply patt_iff_implies_equal in IFF; auto.
  Qed.

  Theorem deduction_theorem :
    forall φ ψ Γ, (* psi closed *)
      Γ ∪ {[ ψ ]} ⊢ φ ->
      Γ ⊢ patt_total (ψ) ---> φ.
  Proof.
  
  Admitted.

  Theorem reverse_deduction_theorem :
    forall φ ψ Γ,
      Γ ⊢ ((patt_total ψ) ---> φ) ->
      Γ ∪ {[ ψ ]} ⊢ φ.
  Proof.
  
  Admitted.

  Lemma equality_elimination Γ φ1 φ2 C :
    well_formed φ1 -> well_formed φ2 ->
    wf_PatCtx C ->
    Γ ⊢ (patt_equal φ1 φ2) ---> (* somewhere "and" is here, somewhere meta-implication *)
       (subst_patctx C φ1) ---> (subst_patctx C φ2).
  Proof.
    intros WF1 WF2 WFC. apply deduction_theorem.
    remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
    assert (Γ' ⊢ (φ1 <---> φ2)). {
      apply hypothesis. now apply well_formed_iff.
      rewrite HeqΓ'. apply elem_of_union_r. constructor.
    }
    apply congruence_iff with (C0 := C) in H.
    apply pf_iff_proj1 in H. rewrite HeqΓ' in H. all: auto.
    1-2: now apply subst_patctx_wf.
  Qed.

  Lemma equality_elimination_helper Γ φ1 φ2 ψ x :
    mu_free ψ ->
    well_formed φ1 -> well_formed φ2 -> well_formed ψ ->
    Γ ⊢ (patt_equal φ1 φ2) ---> 
        (free_evar_subst ψ φ1 x) ---> (free_evar_subst ψ φ2 x).
  Proof.
    intros MF WF1 WF2 WFψ. apply deduction_theorem.
    remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
    assert (Γ' ⊢ (φ1 <---> φ2)). {
      apply hypothesis. now apply well_formed_iff.
      rewrite HeqΓ'. apply elem_of_union_r. constructor.
    }
    apply congruence_iff_helper with (ψ0 := ψ) (sz := Syntax.size ψ) (x0 := x) in H.
    rewrite HeqΓ' in H.
    apply pf_iff_proj1 in H. all: auto.
  Qed.

  Corollary equality_elimination2 Γ φ1 φ2 ψ:
    mu_free ψ ->
    well_formed φ1 -> well_formed φ2 -> wf_body_ex ψ ->
    Γ ⊢ (patt_equal φ1 φ2) ---> 
        (bevar_subst ψ φ1 0) ---> (bevar_subst ψ φ2 0).
  Proof.
    intros MF WF1 WF2 WFB. remember (fresh_evar ψ) as x.
    assert (x ∉ free_evars ψ) by now apply x_eq_fresh_impl_x_notin_free_evars.
    rewrite (@bound_to_free_variable_subst _ ψ x 1 0 0 φ1).
    4: rewrite (@bound_to_free_variable_subst _ ψ x 1 0 0 φ2).
    1, 4: lia. all: auto.
    1, 2: apply wf_body_ex_to_wf in WFB; apply andb_true_iff in WFB as [E1 E2]; auto.
    apply equality_elimination_helper; auto.
    now apply mu_free_evar_open.
  Qed.

  Lemma patt_eq_sym_meta Γ φ1 φ2 :
     well_formed φ1 -> well_formed φ2 ->
     Γ ⊢ (patt_equal φ1 φ2) -> Γ ⊢ (patt_equal φ2 φ1).
  Proof.
    intros WF1 WF2 H.
    epose proof (P2 := @equality_elimination Γ φ1 φ2 pctx_box WF1 WF2 ltac:(constructor)). simpl in P2.
    eapply Modus_ponens in P2; auto.
    3: apply well_formed_imp; auto. 2-3: apply well_formed_equal; auto.
    epose proof (P1 := @equality_elimination Γ φ1 φ2 (pctx_imp_l pctx_box φ1) WF1 WF2 _).
    simpl in P1.
    apply Modus_ponens in P1; auto. 3: apply well_formed_imp; auto. 2-3: apply well_formed_equal; auto.
    apply Modus_ponens in P1. 2-3: auto. 2: apply A_impl_A; auto.
    apply pf_iff_split in P2; auto.
    apply patt_iff_implies_equal in P2; auto.
    Unshelve.
      simpl. now rewrite WF1.
  Qed.

  Lemma patt_eq_sym Γ φ1 φ2:
     well_formed φ1 -> well_formed φ2 ->
     Γ ⊢ (patt_equal φ1 φ2) ---> (patt_equal φ2 φ1).
  Proof.
    intros WF1 WF2.
    apply deduction_theorem.
    remember (Γ ∪ {[ (φ1 <---> φ2) ]}) as Γ'.
    assert (Γ' ⊢ (φ1 <---> φ2)). {
      apply hypothesis. apply well_formed_iff; auto.
      rewrite HeqΓ'. apply elem_of_union_r. constructor.
    }
    apply pf_iff_equiv_sym in H; auto.
    apply patt_iff_implies_equal; auto. now rewrite HeqΓ' in H.
  Qed.

  Lemma evar_quantify_equal_simpl : forall φ1 φ2 x n,
    evar_quantify x n (patt_equal φ1 φ2) = patt_equal (evar_quantify x n φ1) (evar_quantify x n φ2). Proof. auto. Qed.

  Lemma exists_functional_subst φ φ' Γ :
    mu_free φ -> well_formed φ' -> wf_body_ex φ ->
    Γ ⊢ ((instantiate (patt_exists φ) φ') and (patt_exists (patt_equal φ' (patt_bound_evar 0)))) ---> (patt_exists φ).
  Proof.
    intros MF WF WFB.
    remember (fresh_evar (φ $ φ')) as Zvar.
    remember (patt_free_evar Zvar) as Z.
    assert (well_formed Z) as WFZ. { rewrite HeqZ. auto. }
    assert (Γ ⊢ (patt_equal φ' Z <---> patt_equal Z φ')). {
      pose proof (SYM1 := @patt_eq_sym Γ φ' Z ltac:(auto) WFZ).
      pose proof (SYM2 := @patt_eq_sym Γ Z φ' WFZ ltac:(auto)).
      apply pf_iff_split; auto. 1-2: now apply well_formed_equal.
    }
    assert (well_formed (instantiate (ex , φ) φ')) as WF1. {
      unfold instantiate.
      unfold well_formed, well_formed_closed.
      apply andb_true_iff in WF as [E1 E2]. simpl in E1, E2.
      apply wf_body_ex_to_wf in WFB.
      apply andb_true_iff in WFB as [E3 E4]. simpl in E3, E4.
      erewrite bevar_subst_closed, bevar_subst_positive; auto.
    }
    assert (well_formed (instantiate (ex , φ) Z)) as WF2. {
      unfold instantiate.
      unfold well_formed, well_formed_closed.
      apply andb_true_iff in WF as [E1 E2]. simpl in E1, E2.
      apply wf_body_ex_to_wf in WFB.
      apply andb_true_iff in WFB as [E3 E4]. simpl in E3, E4.
      erewrite bevar_subst_closed, bevar_subst_positive; auto.
      all: rewrite HeqZ; auto.
    }
    pose proof (@equality_elimination2 Γ φ' Z φ MF WF WFZ WFB).
    apply pf_iff_iff in H. destruct H.
    pose proof (EQ := Ex_quan Γ φ Zvar).
    epose proof (PC := prf_conclusion Γ (patt_equal φ' Z) (instantiate (ex , φ) (patt_free_evar Zvar) ---> ex , φ) ltac:(apply well_formed_equal;auto) _ EQ).
    2-3: apply well_formed_equal;auto.
    assert (Γ
     ⊢ patt_equal φ' Z ---> instantiate (ex , φ) φ' ---> ex , φ) as HSUB. {
       pose proof (EE := @equality_elimination2 Γ φ' Z φ 
                     ltac:(auto) ltac:(auto) ltac:(auto) WFB).
       unfold instantiate in EE.
       epose proof (PSP := prf_strenghten_premise Γ ((patt_equal φ' Z) and (instantiate (ex , φ) Z))
                                             ((patt_equal φ' Z) and (instantiate (ex , φ) φ'))
                                             (ex , φ) _ _ _).
       eapply Modus_ponens. 4: apply and_impl.
       all: auto. 1, 2, 4: shelve.
       eapply Modus_ponens. 4: eapply Modus_ponens.
       7: exact PSP. 1, 2, 4, 5: shelve.
       * epose proof (AI := and_impl' Γ (patt_equal φ' Z) (bevar_subst φ Z 0) (ex , φ) _ _ _).
         unfold instantiate. eapply Modus_ponens. 1, 2: shelve. 2: exact AI.
         rewrite <- HeqZ in PC.
         exact PC.
       * apply and_drop. 1-3: shelve.
         epose proof (AI := and_impl' Γ (patt_equal φ' Z) (instantiate (ex , φ) φ') (instantiate (ex , φ) Z) _ _ _).
         eapply Modus_ponens. 4: exact AI. 1-2: shelve. exact EE.
      Unshelve.
      all: unfold patt_equal, patt_iff, patt_total, patt_defined, patt_and, patt_or, patt_not; auto 10.
      all: repeat try apply well_formed_imp; auto.
      all: repeat try apply well_formed_app; auto.
      all: repeat try apply well_formed_imp; auto.
      rewrite <- HeqZ. auto.
      all: now apply wf_body_ex_to_wf.
      * now apply wf_body_ex_to_wf.
    }
    eapply Modus_ponens. 4: apply and_impl'; auto.
    1,2,4,5: shelve.
    apply reorder_meta; auto. 1-2: shelve.
    eapply (Ex_gen Γ _ _ Zvar) in HSUB. unfold exists_quantify in HSUB.
    rewrite evar_quantify_equal_simpl in HSUB.
    rewrite -> HeqZ, -> HeqZvar in HSUB. simpl evar_quantify in HSUB.
    2-4: shelve.
    destruct (decide ((fresh_evar (φ $ φ')) = (fresh_evar (φ $ φ')))) in HSUB;
    simpl in HSUB. 2: congruence.
    rewrite evar_quantify_free_evar_subst in HSUB; auto.

    apply count_evar_occurrences_0.
    unfold fresh_evar. simpl.
    epose (NIN := not_elem_of_union (evar_fresh (elements (free_evars φ ∪ free_evars φ'))) (free_evars φ) (free_evars φ')). destruct NIN as [NIN1 NIN2].
    epose (NIN3 := NIN1 _). destruct NIN3. auto.
  Unshelve.
    1-6: unfold patt_equal, patt_iff, patt_total, patt_defined, patt_and, patt_or, patt_not; auto 10.
    1-4: repeat try apply well_formed_imp; auto.
    1-9: unfold well_formed, well_formed_closed in *; simpl.
    all: apply wf_body_ex_to_wf in WFB; auto; apply eq_sym, andb_true_eq in WFB; unfold well_formed_closed in WFB; simpl in WFB; destruct WFB;
      try rewrite <- WFB, <- H4; auto.
    1-5: apply andb_true_iff in WF as [E1 E2];
      apply wfc_aux_extend with (n' := 1) (m' := 0) in E2.
    all: try lia. 1-5: rewrite -> E1, -> E2; simpl; auto.
    apply well_formed_equal; auto.
    unfold instantiate. simpl. eapply stdpp_ext.not_elem_of_larger_impl_not_elem_of.
    eapply union_mono_r. apply free_evars_bevar_subst.
    rewrite HeqZvar.
    rewrite (union_comm_L (free_evars φ) (free_evars φ')).
    rewrite <- (union_assoc_L (free_evars φ') (free_evars φ) (free_evars φ)).
    rewrite (union_idemp_L (free_evars φ)).
    rewrite (union_comm_L (free_evars φ') (free_evars φ)).
    replace (@union (@EVarSet sig)
        (@gmap.gset_union _ _ _) (@free_evars sig φ)
        (@free_evars sig φ')) with (free_evars (φ $ φ')) by reflexivity.
    now apply x_eq_fresh_impl_x_notin_free_evars.
    apply set_evar_fresh_is_fresh'.
  Qed.

  Corollary forall_functional_subst φ φ' Γ : 
    mu_free φ -> well_formed φ' -> wf_body_ex φ -> 
      Γ ⊢ ((patt_forall φ) and (patt_exists (patt_equal φ' (patt_bound_evar 0)))) ---> (bevar_subst φ φ' 0).
  Proof.
    intros MF WF WFB. unfold patt_forall.
    assert (well_formed (bevar_subst φ φ' 0)) as BWF. {
      unfold well_formed, well_formed_closed.
      rewrite -> well_formed_positive_bevar_subst, -> bevar_subst_well_formedness; auto.
      2, 4: apply andb_true_iff in WF as [E1 E2]; auto.
      all: apply wf_body_ex_to_wf, andb_true_iff in WFB as [E1 E2]; 
        unfold well_formed_closed in E2; simpl in E1, E2; auto.
    }
    assert (well_formed (ex , patt_equal φ' b0)) as SWF. {
      unfold well_formed, well_formed_closed.
      apply andb_true_iff in WF as [E1 E2]. unfold well_formed_closed in E2.
      simpl. rewrite E1. apply wfc_aux_extend with (n' := 1) (m' := 0) in E2.
      rewrite E2. auto. all: lia.
    }
    assert (well_formed (ex , (φ ---> ⊥))) as NWF. {
      apply wf_body_ex_to_wf in WFB. unfold well_formed, well_formed_closed in *.
      clear BWF SWF.
      apply andb_true_iff in WFB as [E1 E2]. simpl in *.
      now rewrite -> E1, -> E2.
    }
    epose proof (H := @exists_functional_subst (¬ φ) φ' Γ _ WF _).
    simpl in H.
    epose proof (H0 := and_impl _ _ _ _ _ _ _).
    eapply Modus_ponens in H0. 4: exact H. 2-3: shelve.
    apply reorder_meta in H0. 2-4: shelve.
    
    epose proof (H1 := and_impl' _ _ _ _ _ _ _). eapply Modus_ponens in H1. exact H1.
    1-2: shelve.
    apply reorder_meta. 1-3: shelve.
    epose proof (H2 := P4 Γ (bevar_subst φ φ' 0) (¬ ex , ¬ φ) _ _).
    clear H H1.
    epose proof (H := prf_weaken_conclusion Γ (ex , patt_equal φ' b0) ((bevar_subst φ φ' 0 ---> ⊥) ---> ex , (¬ φ)) ((bevar_subst φ φ' 0 ---> ⊥) ---> ¬ ¬ ex , (¬ φ)) _ _ _).
    eapply Modus_ponens in H. eapply Modus_ponens in H; auto.
    2-4: shelve.
    2: {
      epose proof (H1 := prf_weaken_conclusion Γ (bevar_subst φ φ' 0 ---> ⊥) (ex , (¬ φ)) (¬ ¬ ex , (¬ φ)) _ _ _). eapply Modus_ponens. 4: exact H1. 1-2: shelve.
      apply not_not_intro. shelve.
    }
    eapply syllogism_intro in H2. exact H2. all: auto.
    Unshelve.
    all: unfold patt_not; auto.
    simpl. now rewrite MF.
    apply wf_body_ex_to_wf in WFB; apply wf_ex_to_wf_body; auto.
    all: repeat apply well_formed_imp; auto.
  Qed.

  End ProofSystemTheorems.

End definedness.

Hint Rewrite ->
@evar_open_defined
  @svar_open_defined
  @evar_open_total
  @svar_open_total
  @evar_open_equal
  @svar_open_equal
  @evar_open_subseteq
  @svar_open_subseteq
  @evar_open_in
  @svar_open_in
  : ml_db.

  Hint Resolve T_predicate_defined : core.
  Hint Resolve T_predicate_total : core.
  Hint Resolve T_predicate_subseteq : core.
  Hint Resolve T_predicate_equals : core.
  Hint Resolve T_predicate_in : core.
