From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool String Btauto.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Equations Require Import Equations.

Require Import Coq.Program.Tactics.

From MatchingLogic Require Import Syntax
                                  ProofSystem
                                  wftactics
                                  NamedAxioms
                                  IndexManipulation.

From stdpp Require Import list tactics fin_sets coGset gmap sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators_Syntax.Notations
  MatchingLogic.ProofSystem.Notations_private
.

Set Default Proof Mode "Classic".

Open Scope ml_scope.

Section with_signature.
  Context {Σ : Signature}.
  (* TODO make this return well-formed patterns. *)
  Fixpoint framing_patterns Γ ϕ (pf : Γ ⊢H ϕ) : gset wfPattern :=
  match pf with
  | hypothesis _ _ _ _ => ∅
  | P1 _ _ _ _ _ => ∅
  | P2 _ _ _ _ _ _ _ => ∅
  | P3 _ _ _ => ∅
  | Modus_ponens _ _ _ m0 m1
    => (@framing_patterns _ _ m0) ∪ (@framing_patterns _ _ m1)
  | Ex_quan _ _ _ _ => ∅
  | Ex_gen _ _ _ x _ _ pf _ => @framing_patterns _ _ pf
  | Prop_bott_left _ _ _ => ∅
  | Prop_bott_right _ _ _ => ∅
  | Prop_disj_left _ _ _ _ _ _ _ => ∅
  | Prop_disj_right _ _ _ _ _ _ _ => ∅
  | Prop_ex_left _ _ _ _ _ => ∅
  | Prop_ex_right _ _ _ _ _ => ∅
  | Framing_left _ _ _ psi wfp m0 => {[(exist _ psi wfp)]} ∪ (@framing_patterns _ _ m0)
  | Framing_right _ _ _ psi wfp m0 => {[(exist _ psi wfp)]} ∪ (@framing_patterns _ _ m0)
  | Svar_subst _ _ _ _ _ _ m0 => @framing_patterns _ _ m0
  | Pre_fixp _ _ _ => ∅
  | Knaster_tarski _ _ phi psi m0 => @framing_patterns _ _ m0
  | Existence _ => ∅
  | Singleton_ctx _ _ _ _ _ _ => ∅
  end.


  Fixpoint uses_ex_gen (EvS : EVarSet) Γ ϕ (pf : ML_proof_system Γ ϕ) :=
  match pf with
  | hypothesis _ _ _ _ => false
  | P1 _ _ _ _ _ => false
  | P2 _ _ _ _ _ _ _ => false
  | P3 _ _ _ => false
  | Modus_ponens _ _ _ m0 m1
    => uses_ex_gen EvS _ _ m0
        || uses_ex_gen EvS _ _ m1
  | Ex_quan _ _ _ _ => false
  | Ex_gen _ _ _ x _ _ pf _ => if decide (x ∈ EvS) is left _ then true else uses_ex_gen EvS _ _ pf
  | Prop_bott_left _ _ _ => false
  | Prop_bott_right _ _ _ => false
  | Prop_disj_left _ _ _ _ _ _ _ => false
  | Prop_disj_right _ _ _ _ _ _ _ => false
  | Prop_ex_left _ _ _ _ _ => false
  | Prop_ex_right _ _ _ _ _ => false
  | Framing_left _ _ _ _ _ m0 => uses_ex_gen EvS _ _ m0
  | Framing_right _ _ _ _ _ m0 => uses_ex_gen EvS _ _ m0
  | Svar_subst _ _ _ _ _ _ m0 => uses_ex_gen EvS _ _ m0
  | Pre_fixp _ _ _ => false
  | Knaster_tarski _ _ phi psi m0 => uses_ex_gen EvS _ _ m0
  | Existence _ => false
  | Singleton_ctx _ _ _ _ _ _ => false
  end.

Fixpoint uses_of_ex_gen Γ ϕ (pf : ML_proof_system Γ ϕ) : EVarSet :=
  match pf with
  | hypothesis _ _ _ _ => ∅
  | P1 _ _ _ _ _ => ∅
  | P2 _ _ _ _ _ _ _ => ∅
  | P3 _ _ _ => ∅
  | Modus_ponens _ _ _ m0 m1
    => uses_of_ex_gen _ _ m0
        ∪ uses_of_ex_gen _ _ m1
  | Ex_quan _ _ _ _ => ∅
  | Ex_gen _ _ _ x _ _ pf _ => {[x]} ∪ uses_of_ex_gen _ _ pf
  | Prop_bott_left _ _ _ => ∅
  | Prop_bott_right _ _ _ => ∅
  | Prop_disj_left _ _ _ _ _ _ _ => ∅
  | Prop_disj_right _ _ _ _ _ _ _ => ∅
  | Prop_ex_left _ _ _ _ _ => ∅
  | Prop_ex_right _ _ _ _ _ => ∅
  | Framing_left _ _ _ _ _ m0 => uses_of_ex_gen _ _ m0
  | Framing_right _ _ _ _ _ m0 => uses_of_ex_gen _ _ m0
  | Svar_subst _ _ _ _ _ _ m0 => uses_of_ex_gen _ _ m0
  | Pre_fixp _ _ _ => ∅
  | Knaster_tarski _ _ phi psi m0 => uses_of_ex_gen _ _ m0
  | Existence _ => ∅
  | Singleton_ctx _ _ _ _ _ _ => ∅
  end.
  
  Lemma uses_of_ex_gen_correct Γ ϕ (pf : ML_proof_system Γ ϕ) (x : evar) :
    x ∈ uses_of_ex_gen Γ ϕ pf <-> uses_ex_gen {[x]} Γ ϕ pf = true.
  Proof.
    induction pf; simpl; try set_solver.
    {
      rewrite orb_true_iff. set_solver.
    }
    {
      rewrite elem_of_union. rewrite IHpf.
      destruct (decide (x0 ∈ {[x]})) as [Hin|Hnotin].
      {
        rewrite elem_of_singleton in Hin. subst.
        split; intros H. reflexivity. left. rewrite elem_of_singleton.
        reflexivity.
      }
      {
        split; intros H.
        {
          destruct H as [H|H].
          {
            exfalso. set_solver.
          }
          exact H.
        }
        {
          right. exact H.
        }
      }
    }
  Qed.

  Fixpoint uses_svar_subst (S : SVarSet) Γ ϕ (pf : Γ ⊢H ϕ) :=
    match pf with
    | hypothesis _ _ _ _ => false
    | P1 _ _ _ _ _ => false
    | P2 _ _ _ _ _ _ _ => false
    | P3 _ _ _ => false
    | Modus_ponens _ _ _ m0 m1
      => uses_svar_subst S _ _ m0
         || uses_svar_subst S _ _ m1
    | Ex_quan _ _ _ _ => false
    | Ex_gen _ _ _ _ _ _ pf' _ => uses_svar_subst S _ _ pf'
    | Prop_bott_left _ _ _ => false
    | Prop_bott_right _ _ _ => false
    | Prop_disj_left _ _ _ _ _ _ _ => false
    | Prop_disj_right _ _ _ _ _ _ _ => false
    | Prop_ex_left _ _ _ _ _ => false
    | Prop_ex_right _ _ _ _ _ => false
    | Framing_left _ _ _ _ _ m0 => uses_svar_subst S _ _ m0
    | Framing_right _ _ _ _ _ m0 => uses_svar_subst S _ _ m0
    | Svar_subst _ _ _ X _ _ m0 => if decide (X ∈ S) is left _ then true else uses_svar_subst S _ _ m0
    | Pre_fixp _ _ _ => false
    | Knaster_tarski _ _ phi psi m0 => uses_svar_subst S _ _ m0
    | Existence _ => false
    | Singleton_ctx _ _ _ _ _ _ => false
    end.

  Fixpoint uses_of_svar_subst Γ ϕ (pf : Γ ⊢H ϕ) : SVarSet :=
    match pf with
    | hypothesis _ _ _ _ => ∅
    | P1 _ _ _ _ _ => ∅
    | P2 _ _ _ _ _ _ _ => ∅
    | P3 _ _ _ => ∅
    | Modus_ponens _ _ _ m0 m1
      => uses_of_svar_subst _ _ m0
          ∪ uses_of_svar_subst _ _ m1
    | Ex_quan _ _ _ _ => ∅
    | Ex_gen _ _ _ _ _ _ pf' _ => uses_of_svar_subst _ _ pf'
    | Prop_bott_left _ _ _ => ∅
    | Prop_bott_right _ _ _ => ∅
    | Prop_disj_left _ _ _ _ _ _ _ => ∅
    | Prop_disj_right _ _ _ _ _ _ _ => ∅
    | Prop_ex_left _ _ _ _ _ => ∅
    | Prop_ex_right _ _ _ _ _ => ∅
    | Framing_left _ _ _ _ _ m0 => uses_of_svar_subst _ _ m0
    | Framing_right _ _ _ _ _ m0 => uses_of_svar_subst _ _ m0
    | Svar_subst _ _ _ X _ _ m0 => {[X]} ∪ uses_of_svar_subst _ _ m0
    | Pre_fixp _ _ _ => ∅
    | Knaster_tarski _ _ phi psi m0 => uses_of_svar_subst _ _ m0
    | Existence _ => ∅
    | Singleton_ctx _ _ _ _ _ _ => ∅
    end.

  Lemma uses_of_svar_subst_correct Γ ϕ (pf : ML_proof_system Γ ϕ) (X : svar) :
    X ∈ uses_of_svar_subst Γ ϕ pf <-> uses_svar_subst {[X]} Γ ϕ pf = true.
  Proof.
    induction pf; simpl; try set_solver.
    {
      rewrite orb_true_iff. set_solver.
    }
    {
      rewrite elem_of_union. rewrite IHpf. clear IHpf.
      destruct (decide (X0 ∈ {[X]})) as [Hin|Hnotin].
      {
        rewrite elem_of_singleton in Hin. subst.
        split; intros H. reflexivity. left. rewrite elem_of_singleton.
        reflexivity.
      }
      {
        split; intros H.
        {
          destruct H as [H|H].
          {
            exfalso. set_solver.
          }
          exact H.
        }
        {
          right. exact H.
        }
      }
    }
  Qed.

  Fixpoint uses_kt Γ ϕ (pf : Γ ⊢H ϕ) :=
    match pf with
    | hypothesis _ _ _ _ => false
    | P1 _ _ _ _ _ => false
    | P2 _ _ _ _ _ _ _ => false
    | P3 _ _ _ => false
    | Modus_ponens _ _ _ m0 m1
      => uses_kt _ _ m0 || uses_kt _ _ m1
    | Ex_quan _ _ _ _ => false
    | Ex_gen _ _ _ _ _ _ pf' _ => uses_kt _ _ pf'
    | Prop_bott_left _ _ _ => false
    | Prop_bott_right _ _ _ => false
    | Prop_disj_left _ _ _ _ _ _ _ => false
    | Prop_disj_right _ _ _ _ _ _ _ => false
    | Prop_ex_left _ _ _ _ _ => false
    | Prop_ex_right _ _ _ _ _ => false
    | Framing_left _ _ _ _ _ m0 => uses_kt _ _ m0
    | Framing_right _ _ _ _ _ m0 => uses_kt _ _ m0
    | Svar_subst _ _ _ X _ _ m0 => uses_kt _ _ m0
    | Pre_fixp _ _ _ => false
    | Knaster_tarski _ _ phi psi m0 => true
    | Existence _ => false
    | Singleton_ctx _ _ _ _ _ _ => false
    end.

  Fixpoint propositional_only Γ ϕ (pf : Γ ⊢H ϕ) :=
    match pf with
    | hypothesis _ _ _ _ => true
    | P1 _ _ _ _ _ => true
    | P2 _ _ _ _ _ _ _ => true
    | P3 _ _ _ => true
    | Modus_ponens _ _ _ m0 m1
      => propositional_only _ _ m0 && propositional_only _ _ m1
    | Ex_quan _ _ _ _ => false
    | Ex_gen _ _ _ _ _ _ pf' _ => false
    | Prop_bott_left _ _ _ => false
    | Prop_bott_right _ _ _ => false
    | Prop_disj_left _ _ _ _ _ _ _ => false
    | Prop_disj_right _ _ _ _ _ _ _ => false
    | Prop_ex_left _ _ _ _ _ => false
    | Prop_ex_right _ _ _ _ _ => false
    | Framing_left _ _ _ _ _ m0 => false
    | Framing_right _ _ _ _ _ m0 => false
    | Svar_subst _ _ _ X _ _ m0 => false
    | Pre_fixp _ _ _ => false
    | Knaster_tarski _ _ phi psi m0 => false
    | Existence _ => false
    | Singleton_ctx _ _ _ _ _ _ => false
    end.

  Lemma propositional_implies_no_frame Γ ϕ (pf : Γ ⊢H ϕ) :
    propositional_only Γ ϕ pf = true -> framing_patterns Γ ϕ pf = ∅.
  Proof.
    intros H.
    induction pf; simpl in *; try apply reflexivity; try congruence.
    {
      destruct_and!. specialize (IHpf1 ltac:(assumption)). specialize (IHpf2 ltac:(assumption)).
      rewrite IHpf1. rewrite IHpf2. set_solver.
    }
  Qed.

  Lemma propositional_implies_noKT Γ ϕ (pf : Γ ⊢H ϕ) :
    propositional_only Γ ϕ pf = true -> uses_kt Γ ϕ pf = false.
  Proof.
    induction pf; simpl; intros H; try reflexivity; try congruence.
    { destruct_and!. rewrite IHpf1;[assumption|]. rewrite IHpf2;[assumption|]. reflexivity. }
  Qed.

  Lemma propositional_implies_no_uses_svar Γ ϕ (pf : ML_proof_system Γ ϕ) (SvS : SVarSet) :
    propositional_only Γ ϕ pf = true -> uses_svar_subst SvS Γ ϕ pf = false.
  Proof.
    induction pf; simpl; intros H; try reflexivity; try congruence.
    { destruct_and!. rewrite IHpf1;[assumption|]. rewrite IHpf2;[assumption|]. reflexivity. }
  Qed.

  Lemma propositional_implies_no_uses_ex_gen Γ ϕ (pf : ML_proof_system Γ ϕ) (EvS : EVarSet) :
    propositional_only Γ ϕ pf = true -> uses_ex_gen EvS Γ ϕ pf = false.
  Proof.
    induction pf; simpl; intros H; try reflexivity; try congruence.
    { destruct_and!. rewrite IHpf1;[assumption|]. rewrite IHpf2;[assumption|]. reflexivity. }
  Qed.
  
  Lemma propositional_implies_no_uses_ex_gen_2 Γ ϕ (pf : ML_proof_system Γ ϕ) :
    propositional_only Γ ϕ pf = true -> uses_of_ex_gen Γ ϕ pf = ∅.
  Proof.
    induction pf; simpl; intros H; try reflexivity; try congruence.
    { destruct_and!. rewrite IHpf1;[assumption|]. rewrite IHpf2;[assumption|]. set_solver. }
  Qed.

  Lemma propositional_implies_no_uses_svar_2 Γ ϕ (pf : ML_proof_system Γ ϕ)  :
    propositional_only Γ ϕ pf = true -> uses_of_svar_subst Γ ϕ pf = ∅.
  Proof.
    induction pf; simpl; intros H; try reflexivity; try congruence.
    { destruct_and!. rewrite IHpf1;[assumption|]. rewrite IHpf2;[assumption|]. set_solver. }
  Qed.
    
  Definition proofbpred := forall (Γ : Theory) (ϕ : Pattern),  Γ ⊢H ϕ -> bool.

  Definition indifferent_to_cast (P : proofbpred)
    := forall (Γ : Theory) (ϕ ψ : Pattern) (e: ψ = ϕ) (pf : Γ ⊢H ϕ),
         P Γ ψ (cast_proof e pf) = P Γ ϕ pf.

  Lemma indifferent_to_cast_uses_svar_subst SvS:
    indifferent_to_cast (uses_svar_subst SvS).
  Proof.
   unfold indifferent_to_cast. intros Γ ϕ ψ e pf.
   induction pf; unfold cast_proof; unfold eq_rec_r;
     unfold eq_rec; unfold eq_rect; unfold eq_sym; simpl; auto;
     pose proof (e' := e); move: e; rewrite e'; clear e'; intros e;
     match type of e with
     | ?x = ?x => replace e with (@erefl _ x) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec)
     end; simpl; try reflexivity.
  Qed.

  Lemma indifferent_to_cast_uses_kt:
    indifferent_to_cast uses_kt.
  Proof.
   unfold indifferent_to_cast. intros Γ ϕ ψ e pf.
   induction pf; unfold cast_proof; unfold eq_rec_r;
     unfold eq_rec; unfold eq_rect; unfold eq_sym; simpl; auto;
     pose proof (e' := e); move: e; rewrite e'; clear e'; intros e;
     match type of e with
     | ?x = ?x => replace e with (@erefl _ x) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec)
     end; simpl; try reflexivity.
  Qed.


  Lemma indifferent_to_cast_uses_ex_gen EvS:
    indifferent_to_cast (uses_ex_gen EvS).
  Proof.
   unfold indifferent_to_cast. intros Γ ϕ ψ e pf.
   induction pf; unfold cast_proof; unfold eq_rec_r;
     unfold eq_rec; unfold eq_rect; unfold eq_sym; simpl; auto;
     pose proof (e' := e); move: e; rewrite e'; clear e'; intros e;
     match type of e with
     | ?x = ?x => replace e with (@erefl _ x) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec)
     end; simpl; try reflexivity.
  Qed.

End with_signature.

Definition has_bound_variable_under_mu {Σ : Signature} (ϕ : Pattern) : bool
:= let x := fresh_evar ϕ in
  mu_in_evar_path x (bsvar_subst (patt_free_evar x) 0 ϕ) 0
.

Fixpoint uses_kt_unreasonably {Σ : Signature} Γ ϕ (pf : ML_proof_system Γ ϕ) :=
  match pf with
  | ProofSystem.hypothesis _ _ _ _ => false
  | ProofSystem.P1 _ _ _ _ _ => false
  | ProofSystem.P2 _ _ _ _ _ _ _ => false
  | ProofSystem.P3 _ _ _ => false
  | ProofSystem.Modus_ponens _ _ _ m0 m1
    => uses_kt_unreasonably _ _ m0 || uses_kt_unreasonably _ _ m1
  | ProofSystem.Ex_quan _ _ _ _ => false
  | ProofSystem.Ex_gen _ _ _ _ _ _ pf' _ => uses_kt_unreasonably _ _ pf'
  | ProofSystem.Prop_bott_left _ _ _ => false
  | ProofSystem.Prop_bott_right _ _ _ => false
  | ProofSystem.Prop_disj_left _ _ _ _ _ _ _ => false
  | ProofSystem.Prop_disj_right _ _ _ _ _ _ _ => false
  | ProofSystem.Prop_ex_left _ _ _ _ _ => false
  | ProofSystem.Prop_ex_right _ _ _ _ _ => false
  | ProofSystem.Framing_left _ _ _ _ _ m0 => uses_kt_unreasonably _ _ m0
  | ProofSystem.Framing_right _ _ _ _ _ m0 => uses_kt_unreasonably _ _ m0
  | ProofSystem.Svar_subst _ _ _ X _ _ m0 => uses_kt_unreasonably _ _ m0
  | ProofSystem.Pre_fixp _ _ _ => false
  | ProofSystem.Knaster_tarski _ phi psi wf m0 =>
    (*has_bound_variable_under_mu phi ||*)
    ~~ (bound_svar_is_banned_under_mus phi 0 0) ||
    uses_kt_unreasonably _ _ m0
  | ProofSystem.Existence _ => false
  | ProofSystem.Singleton_ctx _ _ _ _ _ _ => false
  end.

  Lemma indifferent_to_cast_uses_kt_unreasonably {Σ : Signature}:
    indifferent_to_cast uses_kt_unreasonably.
  Proof.
   unfold indifferent_to_cast. intros Γ ϕ ψ e pf.
   induction pf; unfold cast_proof; unfold eq_rec_r;
     unfold eq_rec; unfold eq_rect; unfold eq_sym; simpl; auto;
     pose proof (e' := e); move: e; rewrite e'; clear e'; intros e;
     match type of e with
     | ?x = ?x => replace e with (@erefl _ x) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec)
     end; simpl; try reflexivity.
  Qed.

Lemma kt_unreasonably_implies_somehow {Σ : Signature} Γ ϕ (pf : ML_proof_system Γ ϕ) :
  uses_kt_unreasonably Γ ϕ pf -> uses_kt Γ ϕ pf.
Proof.
  induction pf; cbn; auto with nocore.
  { intros H. unfold is_true in *. rewrite orb_true_iff in H.
    destruct H as [H|H].
    {
      specialize (IHpf1 H).
      rewrite IHpf1.
      reflexivity.
    }
    {
      specialize (IHpf2 H).
      rewrite IHpf2.
      rewrite orb_true_r.
      reflexivity.
    }
  }
  {
    intros _. reflexivity.
  }
Qed.

Arguments uses_svar_subst {Σ} S {Γ} {ϕ} pf : rename.
Arguments uses_kt {Σ} {Γ} {ϕ} pf : rename.
Arguments uses_kt_unreasonably {Σ} {Γ} {ϕ} pf : rename.
Arguments uses_ex_gen {Σ} E {Γ} {ϕ} pf : rename.


Section proof_constraint.
  Context {Σ : Signature}.

  Lemma instantiate_named_axiom (NA : NamedAxioms) (name : (NAName NA)) :
    (theory_of_NamedAxioms NA) ⊢H (@NAAxiom Σ NA name).
  Proof.
    apply hypothesis.
    { apply NAwf. }
    unfold theory_of_NamedAxioms.
    apply propset.elem_of_PropSet.
    exists name.
    reflexivity.
  Defined.



  Definition coEVarSet := coGset evar.
  Definition coSVarSet := coGset svar.
  Definition WfpSet := gmap.gset wfPattern.
  Definition coWfpSet := coGset wfPattern.

  Record ProofInfo :=
    mkProofInfo
    {
      pi_generalized_evars : coEVarSet ;
      pi_substituted_svars : coSVarSet ;
      pi_uses_kt : bool ;
      pi_uses_advanced_kt : bool ;
      (* pi_framing_patterns : coWfpSet ;  *)
    }.

  Definition ProofInfoLe (i₁ i₂ : ProofInfo) : Prop :=
    pi_generalized_evars i₁ ⊆ pi_generalized_evars i₂ /\
    pi_substituted_svars i₁ ⊆ pi_substituted_svars i₂ /\
    (pi_uses_kt i₁ ==> pi_uses_kt i₂) /\
    (pi_uses_advanced_kt i₁ ==> pi_uses_advanced_kt i₂)
  .


  (* A proof together with some properties of it. *)
  Record ProofInfoMeaning
    (Γ : Theory)
    (ϕ : Pattern)
    (pwi_pf : Γ ⊢H ϕ)
    (pi : ProofInfo)
    : Prop
    :=
  mkProofInfoMeaning
  {
    pwi_pf_ge : gset_to_coGset (@uses_of_ex_gen Σ Γ ϕ pwi_pf) ⊆ pi_generalized_evars pi ;
    pwi_pf_svs : gset_to_coGset (@uses_of_svar_subst Σ Γ ϕ pwi_pf) ⊆ pi_substituted_svars pi ;
    pwi_pf_kt : implb (@uses_kt Σ Γ ϕ pwi_pf) (pi_uses_kt pi) ;
    pwi_pf_kta : implb (@uses_kt_unreasonably Σ Γ ϕ pwi_pf) (pi_uses_advanced_kt pi && (@uses_kt Σ Γ ϕ pwi_pf)) ;
    (* pwi_pf_fp : gset_to_coGset (@framing_patterns Σ Γ ϕ pwi_pf) ⊆ (pi_framing_patterns pi) ; *)
  }.

  Definition ProofLe (i₁ i₂ : ProofInfo) :=
    forall (Γ : Theory) (ϕ : Pattern) (pf : Γ ⊢H ϕ),
      @ProofInfoMeaning Γ ϕ pf i₁ -> @ProofInfoMeaning Γ ϕ pf i₂.


  Lemma ProofInfoLe_ProofLe (i₁ i₂ : ProofInfo) :
    ProofInfoLe i₁ i₂ -> ProofLe i₁ i₂.
  Proof.
    intros H. intros Γ φ pf Hpf. destruct Hpf.
    destruct H as [HEV [HSV [HKT HKTA] ] ].
    constructor. 1-2: set_solver.
    {
      apply implb_true_iff.
      pose proof (proj1 (implb_true_iff _ _) HKT).
      pose proof (proj1 (implb_true_iff _ _) pwi_pf_kt0).
      tauto.
    }
    {
      apply implb_true_iff.
      pose proof (H1 := proj1 (implb_true_iff _ _) HKTA).
      pose proof (H2 := proj1 (implb_true_iff _ _) pwi_pf_kta0).
      intro H.
      rewrite andb_true_iff.
      specialize (H2 H).
      unfold is_true in pwi_pf_kta0.
      rewrite implb_true_iff in pwi_pf_kta0.
      specialize (pwi_pf_kta0 H).
      split.
      {
        apply H1. clear H1.
        rewrite andb_true_iff in pwi_pf_kta0.
        apply pwi_pf_kta0.
      }
      rewrite andb_true_iff in H2. apply H2.
    }
  Qed.

End proof_constraint.

  Ltac convert_implb :=
  unfold is_true in *;
  match goal with
  | |- context G [implb _ _ = true] => rewrite implb_true_iff
  | H : context G [implb _ _ = true] |- _ => rewrite implb_true_iff in H
  end.

  Ltac convert_orb :=
  unfold is_true in *;
  match goal with
  | |- context G [orb _ _ = true] => rewrite orb_true_iff
  | H : context G [orb _ _ = true] |- _ => rewrite orb_true_iff in H
  end.

  Ltac convert_andb :=
  unfold is_true in *;
  match goal with
  | |- context G [orb _ _ = true] => rewrite andb_true_iff
  | H : context G [orb _ _ = true] |- _ => rewrite andb_true_iff in H
  end.

  Ltac destruct_pile :=
    match goal with
    | H : @ProofInfoLe _ _ _ |- _ => destruct H as [? [? ?] ]
    end.

  (** To solve goals shaped like: ProofInfoLe i₁ i₂ *)
  Ltac try_solve_pile :=
    assumption + (* optimization *)
    (repeat destruct_pile;
    simpl in *;
    split; [try set_solver|split;[try set_solver
    |try (repeat convert_implb;
          repeat convert_orb;
          repeat convert_andb;
          set_solver)] ]).

Section proof_info.
  Context {Σ : Signature}.
  Import Notations_private.
  (*
  #[global]
  Instance
  *)
  Lemma pile_refl (i : ProofInfo) : ProofInfoLe i i.
  Proof.
    try_solve_pile. 
  Qed.

  (*
  #[global]
  Instance
  *)
  Lemma pile_trans
    (i₁ i₂ i₃ : ProofInfo) (PILE12 : ProofInfoLe i₁ i₂) (PILE23 : ProofInfoLe i₂ i₃)
  : ProofInfoLe i₁ i₃.
  Proof.
    try_solve_pile.
  Qed.

  Definition BasicReasoning : ProofInfo := ((@mkProofInfo _ ∅ ∅ false false)).
  Definition AnyReasoning : ProofInfo := (@mkProofInfo _ ⊤ ⊤ true true).


  Definition derives_using Γ ϕ pi
  := ({pf : Γ ⊢H ϕ | @ProofInfoMeaning _ _ _ pf pi }).

  Definition derives Γ ϕ
  := derives_using Γ ϕ AnyReasoning.

  Definition raw_proof_of {Γ} {ϕ} {pi}:
    derives_using Γ ϕ pi ->
    ML_proof_system Γ ϕ
  := fun pf => proj1_sig pf.

End proof_info.


Module Notations.

Notation "Γ '⊢i' ϕ 'using' pi"
:= (derives_using Γ ϕ pi)  (at level 95, no associativity).

Notation "Γ ⊢ ϕ" := (derives Γ ϕ)
(at level 95, no associativity).

Notation "'ExGen' ':=' evs ',' 'SVSubst' := svs ',' 'KT' := bkt ',' 'AKT' := akt"
  := (@mkProofInfo _ evs svs bkt akt) (at level 95, no associativity).

End Notations.

(* We cannot turn a proof into wellformedness hypotheses
   if there is a ProofLe hypothesis depending on the proof
  *)
Ltac2 clear_piles () :=
  repeat (
    lazy_match! goal with
    | [ h : @ProofInfoLe _ _ _ |- _]
      => clear $h
      | [ h : @ProofLe _ _ _ |- _]
      => clear $h
      | [ h : @ProofInfoMeaning _ _ _ _ _ |- _]
      => clear $h
    end
  )
.  

Ltac2 pfs_to_wfs () :=
  repeat (
    match! goal with
    | [h : @derives _ _ _ |- _]
      => unfold derives
    | [h : @derives_using _ _ _ _ |- _]
      => apply @raw_proof_of in $h
    | [ h: @ML_proof_system _ _ _ |- _]
      => apply @proved_impl_wf in $h
    end
  ).


Ltac2 Set proved_hook_wfauto as oldhook
:= (fun () => (*Message.print (Message.of_string "hook_wfauto p2w");*) clear_piles (); pfs_to_wfs () (*; oldhook ()*)).

(*
Ltac2 Set hook_wfauto
:= (fun () => Message.print (Message.of_string "hook_wfauto p2w")).
*)



(** For goals shaped like ProoInforMeeaning _ _ _ BasicReasoning *)
Ltac solve_pim_simple := constructor; simpl;[(set_solver)|(set_solver)|(reflexivity)|(reflexivity)].

Import Notations.

Lemma useBasicReasoning {Σ : Signature} {Γ : Theory} {ϕ : Pattern} (i : ProofInfo) :
  Γ ⊢i ϕ using BasicReasoning ->
  Γ ⊢i ϕ using i.
Proof.
  intros H.
  pose proof (Hpf := proj2_sig H).
  remember (proj1_sig H) as _H.
  exists (_H).
  clear Heq_H.
  destruct Hpf as [Hpf1 Hpf2 Hpf3 Hpf4].
  destruct i; constructor; simpl in *;
  [set_solver|set_solver|idtac|idtac].
  {
    (destruct (uses_kt _H); simpl in *; try congruence).
  }
  {
    (destruct (uses_kt_unreasonably _H); simpl in *; try congruence).
  }
Defined.


Tactic Notation "remember_constraint" "as" ident(i') :=
    match goal with
    | [|- (_ ⊢i _ using ?constraint)] => remember constraint as i'
    end.

Lemma useGenericReasoning  {Σ : Signature} (Γ : Theory) (ϕ : Pattern) i' i:
  (ProofInfoLe i' i) ->
  Γ ⊢i ϕ using i' ->
  Γ ⊢i ϕ using i.
Proof.
  intros pile [pf Hpf].
  exists pf.

  destruct Hpf as [Hpf2 Hpf3 Hpf4 Hpf5].
  destruct i, i'; cbn in *.
  destruct pile as [H [H0 H1] ].
  constructor; simpl.
  { set_solver. }
  { set_solver. }
  { simpl in *. apply implb_true_iff.
    unfold is_true in *. rewrite implb_true_iff in Hpf4 H1.
    set_solver.
  }
  {
    simpl in *. apply implb_true_iff.
    unfold is_true in *. rewrite implb_true_iff in Hpf5 H1.
    destruct H1 as [H11 H12].
    rewrite implb_true_iff in H11.
    rewrite implb_true_iff in H12.
    intros H'.
    naive_solver.
  }
Defined.

Tactic Notation "gapply" uconstr(pf) := eapply useGenericReasoning;[|eapply pf].

Tactic Notation "gapply" uconstr(pf) "in" ident(H) :=
  eapply useGenericReasoning in H;[|apply pf].

Lemma pile_any {Σ : Signature} i:
  ProofInfoLe i AnyReasoning.
Proof.
  try_solve_pile.
Qed.

Tactic Notation "aapply" uconstr(pf)
  := gapply pf; try apply pile_any.

Lemma pile_basic_generic {Σ : Signature} i:
  ProofInfoLe BasicReasoning i.
Proof.
  try_solve_pile.
Qed.

Lemma pile_impl_allows_gen_x {Σ : Signature} x gpi svs kt:
  ProofInfoLe ( (ExGen := {[x]}, SVSubst := svs, KT := kt, AKT := false)) ( gpi) ->
  x ∈ pi_generalized_evars gpi.
Proof.
  destruct gpi. intro H.
  destruct_pile. set_solver.
Qed.

Lemma pile_impl_uses_kt {Σ : Signature} gpi evs svs:
  ProofInfoLe ( (ExGen := evs, SVSubst := svs, KT := true, AKT := false)) ( gpi) ->
  pi_uses_kt gpi.
Proof.
  destruct gpi. intro H.
  destruct_pile. set_solver.
Qed.

Lemma pile_impl_allows_svsubst_X {Σ : Signature} gpi evs X kt:
  ProofInfoLe ( (ExGen := evs, SVSubst := {[X]}, KT := kt, AKT := false)) ( gpi) ->
  X ∈ pi_substituted_svars gpi.
Proof.
  destruct gpi. intro H.
  destruct_pile. set_solver.
Qed.

Lemma liftProofLe {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (i₁ i₂ : ProofInfo)
  {pile : ProofLe i₁ i₂}
  :
  Γ ⊢i ϕ using i₁ ->
  Γ ⊢i ϕ using i₂.
Proof.
    intros [pf Hpf].
    apply pile in Hpf.
    exists pf.
    exact Hpf.
Qed.

Lemma liftProofInfoLe {Σ : Signature} (Γ : Theory) (ϕ : Pattern) (i₁ i₂ : ProofInfo)
  {pile : ProofInfoLe i₁ i₂}
  :
  Γ ⊢i ϕ using i₁ ->
  Γ ⊢i ϕ using i₂.
Proof.
    intros H.
    eapply liftProofLe.
    apply ProofInfoLe_ProofLe.
    all: eassumption.
Qed.

Tactic Notation "use" constr(i) "in" ident(H) :=
  apply liftProofInfoLe with (i₂ := i) in H; [|try_solve_pile].

Close Scope ml_scope.