From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Logic.Classical_Prop Logic.Eqdep_dec.
From MatchingLogic.Utils Require Import stdpp_ext Lattice.
From MatchingLogic Require Import Syntax NamedAxioms DerivedOperators_Syntax monotonic wftactics.
From stdpp Require Import base fin_sets sets propset.

From MatchingLogic.Utils Require Import extralibrary.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.

Section ml_proof_system.
  Open Scope ml_scope.

  Context {Σ : Signature}.

  
  (* Proof system for AML ref. snapshot: Section 3 *)

  Reserved Notation "theory ⊢ pattern" (at level 76).
  Inductive ML_proof_system (theory : Theory) :
    Pattern -> Set :=

  (* Hypothesis *)
  | hypothesis (axiom : Pattern) :
      well_formed axiom ->
      (axiom ∈ theory) -> theory ⊢ axiom
                                              
  (* FOL reasoning *)
  (* Propositional tautology *)
  | P1 (phi psi : Pattern) :
      well_formed phi -> well_formed psi ->
      theory ⊢ (phi ---> (psi ---> phi))
  | P2 (phi psi xi : Pattern) :
      well_formed phi -> well_formed psi -> well_formed xi ->
      theory ⊢ ((phi ---> (psi ---> xi)) ---> ((phi ---> psi) ---> (phi ---> xi)))
  | P3 (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (((phi ---> Bot) ---> Bot) ---> phi)

  (* Modus ponens *)
  | Modus_ponens (phi1 phi2 : Pattern) :
      theory ⊢ phi1 ->
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ phi2

  (* Existential quantifier *)
  | Ex_quan (phi : Pattern) (y : evar) :
      well_formed (patt_exists phi) ->
      theory ⊢ (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi))

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Pattern) (x : evar) :
      well_formed phi1 -> well_formed phi2 ->
      theory ⊢ (phi1 ---> phi2) ->
      x ∉ (free_evars phi2) ->
      theory ⊢ (exists_quantify x phi1 ---> phi2)

  (* Frame reasoning *)
  (* Propagation bottom *)
  | Prop_bott_left (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (patt_bott $ phi ---> patt_bott)

  | Prop_bott_right (phi : Pattern) :
      well_formed phi ->
      theory ⊢ (phi $ patt_bott ---> patt_bott)

  (* Propagation disjunction *)
  | Prop_disj_left (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->
      theory ⊢ (((phi1 or phi2) $ psi) ---> ((phi1 $ psi) or (phi2 $ psi)))

  | Prop_disj_right (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->
      theory ⊢ ((psi $ (phi1 or phi2)) ---> ((psi $ phi1) or (psi $ phi2)))

  (* Propagation exist *)
  | Prop_ex_left (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢ (((ex , phi) $ psi) ---> (ex , phi $ psi))

  | Prop_ex_right (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢ ((psi $ (ex , phi)) ---> (ex , psi $ phi))

  (* Framing *)
  | Framing_left (phi1 phi2 psi : Pattern) :
      well_formed psi ->
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((phi1 $ psi) ---> (phi2 $ psi))

  | Framing_right (phi1 phi2 psi : Pattern) :
      well_formed psi ->
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((psi $ phi1) ---> (psi $ phi2))

  (* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | Svar_subst (phi psi : Pattern) (X : svar) :
      well_formed phi -> well_formed psi ->
      theory ⊢ phi -> theory ⊢ (free_svar_subst phi psi X)

  (* Pre-Fixpoint *)
  | Pre_fixp (phi : Pattern) :
      well_formed (patt_mu phi) ->
      theory ⊢ (instantiate (patt_mu phi) (patt_mu phi) ---> (patt_mu phi))

  (* Knaster-Tarski *)
  | Knaster_tarski (phi psi : Pattern) :
      well_formed (patt_mu phi) ->
      theory ⊢ ((instantiate (patt_mu phi) psi) ---> psi) ->
      theory ⊢ ((@patt_mu Σ phi) ---> psi)

  (* Technical rules *)
  (* Existence *)
  | Existence : theory ⊢ (ex , patt_bound_evar 0)

  (* Singleton *)
  | Singleton_ctx (C1 C2 : Application_context) (phi : Pattern) (x : evar) :
      well_formed phi ->
      theory ⊢ (! ((subst_ctx C1 (patt_free_evar x and phi)) and
                   (subst_ctx C2 (patt_free_evar x and (! phi)))))

  where "theory ⊢ pattern" := (ML_proof_system theory pattern).

  Instance ML_proof_system_eqdec: forall gamma phi, EqDecision (ML_proof_system gamma phi).
  Proof. intros. intros x y. 
         unfold Decision. Fail decide equality.
  Abort.


Lemma cast_proof {Γ} {ϕ} {ψ} (e : ψ = ϕ) : ML_proof_system Γ ϕ -> ML_proof_system Γ ψ.
Proof. intros H. rewrite <- e in H. exact H. Defined.

Fixpoint framing_patterns Γ ϕ (pf : Γ ⊢ ϕ) : list Pattern :=
  match pf with
  | hypothesis _ _ _ _ => []
  | P1 _ _ _ _ _ => []
  | P2 _ _ _ _ _ _ _ => []
  | P3 _ _ _ => []
  | Modus_ponens _ _ _ m0 m1
    => (@framing_patterns _ _ m0) ++ (@framing_patterns _ _ m1)
  | Ex_quan _ _ _ _ => []
  | Ex_gen _ _ _ x _ _ pf _ => @framing_patterns _ _ pf
  | Prop_bott_left _ _ _ => []
  | Prop_bott_right _ _ _ => []
  | Prop_disj_left _ _ _ _ _ _ _ => []
  | Prop_disj_right _ _ _ _ _ _ _ => []
  | Prop_ex_left _ _ _ _ _ => []
  | Prop_ex_right _ _ _ _ _ => []
  | Framing_left _ _ _ psi _ m0 => psi :: (@framing_patterns _ _ m0)
  | Framing_right _ _ _ psi _ m0 => psi :: (@framing_patterns _ _ m0)
  | Svar_subst _ _ _ _ _ _ m0 => @framing_patterns _ _ m0
  | Pre_fixp _ _ _ => []
  | Knaster_tarski _ _ phi psi m0 => @framing_patterns _ _ m0
  | Existence _ => []
  | Singleton_ctx _ _ _ _ _ _ => []
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

  Fixpoint uses_svar_subst (S : SVarSet) Γ ϕ (pf : Γ ⊢ ϕ) :=
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

    Fixpoint uses_of_svar_subst Γ ϕ (pf : Γ ⊢ ϕ) : SVarSet :=
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

  Fixpoint uses_kt Γ ϕ (pf : Γ ⊢ ϕ) :=
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

    Fixpoint propositional_only Γ ϕ (pf : Γ ⊢ ϕ) :=
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
  
  Lemma propositional_implies_no_frame Γ ϕ (pf : Γ ⊢ ϕ) :
    propositional_only Γ ϕ pf = true -> framing_patterns Γ ϕ pf = [].
  Proof.
    intros H.
    induction pf; simpl in *; try apply reflexivity; try congruence.
    {
      destruct_and!. specialize (IHpf1 ltac:(assumption)). specialize (IHpf2 ltac:(assumption)).
      rewrite IHpf1. rewrite IHpf2. reflexivity.
    }
  Qed.

  Lemma propositional_implies_noKT Γ ϕ (pf : Γ ⊢ ϕ) :
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

  Definition proofbpred := forall (Γ : Theory) (ϕ : Pattern),  Γ ⊢ ϕ -> bool.

  Definition indifferent_to_cast (P : proofbpred)
    := forall (Γ : Theory) (ϕ ψ : Pattern) (e: ψ = ϕ) (pf : Γ ⊢ ϕ),
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

  Lemma indifferent_to_cast_propositional_only :
    indifferent_to_cast propositional_only.
  Proof.
    unfold indifferent_to_cast. intros Γ ϕ ψ e pf.
    induction pf; unfold cast_proof; unfold eq_rec_r;
      unfold eq_rec; unfold eq_rect; unfold eq_sym; simpl; auto;
      pose proof (e' := e); move: e; rewrite e'; clear e'; intros e;
      match type of e with
      | ?x = ?x => replace e with (@erefl _ x) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec)
      end; simpl; try reflexivity.
  Qed.

  Definition indifferent_to_prop (P : proofbpred) :=
      (forall Γ phi psi wfphi wfpsi, P Γ _ (P1 Γ phi psi wfphi wfpsi) = false)
   /\ (forall Γ phi psi xi wfphi wfpsi wfxi, P Γ _ (P2 Γ phi psi xi wfphi wfpsi wfxi) = false)
   /\ (forall Γ phi wfphi, P Γ _ (P3 Γ phi wfphi) = false)
   /\ (forall Γ phi1 phi2 pf1 pf2,
        P Γ _ (Modus_ponens Γ phi1 phi2 pf1 pf2)
        = P Γ _ pf1 || P Γ _ pf2
      ).

  Lemma indifferent_to_prop_uses_svar_subst SvS:
    indifferent_to_prop (uses_svar_subst SvS).
  Proof.
    split;[auto|].
    split;[auto|].
    split;[auto|].
    intros. simpl. reflexivity.
  Qed.

  Lemma indifferent_to_prop_uses_kt:
    indifferent_to_prop uses_kt.
  Proof.
    split;[auto|].
    split;[auto|].
    split;[auto|].
    intros. simpl. reflexivity.
  Qed.


  Lemma indifferent_to_prop_uses_ex_gen EvS:
    indifferent_to_prop (uses_ex_gen EvS).
  Proof.
    split;[auto|].
    split;[auto|].
    split;[auto|].
    intros. simpl. reflexivity.
  Qed.

  Lemma proved_impl_wf Γ ϕ:
    Γ ⊢ ϕ -> well_formed ϕ.
  Proof.
    intros pf.
    induction pf; auto; try (solve [wf_auto2]).
    - unfold free_svar_subst. wf_auto2.
      apply wfp_free_svar_subst_1; auto; unfold well_formed_closed; split_and; assumption.
      all: fold free_svar_subst.
      apply wfc_mu_free_svar_subst; auto.
      apply wfc_ex_free_svar_subst; auto.
  Qed.

End ml_proof_system.

Arguments uses_svar_subst {Σ} S {Γ} {ϕ} pf : rename.
Arguments uses_kt {Σ} {Γ} {ϕ} pf : rename.
Arguments uses_ex_gen {Σ} E {Γ} {ϕ} pf : rename.

Module Notations.

  Notation "theory ⊢ pattern" := (ML_proof_system theory pattern) (at level 95, no associativity).

End Notations.

Import Notations.

Lemma instantiate_named_axiom {Σ : Signature} (NA : NamedAxioms) (name : (NAName NA)) :
  (theory_of_NamedAxioms NA) ⊢ (@NAAxiom Σ NA name).
Proof.
  apply hypothesis.
  { apply NAwf. }
  unfold theory_of_NamedAxioms.
  apply elem_of_PropSet.
  exists name.
  reflexivity.
Defined.
