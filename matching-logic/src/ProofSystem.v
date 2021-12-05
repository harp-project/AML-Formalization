From Coq Require Import ssreflect ssrfun ssrbool.

From Coq Require Import Logic.Classical_Prop Logic.Eqdep_dec.
From MatchingLogic.Utils Require Import stdpp_ext Lattice.
From MatchingLogic Require Import Syntax NamedAxioms Semantics DerivedOperators monotonic.
From stdpp Require Import base fin_sets sets propset.

From Equations Require Import Equations.

From MatchingLogic.Utils Require Import extralibrary.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators.Notations.

Section ml_proof_system.
  Open Scope ml_scope.

  Context {signature : Syntax.Signature}.

  (* soundness for prop_ex_right *)
  Lemma proof_rule_prop_ex_right_sound {m : Model} (theory : Theory) (phi psi : Pattern)
        (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)):
    (well_formed (patt_imp (patt_app (patt_exists phi) psi) (patt_exists (patt_app phi psi)))) ->
    (well_formed (ex, phi)) -> (@well_formed signature psi) ->
    (∀ axiom : Pattern,
        axiom ∈ theory
        → ∀ (evar_val : evar → Domain m) (svar_val : svar → Power (Domain m)),
          pattern_interpretation evar_val svar_val axiom = ⊤) ->
    pattern_interpretation evar_val svar_val ((ex , phi) $ psi ---> ex , phi $ psi) = ⊤.
  Proof.
    intros Hwf H H0 Hv.
    rewrite -> pattern_interpretation_imp_simpl.

    remember (pattern_interpretation evar_val svar_val (patt_app (patt_exists phi) psi)) as Xex.
    assert (Huxex: (⊤ ∖ Xex) ∪ Xex = ⊤).
    { clear.
      set_unfold. intros x. split; intros H. exact I.
      destruct (classic (x ∈ Xex)). right. assumption. left. auto.
    }
    rewrite -> set_eq_subseteq.
    split.
    - rewrite <- Huxex.
      rewrite -> elem_of_subseteq. intros x H1.
      inversion H1.
      + left. rewrite -> Huxex in H2. exact H2.
      + rewrite Huxex. apply elem_of_top'.
    - rewrite -> pattern_interpretation_ex_simpl. simpl.
      rewrite -> elem_of_subseteq.
      intros x _.
      destruct (classic (x ∈ Xex)).
      2: { left. clear -H1. set_solver. }
      right. unfold stdpp_ext.propset_fa_union.
      rewrite -> elem_of_PropSet.
      rewrite -> HeqXex in H1.
      rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_ex_simpl in H1.
      simpl in H1.
      unfold stdpp_ext.propset_fa_union in H1.
      unfold app_ext in H1.
      rewrite -> elem_of_PropSet in H1.
      destruct H1 as [le [re [Hunion [Hext_le Happ]]]].
      rewrite -> elem_of_PropSet in Hunion.
      destruct Hunion as [c Hext_re].
      exists c. rewrite -> evar_open_app, -> pattern_interpretation_app_simpl. unfold app_ext.
      rewrite -> elem_of_PropSet.
      exists le, re.
      split.
      + erewrite -> (@interpretation_fresh_evar_open signature m) in Hext_re. exact Hext_re.
        apply set_evar_fresh_is_fresh.
        {
          unfold fresh_evar. simpl. 
          pose(@set_evar_fresh_is_fresh' signature (free_evars phi ∪ free_evars psi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
      + unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!.
        erewrite -> pattern_interpretation_free_evar_independent.
        erewrite -> evar_open_closed.
        split.
        2: { exact Happ. }
        exact Hext_le.
        assumption.
        rewrite -> evar_open_closed.
        {
          unfold fresh_evar. simpl. 
          pose(@set_evar_fresh_is_fresh' signature (free_evars phi ∪ free_evars psi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
        assumption.
  Qed.

(* soundness for prop_ex_left *)
  Lemma proof_rule_prop_ex_left_sound {m : Model} (theory : Theory) (phi psi : Pattern)
        (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)):
    (well_formed (patt_imp (patt_app psi (patt_exists phi)) (patt_exists (patt_app psi phi)))) ->
    (well_formed (ex, phi)) -> (@well_formed signature psi) ->
    (∀ axiom : Pattern,
        axiom ∈ theory
        → ∀ (evar_val : evar → Domain m) (svar_val : svar → Power (Domain m)),
          pattern_interpretation evar_val svar_val axiom = ⊤) ->
    pattern_interpretation evar_val svar_val (psi $ (ex , phi) ---> ex , psi $ phi) = ⊤.
  Proof.
    intros Hwf H H0 Hv.
    rewrite -> pattern_interpretation_imp_simpl.

    remember (pattern_interpretation evar_val svar_val (patt_app psi (patt_exists phi))) as Xex.
    assert (Huxex: (⊤ ∖ Xex) ∪ Xex = ⊤).
    { clear.
      set_unfold. intros x. split; intros H. exact I.
      destruct (classic (x ∈ Xex)). right. assumption. left. auto.
    }
    rewrite -> set_eq_subseteq.
    split.
    - rewrite <- Huxex.
      rewrite -> elem_of_subseteq. intros x H1.
      rewrite Huxex. apply elem_of_top'.
    - rewrite -> pattern_interpretation_ex_simpl. simpl.
      rewrite -> elem_of_subseteq.
      intros x _.
      destruct (classic (x ∈ Xex)).
      2: { left. clear -H1. set_solver. }
      right. unfold stdpp_ext.propset_fa_union.
      rewrite -> elem_of_PropSet.
      rewrite -> HeqXex in H1.
      rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_ex_simpl in H1.
      simpl in H1.
      unfold stdpp_ext.propset_fa_union in H1.
      unfold app_ext in H1.
      rewrite -> elem_of_PropSet in H1.
      destruct H1 as [le [re [Hext_le [Hunion Happ]]]].
      rewrite -> elem_of_PropSet in Hunion.
      destruct Hunion as [c Hext_re].

      exists c. rewrite -> evar_open_app, -> pattern_interpretation_app_simpl. unfold app_ext.
      exists le, re.
      split.
      + erewrite -> evar_open_closed.
        erewrite -> pattern_interpretation_free_evar_independent. exact Hext_le.
        unfold well_formed in H0.
        apply andb_true_iff in H0.
        destruct H0. 
        {
          unfold fresh_evar. simpl. unfold evar_is_fresh_in.
          pose(@set_evar_fresh_is_fresh' signature (free_evars psi ∪ free_evars phi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
        unfold well_formed,well_formed_closed in *. simpl in *.
        destruct_and!.
        assumption.
      + split; try assumption.
        erewrite -> (@interpretation_fresh_evar_open signature m) in Hext_re. exact Hext_re.
        apply set_evar_fresh_is_fresh.
        {
          pose(@set_evar_fresh_is_fresh' signature (free_evars psi ∪ free_evars phi)).
          apply not_elem_of_union in n. destruct n. assumption.
        }
  Qed.

(* free_svar_subst maintains soundness *)
Lemma proof_rule_set_var_subst_sound {m : Model}: ∀ phi psi,
  well_formed_closed phi → well_formed psi →
  (∀ (evar_val : evar → Domain m) (svar_val : svar → Power (Domain m)),
      pattern_interpretation evar_val svar_val phi = Full)
  →
  ∀ X evar_val svar_val,
    @pattern_interpretation signature m evar_val svar_val (free_svar_subst phi psi X) = Full.
Proof.
  intros. pose (H1 evar_val (update_svar_val X 
                                  (pattern_interpretation evar_val svar_val psi) svar_val)).
  erewrite <- free_svar_subst_update_exchange in e. exact e. assumption. unfold well_formed in H. assumption.
Qed.


  Inductive ML_proof_from_theory (Γ : Theory) : Set :=

  (* Hypothesis *)
  | mlp_hypothesis (axiom : Pattern) :
      well_formed axiom ->
      (axiom ∈ Γ) -> ML_proof_from_theory Γ
                                              
  (* FOL reasoning *)
  (* Propositional tautology *)
  | mlp_P1 (phi psi : Pattern) :
      well_formed phi -> well_formed psi ->  ML_proof_from_theory Γ
(*      theory ⊢ (phi ---> (psi ---> phi))*)
  | mlp_P2 (phi psi xi : Pattern) :
      well_formed phi -> well_formed psi -> well_formed xi ->  ML_proof_from_theory Γ
(*      theory ⊢ ((phi ---> (psi ---> xi)) ---> ((phi ---> psi) ---> (phi ---> xi))) *)
  | mlp_P3 (phi : Pattern) :
      well_formed phi -> ML_proof_from_theory Γ
(*      theory ⊢ (((phi ---> Bot) ---> Bot) ---> phi) *)

  (* Modus ponens *)
  | mlp_Modus_ponens (phi1 phi2 : Pattern) :
      well_formed phi1 -> well_formed (phi1 ---> phi2) -> (* If we prove that we can prove only well-formed patterns, then we can remove these well_formedness constraints here. *)
      ML_proof_from_theory Γ ->  ML_proof_from_theory Γ ->  ML_proof_from_theory Γ
(*
      theory ⊢ phi1 ->
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ phi2
*)

  (* Existential quantifier *)
  | mlp_Ex_quan (phi : Pattern) (y : evar) :
      well_formed (patt_exists phi) ->  ML_proof_from_theory Γ
(*      theory ⊢ (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi)) *)

  (* Existential generalization *)
  | mlp_Ex_gen (phi1 phi2 : Pattern) (x : evar) :
      well_formed phi1 -> well_formed phi2 ->
      ML_proof_from_theory Γ ->
      (* theory ⊢ (phi1 ---> phi2) -> *)
      x ∉ (free_evars phi2) ->  ML_proof_from_theory Γ
      (* theory ⊢ (exists_quantify x phi1 ---> phi2) *)

  (* Frame reasoning *)
  (* Propagation bottom *)
  | mlp_Prop_bott_left (phi : Pattern) :
      well_formed phi -> ML_proof_from_theory Γ
(*      theory ⊢ (patt_bott $ phi ---> patt_bott)*)

  | mlp_Prop_bott_right (phi : Pattern) :
      well_formed phi ->  ML_proof_from_theory Γ
(*      theory ⊢ (phi $ patt_bott ---> patt_bott) *)

  (* Propagation disjunction *)
  | mlp_Prop_disj_left (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->  ML_proof_from_theory Γ
(*      theory ⊢ (((phi1 or phi2) $ psi) ---> ((phi1 $ psi) or (phi2 $ psi))) *)

  | mlp_Prop_disj_right (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->  ML_proof_from_theory Γ
(*      theory ⊢ ((psi $ (phi1 or phi2)) ---> ((psi $ phi1) or (psi $ phi2))) *)

  (* Propagation exist *)
  | mlp_Prop_ex_left (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->  ML_proof_from_theory Γ
(*      theory ⊢ (((ex , phi) $ psi) ---> (ex , phi $ psi)) *)

  | mlp_Prop_ex_right (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->  ML_proof_from_theory Γ
(*      theory ⊢ ((psi $ (ex , phi)) ---> (ex , psi $ phi)) *)

  (* Framing *)
  | mlp_Framing_left (phi1 phi2 psi : Pattern) :
      well_formed psi ->
      ML_proof_from_theory Γ ->  ML_proof_from_theory Γ
(*
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((phi1 $ psi) ---> (phi2 $ psi)) *)

  | mlp_Framing_right (phi1 phi2 psi : Pattern) :
      well_formed psi ->  ML_proof_from_theory Γ -> ML_proof_from_theory Γ
(*
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((psi $ phi1) ---> (psi $ phi2)) *)

  (* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | mlp_Svar_subst (phi psi : Pattern) (X : svar) :
      well_formed phi -> well_formed psi ->  ML_proof_from_theory Γ -> ML_proof_from_theory Γ
(*
      theory ⊢ phi -> theory ⊢ (free_svar_subst phi psi X) *)

  (* Pre-Fixpoint *)
  | mlp_Pre_fixp (phi : Pattern) :
      well_formed (patt_mu phi) ->  ML_proof_from_theory Γ
(*
      theory ⊢ (instantiate (patt_mu phi) (patt_mu phi) ---> (patt_mu phi)) *)

  (* Knaster-Tarski *)
  | mlp_Knaster_tarski (phi psi : Pattern) :
      well_formed (patt_mu phi) ->  ML_proof_from_theory Γ ->  ML_proof_from_theory Γ
(*
      theory ⊢ ((instantiate (patt_mu phi) psi) ---> psi) ->
      theory ⊢ ((@patt_mu signature phi) ---> psi)
*)
  (* Technical rules *)
  (* Existence *)
  | mlp_Existence :
    ML_proof_from_theory Γ
(* theory ⊢ (ex , patt_bound_evar 0) *)

  (* Singleton *)
  | mlp_Singleton_ctx (C1 C2 : Application_context) (phi : Pattern) (x : evar) :
      well_formed phi ->
      ML_proof_from_theory Γ (*
      theory ⊢ (! ((subst_ctx C1 (patt_free_evar x and phi)) and
                   (subst_ctx C2 (patt_free_evar x and (! phi))))) *)
  .

  Instance AC_eqdec : EqDecision Application_context.
  Proof.
    unfold EqDecision. intros AC1 AC2. unfold Decision.
    move: AC2.
    induction AC1; intros AC2; destruct AC2; auto.
    - destruct (decide (p = p0)), (IHAC1 AC2); subst; try (right; congruence).
      { left. f_equal. apply proof_irrelevance. }
    - destruct (decide (p = p0)), (IHAC1 AC2); subst; try (right; congruence).
      { left. f_equal. apply proof_irrelevance. }
  Defined.

  Instance ML_proof_from_theory_eqdec (Γ : Theory) : EqDecision (ML_proof_from_theory Γ).
  Proof.
    unfold EqDecision. intros pf1 pf2. unfold Decision.

    move: pf2.
    induction pf1; intros pf2; destruct pf2; auto.

    - destruct (decide (axiom = axiom0)).
      + subst. left. f_equal. apply proof_irrelevance. apply proof_irrelevance.
      + right. congruence.
    - destruct (decide (phi = phi0)), (decide (psi = psi0)); subst; try (right; congruence).
      { subst. left. f_equal. apply proof_irrelevance. apply proof_irrelevance. }
    - destruct (decide (phi = phi0)), (decide (psi = psi0)), (decide (xi = xi0));
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)); subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi1 = phi0)), (decide (phi2 = phi3)); subst; try (right; congruence).
      destruct (IHpf1_1 pf2_1).
      2: { right. congruence. }
      subst.
      destruct (IHpf1_2 pf2_2).
      2: { right. congruence. }
      subst.
      left. f_equal; apply proof_irrelevance.
    - destruct (decide (phi = phi0)), (decide (y = y0)); subst; try (right; congruence).
      { left. f_equal. apply proof_irrelevance. }
    - destruct (decide (phi1 = phi0)), (decide (phi2 = phi3)), (decide (x = x0)), (IHpf1 pf2);
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)); subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)); subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi0 = phi1)), (decide (phi2 = phi3)), (decide (psi = psi0));
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi0 = phi1)), (decide (phi2 = phi3)), (decide (psi = psi0));
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)), (decide (psi = psi0));
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)), (decide (psi = psi0));
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi0 = phi1)), (decide (phi2 = phi3)), (decide (psi = psi0)), (IHpf1 pf2);
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi0 = phi1)), (decide (phi2 = phi3)), (decide (psi = psi0)), (IHpf1 pf2);
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)), (decide (psi = psi0)), (decide (X = X0)), (IHpf1 pf2);
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)); subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)), (decide (psi = psi0)), (IHpf1 pf2); subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
    - destruct (decide (phi = phi0)), (decide (x = x0)), (decide (C1 = C0)), (decide (C2 = C3));
      subst; try (right; congruence).
      { left. f_equal; apply proof_irrelevance. }
  Defined.
      

  Definition Proved_pattern' (Γ : Theory) (pf : ML_proof_from_theory Γ) : Pattern :=
    match pf with
    | mlp_hypothesis _ axiom _ _ => axiom

    | mlp_P1 _ phi psi _ _
      => (phi ---> (psi ---> phi))

    | mlp_P2 _ phi psi xi _ _ _
      => ((phi ---> (psi ---> xi)) ---> ((phi ---> psi) ---> (phi ---> xi)))

    | mlp_P3 _ phi _
      => (((phi ---> Bot) ---> Bot) ---> phi)

    | mlp_Modus_ponens _ phi1 phi2 _ _ pf1 pf2
      => phi2

    | mlp_Ex_quan _ phi y _
      => (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi))

    | mlp_Ex_gen _ phi1 phi2 x _ _ pf _
      => (exists_quantify x phi1 ---> phi2)

    | mlp_Prop_bott_left _ phi _
      => (patt_bott $ phi ---> patt_bott)

    | mlp_Prop_bott_right _ phi _
      => (phi $ patt_bott ---> patt_bott)

    | mlp_Prop_disj_left _ phi1 phi2 psi _ _ _
      => (((phi1 or phi2) $ psi) ---> ((phi1 $ psi) or (phi2 $ psi)))

    | mlp_Prop_disj_right _ phi1 phi2 psi _ _ _ 
      => ((psi $ (phi1 or phi2)) ---> ((psi $ phi1) or (psi $ phi2)))

    | mlp_Prop_ex_left _ phi psi _ _
      => (((ex , phi) $ psi) ---> (ex , phi $ psi))

    | mlp_Prop_ex_right _ phi psi _ _
      => ((psi $ (ex , phi)) ---> (ex , psi $ phi))

    | mlp_Framing_left _ phi1 phi2 psi _ pf
      => ((phi1 $ psi) ---> (phi2 $ psi))

    | mlp_Framing_right _ phi1 phi2 psi _ pf
      => ((psi $ phi1) ---> (psi $ phi2))

    | mlp_Svar_subst _ phi psi X _ _ pf
      => (free_svar_subst phi psi X)

    | mlp_Pre_fixp _ phi _
      => (instantiate (patt_mu phi) (patt_mu phi) ---> (patt_mu phi))

    | mlp_Knaster_tarski _ phi psi _ pf
      => ((@patt_mu signature phi) ---> psi)

    | mlp_Existence _
      => (ex , patt_bound_evar 0)

    | mlp_Singleton_ctx _ C1 C2 phi x _
      => (! ((subst_ctx C1 (patt_free_evar x and phi))
                    and (subst_ctx C2 (patt_free_evar x and (! phi)))))
    end.

  Fixpoint ML_proof_from_theory_wf (Γ : Theory) (pf : ML_proof_from_theory Γ) : Prop :=
    match pf with
    | mlp_hypothesis _ axiom _ _ => True

    | mlp_P1 _ phi psi _ _
      => True

    | mlp_P2 _ phi psi xi _ _ _
      => True

    | mlp_P3 _ phi _
      => True

    | mlp_Modus_ponens _ phi1 phi2 _ _ pf1 pf2
      => (Proved_pattern' Γ pf1 = phi1)
         /\ (Proved_pattern' Γ pf2 = (phi1 ---> phi2))
         /\ ML_proof_from_theory_wf Γ pf1
         /\ ML_proof_from_theory_wf Γ pf2

    | mlp_Ex_quan _ phi y _
      => True

    | mlp_Ex_gen _ phi1 phi2 x _ _ pf _
      => (Proved_pattern' Γ pf = (phi1 ---> phi2))
         /\ ML_proof_from_theory_wf Γ pf

    | mlp_Prop_bott_left _ phi _
      => True

    | mlp_Prop_bott_right _ phi _
      => True

    | mlp_Prop_disj_left _ phi1 phi2 psi _ _ _
      => True

    | mlp_Prop_disj_right _ phi1 phi2 psi _ _ _ 
      => True

    | mlp_Prop_ex_left _ phi psi _ _
      => True

    | mlp_Prop_ex_right _ phi psi _ _
      => True

    | mlp_Framing_left _ phi1 phi2 psi _ pf
      => (Proved_pattern' Γ pf = (phi1 ---> phi2))
         /\ ML_proof_from_theory_wf Γ pf

    | mlp_Framing_right _ phi1 phi2 psi _ pf
      => (Proved_pattern' Γ pf = (phi1 ---> phi2))
         /\ ML_proof_from_theory_wf Γ pf

    | mlp_Svar_subst _ phi psi X _ _ pf
      => (Proved_pattern' Γ pf = phi)
         /\ ML_proof_from_theory_wf Γ pf

    | mlp_Pre_fixp _ phi _
      => True

    | mlp_Knaster_tarski _ phi psi _ pf
      => (Proved_pattern' Γ pf = ((instantiate (patt_mu phi) psi) ---> psi))
         /\ ML_proof_from_theory_wf Γ pf

    | mlp_Existence _
      => True

    | mlp_Singleton_ctx _ C1 C2 phi x _
      => True
    end.


(*
  Definition proof_of (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_from_theory Γ) :=
    Proved_pattern_old Γ pf = Some ϕ.

  Definition valid_proof (Γ : Theory) (pf : ML_proof_from_theory Γ)
    := exists ϕ, proof_of Γ ϕ pf.
  *)
  
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
      well_formed phi1 -> well_formed (phi1 ---> phi2) -> (* If we prove that we can prove only well-formed patterns, then we can remove these well_formedness constraints here. *)
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
      theory ⊢ ((@patt_mu signature phi) ---> psi)

  (* Technical rules *)
  (* Existence *)
  | Existence : theory ⊢ (ex , patt_bound_evar 0)

  (* Singleton *)
  | Singleton_ctx (C1 C2 : Application_context) (phi : Pattern) (x : evar) :
      well_formed phi ->
      theory ⊢ (! ((subst_ctx C1 (patt_free_evar x and phi)) and
                   (subst_ctx C2 (patt_free_evar x and (! phi)))))

  where "theory ⊢ pattern" := (ML_proof_system theory pattern).

  Notation "G |= phi" := (@satisfies signature G phi) (no associativity, at level 50).

  Instance ML_proof_system_eqdec: forall gamma phi, EqDecision (ML_proof_system gamma phi).
  Proof. intros. intros x y. 
         unfold Decision. Fail decide equality.
  Abort.

(* Soundness theorem *)
Theorem Soundness :
  forall phi : Pattern, forall theory : Theory,
  well_formed phi -> (theory ⊢ phi) -> (theory |= phi).
Proof.
  intros phi theory Hwf Hp. unfold satisfies, satisfies_theory, satisfies_model.
  intros m Hv evar_val svar_val. 
  generalize dependent svar_val. generalize dependent evar_val. generalize dependent Hv.
  induction Hp.

  (* hypothesis *)
  - intros Hv evar_val svar_val. apply Hv. assumption.

  (* FOL reasoning - P1 *)
  - intros Hv evar_val svar_val.
    repeat rewrite -> pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }

    assert (Huxphi: (⊤ ∖ Xphi) ∪ Xphi = ⊤).
    { clear.
      set_unfold. intros x. split; intros H. exact I.
      destruct (classic (x ∈ Xphi)). right. assumption. left. auto.
    }

    rewrite <- Huxphi.
    rewrite -> elem_of_subseteq. intros x H.
    rewrite -> elem_of_union.
    destruct (classic (x ∈ Xphi)).
    + right. right. assumption.
    + left. clear -H0. set_solver.

  (* FOL reasoning - P2 *)
  - intros Hv evar_val svar_val.
    repeat rewrite -> pattern_interpretation_imp_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    remember (pattern_interpretation evar_val svar_val xi) as Xxi.
    clear.
    apply set_eq_subseteq. split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq. intros x _.
    destruct (classic (x ∈ Xphi)), (classic (x ∈ Xpsi)), (classic (x ∈ Xxi));
      set_solver.

  (* FOL reasoning - P3 *)
  - intros Hv evar_val svar_val. 
    repeat rewrite -> pattern_interpretation_imp_simpl; rewrite -> pattern_interpretation_bott_simpl.
    remember (pattern_interpretation evar_val svar_val phi) as Xphi.
    clear.
    apply set_eq_subseteq. split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq. intros x _.
    destruct (classic (x ∈ Xphi)); set_solver.

  (* Modus ponens *)
  - intros Hv evar_val svar_val.
    rename i into wfphi1. rename i0 into wfphi1impphi2.
    pose (IHHp2 wfphi1impphi2 Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    unfold Full.
    pose proof (H1 := (IHHp1 wfphi1 Hv evar_val svar_val)).
    unfold Full in H1.
    clear -e H1.
    set_solver.

  (* Existential quantifier *)
  - intros Hv evar_val svar_val.
    simpl.
    rewrite -> pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_ex_simpl.
    simpl.

    rewrite -> element_substitution_lemma with (x := fresh_evar phi).
    2: { apply set_evar_fresh_is_fresh. }
    apply set_eq_subseteq. split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq. intros x _.
    destruct (classic (x ∈ (⊤ ∖
                              (pattern_interpretation
                                 (update_evar_val (fresh_evar phi) (evar_val y) evar_val)
                                 svar_val
                                 (evar_open 0 (fresh_evar phi) phi))))).
    -- left. apply H.
    -- right. unfold not in H.
       rewrite -> elem_of_difference in H.
       unfold stdpp_ext.propset_fa_union.
       rewrite -> elem_of_PropSet.
       exists (evar_val y).
       assert (x
                 ∉ pattern_interpretation (update_evar_val (fresh_evar phi) (evar_val y) evar_val) svar_val
                 (evar_open 0 (fresh_evar phi) phi) → False).
       { intros Hcontra. apply H. split. apply elem_of_top'. apply Hcontra. }
       apply NNPP in H0. exact H0.
       
  (* Existential generalization *)
  - intros Hv evar_val svar_val.
    rename i into H. rename i0 into H0.
    rewrite pattern_interpretation_iff_subset.
    assert (Hwf_imp: well_formed (phi1 ---> phi2)).
    { unfold well_formed. simpl. unfold well_formed in H, H0.
      unfold well_formed_closed. unfold well_formed_closed in H, H0.
      simpl. apply andb_true_iff in H. apply andb_true_iff in H0.
      destruct H as [Hwfp_phi1 Hwfc_phi1].
      destruct H0 as [Hwfp_phi2 Hwfc_phi2].
      unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!.
      split_and!; assumption.
    }
    specialize (IHHp Hwf_imp Hv). clear Hv. clear Hwf_imp.
    assert (H2: forall evar_val svar_val,
               (@pattern_interpretation _ m evar_val svar_val phi1)
                 ⊆
                 (pattern_interpretation evar_val svar_val phi2)
           ).
    { intros. apply pattern_interpretation_iff_subset. apply IHHp. }
    apply pattern_interpretation_subset_union
      with (evar_val0 := evar_val) (svar_val0 := svar_val) (x0 := x) in H2.
    rewrite -> elem_of_subseteq. intros x0 Hphi1.
    rewrite -> elem_of_subseteq in H2.
    destruct H2 with (x0 := x0).
    -- assert (Hinc:
                              (pattern_interpretation evar_val svar_val (exists_quantify x phi1))
                              ⊆
                              (propset_fa_union
                                 (λ e : Domain m, pattern_interpretation
                                                    (update_evar_val x e evar_val) svar_val phi1))).
       { unfold exists_quantify. rewrite pattern_interpretation_ex_simpl. simpl.
         apply propset_fa_union_included.
         setoid_rewrite -> elem_of_subseteq.
         intros c x1 H3.
         remember (fresh_evar (evar_quantify x 0 phi1)) as x2.
         erewrite interpretation_fresh_evar_open with (y := x) in H3.
         3: { apply evar_is_fresh_in_evar_quantify. }
         2: { subst x2. apply set_evar_fresh_is_fresh. }
         unfold well_formed in H.
         apply andb_true_iff in H.
         destruct H as [Hwfp Hwfc].
         unfold well_formed_closed in Hwfc.
         rewrite -> evar_open_evar_quantify in H3.
         assumption.
         unfold well_formed,well_formed_closed in *. simpl in *.
         destruct_and!.
         assumption.
       }
       rewrite -> elem_of_subseteq in Hinc.
       apply Hinc. apply Hphi1.

    -- simpl.
       rewrite pattern_interpretation_free_evar_independent in H1.
       { auto. }
       apply H1.

  (* Propagation bottom - left *)
  - intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_imp_simpl, pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    unfold Full.
    rewrite right_id_L.
    rewrite -> complement_full_iff_empty.
    apply app_ext_bot_l.
    
  (* Propagation bottom - right *)
  - intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_imp_simpl, pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    rewrite right_id_L.
    rewrite -> complement_full_iff_empty.
    apply app_ext_bot_r.

  (* Propagation disjunction - left *)
  - intros Hv evar_val svar_val. 
    unfold patt_or, patt_not. repeat rewrite -> pattern_interpretation_imp_simpl.
    repeat rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    unfold Full.
    rewrite [_ ∪ ∅]right_id_L.
    rewrite [_ ∪ ∅]right_id_L.
    repeat rewrite Compl_Compl_propset.

    remember (app_ext (Xphi1 ∪ Xphi2) Xpsi) as Xext_union.
    rewrite -> set_eq_subseteq.
    split.
    1: { apply top_subseteq. }
    
    rewrite -> elem_of_subseteq.
    intros x _.
    destruct (classic (x ∈ Xext_union)).
    + right. subst Xext_union.
      destruct H as [le [re [Hunion [Hre Happ] ] ] ].
      destruct Hunion.
      * left. exists le, re. repeat split; assumption.
      * right. exists le, re. repeat split; assumption.
    + left. rewrite -> elem_of_compl. apply H.

  (* Propagation disjunction - right *)
  - intros Hv evar_val svar_val. 
    unfold patt_or, patt_not. repeat rewrite -> pattern_interpretation_imp_simpl.
    repeat rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_imp_simpl.
    rewrite -> pattern_interpretation_app_simpl, pattern_interpretation_bott_simpl.
    remember (pattern_interpretation evar_val svar_val phi1) as Xphi1.
    remember (pattern_interpretation evar_val svar_val phi2) as Xphi2.
    remember (pattern_interpretation evar_val svar_val psi) as Xpsi.
    unfold Full.
    rewrite [_ ∪ ∅]right_id_L.
    rewrite [_ ∪ ∅]right_id_L.
    repeat rewrite Compl_Compl_propset.

    remember (app_ext Xpsi (Xphi1 ∪ Xphi2)) as Xext_union.
    rewrite -> set_eq_subseteq.
    split.
    1: { apply top_subseteq. }
    
    rewrite -> elem_of_subseteq.
    intros x _.
    destruct (classic (x ∈ Xext_union)).
    + right. subst Xext_union.
      destruct H as [le [re [Hle [Hunion Happ] ] ] ].
      destruct Hunion.
      * left. exists le, re. repeat split; assumption.
      * right. exists le, re. repeat split; assumption.
    + left. rewrite -> elem_of_compl. apply H.

  (* Propagation exists - left *)
  - intros Hv evar_val svar_val.
    eauto using proof_rule_prop_ex_right_sound.

  (* Propagation exists - right *)
  - intros Hv evar_val svar_val.
    eauto using proof_rule_prop_ex_left_sound.

  (* Framing - left *)
  - intros Hv evar_val svar_val. 
    rewrite -> pattern_interpretation_iff_subset.
    epose (IHHp _ Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    repeat rewrite -> pattern_interpretation_app_simpl.
    rewrite -> elem_of_subseteq. intros.
    destruct H as [le [re [Hphi1 [Hpsi Happ]]]].
    unfold app_ext.
    exists le, re.
    split. apply e. assumption.
    Unshelve.
    split; assumption.
    {
      unfold well_formed in Hwf.
      apply andb_true_iff in Hwf.
      inversion Hwf.
      simpl in H.
      unfold well_formed.
      apply andb_true_iff in H. destruct H as [H1 H2].
      apply andb_true_iff in H1. destruct H1 as [H3 H4].
      apply andb_true_iff in H2. destruct H2 as [H5 H6].
      simpl. rewrite H3. rewrite H5. simpl.
      unfold well_formed_closed.
      unfold well_formed_closed in H0. simpl in H0.
      apply andb_true_iff in H0. destruct H0 as [H01 H02].
      apply andb_true_iff in H01. destruct H01 as [H011 H012].
      apply andb_true_iff in H02. destruct H02 as [H021 H022].
      simpl.
      destruct_and!.
      split_and!; assumption.
    }

  (* Framing - right *)
  - intros Hv evar_val svar_val.
    rewrite -> pattern_interpretation_iff_subset.
    epose (IHHp _ Hv evar_val svar_val) as e.
    rewrite -> pattern_interpretation_iff_subset in e.
    repeat rewrite -> pattern_interpretation_app_simpl.
    rewrite -> elem_of_subseteq. intros.
    destruct H as [le [re [Hphi1 [Hpsi Happ]]]].
    unfold app_ext.
    exists le, re.
    split. assumption.
    Unshelve.
    split. apply e. assumption.
    assumption.
    {
      unfold well_formed in Hwf.
      apply andb_true_iff in Hwf.
      destruct Hwf as [Hwf1 Hwf2].
      simpl in Hwf1. apply andb_true_iff in Hwf1. destruct Hwf1 as [Hwf11 Hwf12].
      apply andb_true_iff in Hwf11. destruct Hwf11 as [Hwf111 Hwf112].
      apply andb_true_iff in Hwf12. destruct Hwf12 as [Hwf121 Hwf122].
      unfold well_formed. simpl.
      rewrite Hwf112. rewrite Hwf122. simpl.
      unfold well_formed_closed in Hwf2. simpl in Hwf2.
      apply andb_true_iff in Hwf2. destruct Hwf2 as [Hwfc1 Hwfc2].
      apply andb_true_iff in Hwfc1. destruct Hwfc1 as [Hwfc3 Hwfc4].
      apply andb_true_iff in Hwfc2. destruct Hwfc2 as [H2fc5 Hwfc6].
      unfold well_formed_closed. simpl.
      destruct_and!. split_and!; assumption.
    }

  (* Set Variable Substitution *)
  - intros. epose proof (IHHp ltac:(auto) Hv ) as IH.
    unfold well_formed in i.
    apply andb_true_iff in i. destruct i as [H1 H2].
    eauto using proof_rule_set_var_subst_sound.

  (* Pre-Fixpoint *)
  - intros Hv evar_val svar_val.
    apply pattern_interpretation_iff_subset. simpl.
    rewrite -> pattern_interpretation_mu_simpl.
    simpl.
    remember (fun S : propset (Domain m) =>
                pattern_interpretation evar_val
                                       (update_svar_val (fresh_svar phi) S svar_val)
                                       (svar_open 0 (fresh_svar phi) phi)) as F.
    pose (OS := Lattice.PropsetOrderedSet (@Domain signature m)).
    pose (L := Lattice.PowersetLattice (@Domain signature m)).
    assert (Ffix : Lattice.isFixpoint F (Lattice.LeastFixpointOf F)).
    { apply Lattice.LeastFixpoint_fixpoint. subst. apply is_monotonic.
      unfold well_formed in Hwf.
      apply andb_true_iff in Hwf.
      destruct Hwf as [Hwfp Hwfc].
      simpl in Hwfp. unfold well_formed_closed in Hwfc. simpl in Hwfc.
      apply andb_true_iff in Hwfp. destruct Hwfp as [Hwfp1 Hwfp2].
      apply andb_true_iff in Hwfp2. destruct Hwfp2 as [Hwfp2 Hwfp3].
      simpl. rewrite Hwfp3. rewrite Hwfp2.
      reflexivity.
      apply set_svar_fresh_is_fresh.
    }
    unfold Lattice.isFixpoint in Ffix.
    assert (Ffix_set : (F (Lattice.LeastFixpointOf F)) = (Lattice.LeastFixpointOf F)).
    { rewrite -> Ffix. reflexivity. }
    rewrite -> set_eq_subseteq in Ffix_set.
    destruct Ffix_set. clear H0.
    eapply transitivity.
    2: { apply H. }
    rewrite -> HeqF.
    epose proof (Hsimpl := pattern_interpretation_mu_simpl).
    specialize (Hsimpl evar_val svar_val phi).
    simpl in Hsimpl. subst OS. subst L.
    rewrite <- Hsimpl.
    
    rewrite <- set_substitution_lemma.
    2: { simpl in Hwf. unfold well_formed in Hwf.
         apply andb_true_iff in Hwf.
         destruct Hwf as [_ Hwfc].
         apply wfc_wfc_ind in Hwfc. inversion Hwfc. subst.
         apply wfc_ind_wfc. assumption.
    }
    2: { apply set_svar_fresh_is_fresh. }
    apply reflexivity.

  (* Knaster-Tarski *)
  - intros Hv evar_val svar_val.
    rewrite -> pattern_interpretation_imp_simpl. rewrite -> pattern_interpretation_mu_simpl.
    simpl.
    remember (fun S : propset (Domain m) =>
                pattern_interpretation evar_val
                                       (update_svar_val (fresh_svar phi) S svar_val)
                                       (svar_open 0 (fresh_svar phi) phi)) as F.

    pose (OS := Lattice.PropsetOrderedSet (@Domain signature m)).
    pose (L := Lattice.PowersetLattice (@Domain signature m)).

    assert (Ffix : Lattice.isFixpoint F (Lattice.LeastFixpointOf F)).
    { apply Lattice.LeastFixpoint_fixpoint. subst. apply is_monotonic.
      unfold well_formed in Hwf.
      apply andb_true_iff in Hwf.
      destruct Hwf as [Hwfp Hwfc].
      simpl in Hwfp. unfold well_formed_closed in Hwfc. simpl in Hwfc.
      apply andb_true_iff in Hwfp. destruct Hwfp as [Hwfp1 Hwfp2].
      apply andb_true_iff in Hwfp1. destruct Hwfp1 as [Hwfp1 Hwfp3].
      simpl. rewrite Hwfp1. rewrite Hwfp3.
      reflexivity.
      apply set_svar_fresh_is_fresh.
    }
    
    unfold Lattice.isFixpoint in Ffix.
    assert (Ffix_set : (F (Lattice.LeastFixpointOf F)) = (Lattice.LeastFixpointOf F)).
    { rewrite -> Ffix. reflexivity. }
    rewrite -> set_eq_subseteq in Ffix_set.
    destruct Ffix_set. clear H0.
    unfold Full.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }

    (* TODO make it a lemma *)
    assert (Hwannabe_lemma: forall (L R : propset (Domain m)),
               (⊤ ⊆ ((⊤ ∖ L) ∪ R)) ↔ (L ⊆ R)).
    { intros L0 R0. clear. split; intros H. set_solver. rewrite -> elem_of_subseteq. intros x _.
      set_unfold in H.
      destruct (classic (x ∈ R0)); set_solver.
    }
    rewrite -> Hwannabe_lemma. clear Hwannabe_lemma.

    pose proof (Htmp := Lattice.LeastFixpoint_LesserThanPrefixpoint).
    specialize (Htmp (propset (Domain m)) OS L F). simpl in Htmp.
    apply Htmp.

    assert (Hwf': well_formed (instantiate (mu , phi) psi ---> psi)).
    { unfold well_formed in Hwf. apply andb_true_iff in Hwf.
      destruct Hwf as [Hwfp Hwfc].
      simpl in Hwfp. apply andb_true_iff in Hwfp. 
      destruct Hwfp as [Hwfp1 Hwfp2].
      simpl in Hwfp1.
      apply wfc_wfc_ind in Hwfc.
      inversion Hwfc. rename H3 into Hwfcpsi. apply wfc_ind_wfc in Hwfcpsi.
      simpl. unfold well_formed. simpl.
      rewrite Hwfp2.
      apply wfc_ind_wfc in H2.

      rewrite wfp_bsvar_subst; auto.
      simpl.

      unfold well_formed,well_formed_closed in *. simpl in *.
      destruct_and!. assumption.
      split_and!; auto.
      unfold well_formed_closed in *. simpl in *.
      destruct_and!.
      split_and!; auto.
      + apply wfc_mu_aux_bsvar_subst; auto.
      + apply wfc_ex_aux_bsvar_subst; auto.
    }
    specialize (IHHp Hwf').
    

    simpl in IHHp.
    unfold well_formed in Hwf.
    apply andb_true_iff in Hwf.
    destruct Hwf as [_ Hwfc]. apply wfc_wfc_ind in Hwfc. inversion Hwfc.
    subst psi0. subst phi0.

    unfold instantiate in Hp.
    apply IHHp with (evar_val:=evar_val) (svar_val:=svar_val) in Hv.
    apply pattern_interpretation_iff_subset in Hv.
    
    subst F.
    rewrite <- set_substitution_lemma.
    apply Hv. apply wfc_ind_wfc in H3. apply H3. apply set_svar_fresh_is_fresh.


  (* Existence *)
  - intros Hv evar_val svar_val.
    assert (pattern_interpretation evar_val svar_val (ex , BoundVarSugar.b0)
            = pattern_interpretation evar_val svar_val (ex , (BoundVarSugar.b0 and Top))).
    { repeat rewrite pattern_interpretation_ex_simpl. simpl.
      apply propset_fa_union_same. intros.
      repeat rewrite pattern_interpretation_imp_simpl.
      repeat rewrite pattern_interpretation_bott_simpl.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite [_ ∪ ∅]right_id_L.
      rewrite difference_empty_L.
      rewrite difference_diag_L.
      rewrite [_ ∪ ∅]right_id_L.
      repeat rewrite Compl_Compl_propset.
      simpl.
      reflexivity.
    }
    unfold Full.
    rewrite H.
    rewrite pattern_interpretation_set_builder.
    { unfold M_predicate. left. simpl. rewrite pattern_interpretation_imp_simpl.
      rewrite pattern_interpretation_bott_simpl.
      clear. set_solver.
    }
    simpl.
    rewrite -> set_eq_subseteq.
    split.
    { apply top_subseteq. }
    rewrite -> elem_of_subseteq. intros x _.
    rewrite -> elem_of_PropSet.
    rewrite pattern_interpretation_imp_simpl.
    clear. set_solver.
    
  (* Singleton *)
  - assert (Hemp: forall (evar_val : evar -> Domain m) svar_val,
               pattern_interpretation
                 evar_val svar_val
                 (subst_ctx C1 (patt_free_evar x and phi)
                            and subst_ctx C2 (patt_free_evar x and (phi ---> Bot)))
               = ∅).
    { intros evar_val svar_val.
      rewrite -> pattern_interpretation_and_simpl.
      destruct (classic (evar_val x ∈ pattern_interpretation evar_val svar_val phi)).
      - rewrite [(pattern_interpretation
                    evar_val svar_val
                    (subst_ctx C2 (patt_free_evar x and (phi ---> Bot))))]
                propagate_context_empty.
        2: { unfold Semantics.Empty. rewrite intersection_empty_r_L. reflexivity. }
        rewrite pattern_interpretation_and_simpl.
        rewrite pattern_interpretation_free_evar_simpl.
        rewrite pattern_interpretation_imp_simpl.
        rewrite pattern_interpretation_bott_simpl.
        unfold Semantics.Empty.
        rewrite right_id_L.
        clear -H. set_solver.
      - rewrite propagate_context_empty.
        2: { unfold Semantics.Empty. rewrite intersection_empty_l_L. reflexivity. }
        rewrite pattern_interpretation_and_simpl.
        rewrite pattern_interpretation_free_evar_simpl.
        clear -H. set_solver.
    }
    intros Hv evar_val svar_val.
    rewrite pattern_interpretation_predicate_not.
    + rewrite Hemp. clear. apply empty_impl_not_full. reflexivity.
    + unfold M_predicate. right. apply Hemp.
Qed.

Lemma cast_proof {Γ} {ϕ} {ψ} (e : ψ = ϕ) : ML_proof_system Γ ϕ -> ML_proof_system Γ ψ.
Proof. intros H. rewrite <- e in H. exact H. Defined.


  Fixpoint uses_ex_gen (EvS : EVarSet) Γ ϕ (pf : ML_proof_system Γ ϕ) :=
    match pf with
    | hypothesis _ _ _ _ => false
    | P1 _ _ _ _ _ => false
    | P2 _ _ _ _ _ _ _ => false
    | P3 _ _ _ => false
    | Modus_ponens _ _ _ _ _ m0 m1
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

  Fixpoint uses_svar_subst (S : SVarSet) Γ ϕ (pf : Γ ⊢ ϕ) :=
    match pf with
    | hypothesis _ _ _ _ => false
    | P1 _ _ _ _ _ => false
    | P2 _ _ _ _ _ _ _ => false
    | P3 _ _ _ => false
    | Modus_ponens _ _ _ _ _ m0 m1
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


  Fixpoint uses_kt Γ ϕ (pf : Γ ⊢ ϕ) :=
    match pf with
    | hypothesis _ _ _ _ => false
    | P1 _ _ _ _ _ => false
    | P2 _ _ _ _ _ _ _ => false
    | P3 _ _ _ => false
    | Modus_ponens _ _ _ _ _ m0 m1
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

  Definition indifferent_to_prop (P : proofbpred) :=
      (forall Γ phi psi wfphi wfpsi, P Γ _ (P1 Γ phi psi wfphi wfpsi) = false)
   /\ (forall Γ phi psi xi wfphi wfpsi wfxi, P Γ _ (P2 Γ phi psi xi wfphi wfpsi wfxi) = false)
   /\ (forall Γ phi wfphi, P Γ _ (P3 Γ phi wfphi) = false)
   /\ (forall Γ phi1 phi2 wfphi1 wfphi2 pf1 pf2,
        P Γ _ (Modus_ponens Γ phi1 phi2 wfphi1 wfphi2 pf1 pf2)
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
    - apply well_formed_not.
      apply well_formed_and.
      + apply wf_sctx.
        apply well_formed_and.
        * reflexivity.
        * assumption.
      + apply wf_sctx.
        apply well_formed_and.
        * reflexivity.
        * apply well_formed_not.
          assumption.
  Qed.

End ml_proof_system.

Arguments uses_svar_subst {Σ} S {Γ} {ϕ} pf : rename.
Arguments uses_kt {Σ} {Γ} {ϕ} pf : rename.
Arguments uses_ex_gen {Σ} E {Γ} {ϕ} pf : rename.

Module Notations.

  Notation "theory ⊢ pattern" := (ML_proof_system theory pattern) (at level 95, no associativity).

End Notations.

Import Notations.

Lemma instantiate_named_axiom {Σ : Syntax.Signature} (NA : NamedAxioms) (name : (NAName NA)) :
  (theory_of_NamedAxioms NA) ⊢ (@NAAxiom Σ NA name).
Proof.
  apply hypothesis.
  { apply NAwf. }
  unfold theory_of_NamedAxioms.
  apply elem_of_PropSet.
  exists name.
  reflexivity.
Defined.
(*
Print ML_proof_system.
Equations? weak_proof_to_proof' {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_from_theory Γ)
      (pateq: Proved_pattern Γ pf = Some ϕ) : ML_proof_system Γ ϕ by struct pf :=
  weak_proof_to_proof' _ _ (@mlp_hypothesis _ _ _) pateq => hypothesis _ _ _ _ ;
  weak_proof_to_proof' _ _ (@mlp_P1 _ _ _ _) pateq => _ ;
  weak_proof_to_proof' _ _ (@mlp_P2 _ _ _ _ _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_P3 _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Ex_quan _ _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Prop_bott_left _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Prop_bott_right _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Prop_disj_left _ _ _ _ _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Prop_disj_right _ _ _ _ _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Prop_ex_left _ _ _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Prop_ex_right _ _ _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Pre_fixp _ _) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Existence) _ => _ ;
  weak_proof_to_proof' _ _ (@mlp_Singleton_ctx _ _ _ _ _) _ => _ ;
  weak_proof_to_proof' Γ ϕ (@mlp_Modus_ponens phi1 phi2 _ _ pf1 pf2) _
  with ((weak_proof_to_proof' Γ phi1 pf1 _),(weak_proof_to_proof' Γ (phi1 ---> phi2) pf2 _)) => {
  | (pf1',pf2') => _
  } ;
  weak_proof_to_proof' Γ ϕ (@mlp_Ex_gen phi1 phi2 x _ _ pf1 _) _
  with (weak_proof_to_proof' Γ (phi1 ---> phi2) pf1) => {
  | pf1' => _
  } ;
  weak_proof_to_proof' Γ ϕ (@mlp_Framing_left phi1 phi2 psi _ pf1) _
  with (weak_proof_to_proof' Γ (phi1 ---> phi2) pf1) => {
  | pf1' => _
  } ;
  weak_proof_to_proof' Γ ϕ (@mlp_Framing_right phi1 phi2 psi _ pf1) _
  with (weak_proof_to_proof' Γ (phi1 ---> phi2) pf1) => {
  | pf1' => _
  } ;
  weak_proof_to_proof' Γ ϕ (@mlp_Svar_subst phi psi X _ _ pf1) _
  with (weak_proof_to_proof' Γ phi pf1) => {
  | pf1' => _
  } ;
  weak_proof_to_proof' Γ ϕ (@mlp_Knaster_tarski phi psi _ pf1) _
  with (weak_proof_to_proof' Γ (instantiate (mu, phi) psi ---> psi) pf1) => {
  | pf1' => _
  }.
Proof.
  all: clear weak_proof_to_proof'; simp Proved_pattern.
  - eauto using P1 with nocore.
  - eauto using P2 with nocore.
  - eauto using P3 with nocore.
  - simp Proved_pattern in pateq.
    unfold Proved_pattern_clause_5 in pateq.
    case_match.
    2: { inversion pateq. }
    case_match.
    2: { inversion pateq. }
    inversion pateq; subst.
    exact e.
  - simp Proved_pattern in pateq.
    unfold Proved_pattern_clause_5 in pateq.
    case_match.
    2: { inversion pateq. }
    case_match.
    2: { inversion pateq. }
    inversion pateq; subst.
    exact e0.
  - eauto using Ex_quan with nocore.
  - eauto using Prop_bott_left with nocore.
  - eauto using Prop_bott_right with nocore.
  - eauto using Prop_disj_left with nocore.
  - eauto using Prop_disj_right with nocore.
  - eauto using Prop_ex_left with nocore.
  - eauto using Prop_ex_right with nocore.
  - eauto using Pre_fixp with nocore.
  - eauto using Existence with nocore.
  - eauto using Singleton_ctx with nocore.
Defined.
*)

(*


Lemma weak_proof_to_proof_old' {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_from_theory Γ)
      (pateq: Proved_pattern_old Γ pf = Some ϕ) : ML_proof_system Γ ϕ.
Proof.
  move: ϕ pateq.
  induction pf; intros ϕ pateq; inversion pateq; clear pateq; try subst; simp Proved_pattern.
  - apply hypothesis; assumption.
  - apply P1; assumption.
  - apply P2; assumption.
  - apply P3; assumption.
  -  case_match.
     2: { inversion H0. }
     case_match.
     2: { inversion H0. }
     inversion H0. subst.
     apply bool_decide_eq_true in Heqb.
     apply bool_decide_eq_true in Heqb0.
    eauto using Modus_ponens with nocore.
  - apply Ex_quan; assumption.
  - case_match.
    2: { inversion H0. }
    inversion H0. subst.
    eauto using Ex_gen with nocore.
  - apply Prop_bott_left; assumption.
  - apply Prop_bott_right; assumption.
  - apply Prop_disj_left; assumption.
  - apply Prop_disj_right; assumption.
  - apply Prop_ex_left; assumption.
  - apply Prop_ex_right; assumption.
  - case_match.
    2: { inversion H0. }
    inversion H0. subst.
    eauto using Framing_left with nocore.
  - case_match.
    2: { inversion H0. }
    inversion H0. subst.
    eauto using Framing_right with nocore.
  - case_match; inversion H0. subst.
    eauto using Svar_subst with nocore.
  - apply Pre_fixp; assumption.
  - case_match; inversion H0. subst.
    eauto using Knaster_tarski with nocore.
  - apply Existence.
  - apply Singleton_ctx; assumption.
Defined.
*)
Lemma weak_proof_to_proof' {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_from_theory Γ)
      (pateq: Proved_pattern' Γ pf = ϕ) (patwf : ML_proof_from_theory_wf Γ pf) : ML_proof_system Γ ϕ.
Proof.
  move: ϕ pateq.
  induction pf; intros ϕ pateq; inversion pateq; clear pateq; try subst; simpl in *.
  - apply hypothesis; assumption.
  - apply P1; assumption.
  - apply P2; assumption.
  - apply P3; assumption.
  - destruct_and!.
    eauto using Modus_ponens with nocore.
  - apply Ex_quan; assumption.
  - destruct_and!.
    eauto using Ex_gen with nocore.
  - apply Prop_bott_left; assumption.
  - apply Prop_bott_right; assumption.
  - apply Prop_disj_left; assumption.
  - apply Prop_disj_right; assumption.
  - apply Prop_ex_left; assumption.
  - apply Prop_ex_right; assumption.
  - destruct_and!.
    eauto using Framing_left with nocore.
  - destruct_and!.
    eauto using Framing_right with nocore.
  - destruct_and!.
    eauto using Svar_subst with nocore.
  - apply Pre_fixp; assumption.
  - destruct_and!.
    eauto using Knaster_tarski with nocore.
  - apply Existence.
  - apply Singleton_ctx; assumption.
Defined.


(*
Lemma weak_proof_to_proof' {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_from_theory Γ)
      (pateq: Proved_pattern Γ pf = Some ϕ) : ML_proof_system Γ ϕ.
Proof.
  move: ϕ pateq.
  induction pf; intros ϕ pateq; inversion pateq; clear pateq; try subst; simp Proved_pattern.
  - apply hypothesis; assumption.
  - apply P1; assumption.
  - apply P2; assumption.
  - apply P3; assumption.
  - simp Proved_pattern in H0. simpl in H0.
    case_match.
    2: { inversion H0. }
    case_match.
    2: { inversion H0. }
    inversion H0. subst.
    eauto using Modus_ponens with nocore.
  - apply Ex_quan; assumption.
  - simp Proved_pattern in H0. unfold Proved_pattern_clause_7 in H0.
    case_match.
    2: { inversion H0. }
    inversion H0. subst.
    eauto using Ex_gen with nocore.
  - apply Prop_bott_left; assumption.
  - apply Prop_bott_right; assumption.
  - apply Prop_disj_left; assumption.
  - apply Prop_disj_right; assumption.
  - apply Prop_ex_left; assumption.
  - apply Prop_ex_right; assumption.
  - simp Proved_pattern in H0. unfold Proved_pattern_clause_14 in H0.
    case_match.
    2: { inversion H0. }
    inversion H0. subst.
    eauto using Framing_left with nocore.
  - simp Proved_pattern in H0. unfold Proved_pattern_clause_15 in H0.
    case_match.
    2: { inversion H0. }
    inversion H0. subst.
    eauto using Framing_right with nocore.
  - simp Proved_pattern in H0. unfold Proved_pattern_clause_16 in H0.
    case_match; inversion H0. subst.
    eauto using Svar_subst with nocore.
  - apply Pre_fixp; assumption.
  - 
    simp Proved_pattern in H0. unfold Proved_pattern_clause_18 in H0.
    case_match; inversion H0. subst.
    eauto using Knaster_tarski with nocore.
  - apply Existence.
  - apply Singleton_ctx; assumption.
Defined.
*)
(*
Lemma weak_proof_to_proof {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern)
      (pf : {pf' : ML_proof_from_theory Γ & Proved_pattern Γ pf' = Some ϕ}) : ML_proof_system Γ ϕ.
Proof.
  destruct pf. eapply weak_proof_to_proof'; eassumption.
Defined.
*)
Lemma proof_to_weak_proof__data {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_system Γ ϕ)
      : ML_proof_from_theory Γ.
Proof.  
  induction pf.
  - apply (mlp_hypothesis Γ axiom i e).
  - apply ((mlp_P1 Γ phi psi i i0)).
  - apply ((mlp_P2 Γ phi psi xi ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  - apply ((mlp_P3 Γ phi ltac:(assumption))).
  - apply (mlp_Modus_ponens Γ phi1 phi2 ltac:(assumption) ltac:(assumption) IHpf1 IHpf2).
  - apply ((mlp_Ex_quan Γ phi y ltac:(assumption))).
  - apply ((mlp_Ex_gen Γ phi1 phi2 x ltac:(assumption) ltac:(assumption) IHpf ltac:(assumption))).
  - apply ((mlp_Prop_bott_left Γ phi ltac:(assumption))).
  - apply ((mlp_Prop_bott_right Γ phi ltac:(assumption))).
  - apply ((mlp_Prop_disj_left Γ phi1 phi2 psi ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  - apply ((mlp_Prop_disj_right Γ phi1 phi2 psi ltac:(assumption) ltac:(assumption) ltac:(assumption))).
  - apply ((mlp_Prop_ex_left Γ phi psi ltac:(assumption) ltac:(assumption))).
  - apply ((mlp_Prop_ex_right Γ phi psi ltac:(assumption) ltac:(assumption))).
  - apply ((mlp_Framing_left Γ phi1 phi2 psi ltac:(assumption) IHpf)).
  - apply ((mlp_Framing_right Γ phi1 phi2 psi ltac:(assumption) IHpf)).
  - apply ((mlp_Svar_subst Γ phi psi X ltac:(assumption) ltac:(assumption) IHpf)).
  - apply ((mlp_Pre_fixp Γ phi ltac:(assumption))).
  - apply ((mlp_Knaster_tarski Γ phi psi ltac:(assumption) IHpf)).
  - apply ((mlp_Existence Γ)).
  - apply ((mlp_Singleton_ctx Γ C1 C2 phi x ltac:(assumption))).
Defined.

Lemma proof_to_weak_proof__pattern {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_system Γ ϕ):
  Proved_pattern' Γ (proof_to_weak_proof__data Γ ϕ pf) = ϕ.
Proof.
  induction pf; simpl; auto.
Defined.

Lemma proof_to_weak_proof__wf {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_system Γ ϕ):
  ML_proof_from_theory_wf Γ (proof_to_weak_proof__data Γ ϕ pf).
Proof.
  induction pf; simpl; auto; split_and?; auto; auto using proof_to_weak_proof__pattern.
Defined.

#[global]
 Instance option_Pattern_eqdec {Σ : Syntax.Signature} : Classes.EqDec (option Pattern).
Proof.
  unfold EqDec. intros x' y'. apply option_eq_dec.
Defined.

#[global]
 Instance option_Pattern_uip {Σ : Syntax.Signature} : Classes.UIP (option Pattern).
Proof.
  unfold UIP. intros x' y' e e'. apply UIP_dec. intros x y. apply option_eq_dec.
Defined.

#[global]
 Instance Pattern_uip {Σ : Syntax.Signature} : Classes.UIP (Pattern).
Proof.
  unfold UIP. intros x' y' e e'. apply UIP_dec. intros x y. apply Pattern_eqdec.
Defined.

Global Set Transparent Obligations.
Equations Derive NoConfusion for Pattern.

Set Equations With UIP.



Check weak_proof_to_proof'.

Lemma proof_to_weak_proof_to_proof {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern)
      (pf : ML_proof_system Γ ϕ):
  weak_proof_to_proof' Γ ϕ
                       (proof_to_weak_proof__data Γ ϕ pf)
                       (proof_to_weak_proof__pattern Γ ϕ pf)
                       (proof_to_weak_proof__wf Γ ϕ pf)
  = pf.
Proof.
  induction pf; simpl.
  - unfold eq_rec_r,eq_rec,eq_rect.
    replace (eq_sym erefl) with (@erefl _ axiom) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec).
    reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold eq_rec_r,eq_rec,eq_rect.
    replace (eq_sym erefl) with (@erefl _ phi2) by (apply UIP_dec; intros x' y'; apply Pattern_eqdec).
    rewrite IHpf1. rewrite IHpf2.
    reflexivity.
  - reflexivity.
  - rewrite IHpf.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHpf.
    reflexivity.
  - rewrite IHpf.
    reflexivity.
  - rewrite IHpf.
    reflexivity.
  - reflexivity.
  - rewrite IHpf.
    reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Lemma weak_proof_to_proof_to_weak_proof {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern)
      (pf : ML_proof_from_theory Γ) (pat : Proved_pattern' Γ pf = ϕ) (wf : ML_proof_from_theory_wf Γ pf):
  proof_to_weak_proof__data Γ ϕ (weak_proof_to_proof' Γ ϕ pf pat wf)
  = pf.
Proof.
  move: ϕ pat.
  induction pf; intros ϕ pat; simpl in *; repeat case_match; destruct_and?; simpl in *; auto.
  - rewrite IHpf1. rewrite IHpf2. reflexivity.
  - rewrite IHpf. reflexivity.
  - rewrite IHpf. reflexivity.
  - rewrite IHpf. reflexivity.
  - rewrite IHpf. reflexivity.
  - rewrite IHpf. reflexivity.
Defined.

Lemma proof_to_weak_proof {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_system Γ ϕ)
  : {pf' : ML_proof_from_theory Γ & Proved_pattern' Γ pf' = ϕ & ML_proof_from_theory_wf Γ pf' }.
Proof.
  eapply (existT2 _ _ (proof_to_weak_proof__data Γ ϕ pf)).
  { apply proof_to_weak_proof__pattern. }
  { apply proof_to_weak_proof__wf. }
Defined.

Lemma weak_proof_to_proof {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern)
      (pf : {pf' : ML_proof_from_theory Γ & Proved_pattern' Γ pf' = ϕ & ML_proof_from_theory_wf Γ pf' })
  : ML_proof_system Γ ϕ.
Proof.
  destruct pf.
  eapply weak_proof_to_proof'; eassumption.
Defined.

Instance proof_to_weak_proof__weak_proof_to_proof__cancel
         {Σ : Syntax.Signature} (Γ : Theory) (ϕ : Pattern)
  : Cancel eq (proof_to_weak_proof Γ ϕ) (weak_proof_to_proof Γ ϕ).
Proof.
  unfold Cancel.
  intros x. destruct x.
  simpl.
  unfold proof_to_weak_proof.
  apply eq_existT2_uncurried; simpl.
  unshelve(eexists).
  apply weak_proof_to_proof_to_weak_proof.
  - unfold eq_rect.
    apply UIP_dec. intros x0 y0. apply Pattern_eqdec.
  - unfold eq_rect. apply proof_irrelevance.
Defined.
