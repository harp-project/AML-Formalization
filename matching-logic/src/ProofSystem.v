From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

From Coq Require Import Logic.Classical_Prop Logic.Eqdep_dec Btauto.
From MatchingLogic.Utils Require Import stdpp_ext Lattice.
From MatchingLogic Require Import Syntax NamedAxioms DerivedOperators_Syntax wftactics.
From stdpp Require Import base fin_sets sets propset gmap.

From MatchingLogic.Utils Require Import extralibrary.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Substitution.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.

Set Default Proof Mode "Classic".

Section ml_proof_system.
  Open Scope ml_scope.

  Context {Σ : Signature}.

  (* Proof system for AML ref. snapshot: Section 3 *)

  Reserved Notation "theory ⊢H pattern" (at level 76).
  Inductive ML_proof_system (theory : Theory) :
    Pattern -> Set :=

  (* Hypothesis *)
  | hypothesis (axiom : Pattern) :
      well_formed axiom ->
      (axiom ∈ theory) -> theory ⊢H axiom

  (* FOL reasoning *)
  (* Propositional tautology *)
  | P1 (phi psi : Pattern) :
      well_formed phi -> well_formed psi ->
      theory ⊢H (phi ---> (psi ---> phi))
  | P2 (phi psi xi : Pattern) :
      well_formed phi -> well_formed psi -> well_formed xi ->
      theory ⊢H ((phi ---> (psi ---> xi)) ---> ((phi ---> psi) ---> (phi ---> xi)))
  | P3 (phi : Pattern) :
      well_formed phi ->
      theory ⊢H (((phi ---> Bot) ---> Bot) ---> phi)

  (* Modus ponens *)
  | Modus_ponens (phi1 phi2 : Pattern) :
      theory ⊢H phi1 ->
      theory ⊢H (phi1 ---> phi2) ->
      theory ⊢H phi2

  (* Existential quantifier *)
  | Ex_quan (phi : Pattern) (y : evar) :
      well_formed (patt_exists phi) ->
      theory ⊢H (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi))

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Pattern) (x : evar) :
      well_formed phi1 -> well_formed phi2 ->
      theory ⊢H (phi1 ---> phi2) ->
      x ∉ (free_evars phi2) ->
      theory ⊢H (exists_quantify x phi1 ---> phi2)

  (* Frame reasoning *)
  (* Propagation bottom *)
  | Prop_bott_left (phi : Pattern) :
      well_formed phi ->
      theory ⊢H (patt_bott $ phi ---> patt_bott)

  | Prop_bott_right (phi : Pattern) :
      well_formed phi ->
      theory ⊢H (phi $ patt_bott ---> patt_bott)

  (* Propagation disjunction *)
  | Prop_disj_left (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->
      theory ⊢H (((phi1 or phi2) $ psi) ---> ((phi1 $ psi) or (phi2 $ psi)))

  | Prop_disj_right (phi1 phi2 psi : Pattern) :
      well_formed phi1 -> well_formed phi2 -> well_formed psi ->
      theory ⊢H ((psi $ (phi1 or phi2)) ---> ((psi $ phi1) or (psi $ phi2)))

  (* Propagation exist *)
  | Prop_ex_left (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢H (((ex , phi) $ psi) ---> (ex , phi $ psi))

  | Prop_ex_right (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢H ((psi $ (ex , phi)) ---> (ex , psi $ phi))

  (* Framing *)
  | Framing_left (phi1 phi2 psi : Pattern) :
      well_formed psi ->
      theory ⊢H (phi1 ---> phi2) ->
      theory ⊢H ((phi1 $ psi) ---> (phi2 $ psi))

  | Framing_right (phi1 phi2 psi : Pattern) :
      well_formed psi ->
      theory ⊢H (phi1 ---> phi2) ->
      theory ⊢H ((psi $ phi1) ---> (psi $ phi2))

  (* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | Svar_subst (phi psi : Pattern) (X : svar) :
      well_formed phi -> well_formed psi ->
      theory ⊢H phi -> theory ⊢H (phi^[[svar: X ↦ psi]])

  (* Pre-Fixpoint *)
  | Pre_fixp (phi : Pattern) :
      well_formed (patt_mu phi) ->
      theory ⊢H (instantiate (patt_mu phi) (patt_mu phi) ---> (patt_mu phi))

  (* Knaster-Tarski *)
  | Knaster_tarski (phi psi : Pattern) :
      well_formed (patt_mu phi) ->
      theory ⊢H ((instantiate (patt_mu phi) psi) ---> psi) ->
      theory ⊢H ((@patt_mu Σ phi) ---> psi)

  (* Technical rules *)
  (* Existence *)
  | Existence : theory ⊢H (ex , patt_bound_evar 0)

  (* Singleton *)
  | Singleton_ctx (C1 C2 : Application_context) (phi : Pattern) (x : evar) :
      well_formed phi ->
      theory ⊢H (! ((subst_ctx C1 (patt_free_evar x and phi)) and
                   (subst_ctx C2 (patt_free_evar x and (! phi)))))

  where "theory ⊢H pattern" := (ML_proof_system theory pattern).

  Instance ML_proof_system_eqdec: forall gamma phi, EqDecision (ML_proof_system gamma phi).
  Proof. intros. intros x y. 
         unfold Decision. Fail decide equality.
  Abort.

  Lemma proved_impl_wf Γ ϕ:
    Γ ⊢H ϕ -> well_formed ϕ.
  Proof.
    intros pf.
    induction pf; wf_auto2. Set Printing All.
  Qed.

  Lemma cast_proof {Γ} {ϕ} {ψ} (e : ψ = ϕ) : ML_proof_system Γ ϕ -> ML_proof_system Γ ψ.
  Proof. intros H. rewrite <- e in H. exact H. Defined.

  Theorem extend_theory (Γ Γ' : Theory) φ :
    Γ ⊆ Γ' ->
    Γ ⊢H φ ->
    Γ' ⊢H φ.
  Proof.
    intros H IH. revert Γ' H. induction IH; intros; try now constructor.
    * constructor. assumption. set_solver.
    * eapply Modus_ponens; [apply IHIH1; assumption | apply IHIH2; assumption].
    * apply Ex_gen; try assumption. now apply IHIH.
    * apply Framing_left. assumption. now apply IHIH.
    * apply Framing_right. assumption. now apply IHIH.
    * apply Svar_subst; try assumption. now apply IHIH.
    * apply Knaster_tarski; try assumption. now apply IHIH.
  Defined.

End ml_proof_system.

Module Notations_private.

  Notation "theory ⊢H pattern" := (ML_proof_system theory pattern) (at level 95, no associativity).

End Notations_private.
