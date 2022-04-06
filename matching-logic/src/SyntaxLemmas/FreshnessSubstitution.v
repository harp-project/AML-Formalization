From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base tactics sets.

From MatchingLogic.Utils
Require Import
    extralibrary
.

From MatchingLogic
Require Import
    Signature
    Pattern
    Substitution
    Freshness
.

Import Substitution.Notations.

Section lemmas.
    Context {Σ : Signature}.

Lemma evar_is_fresh_in_free_evar_subst x phi psi:
evar_is_fresh_in x psi ->
evar_is_fresh_in x (phi.[[evar: x ↦ psi]]).
Proof.
move: x psi. induction phi; intros y psi H; unfold evar_is_fresh_in; simpl; try set_solver.
case_match; auto. set_solver.
Qed.

Lemma evar_is_fresh_in_evar_quantify x n phi:
evar_is_fresh_in x (evar_quantify x n phi).
Proof.
move: x n. induction phi; intros y m; unfold evar_is_fresh_in; simpl; try set_solver.
case_match; auto; set_solver.
Qed.

Lemma svar_is_fresh_in_free_evar_subst X phi psi:
svar_is_fresh_in X psi ->
svar_is_fresh_in X (phi.[[svar: X ↦ psi]]).
Proof.
move: X psi. induction phi; intros y psi H; unfold svar_is_fresh_in; simpl; try set_solver.
case_match; auto. set_solver.
Qed.

Lemma svar_is_fresh_in_svar_quantify X n phi:
svar_is_fresh_in X (svar_quantify X n phi).
Proof.
move: X n. induction phi; intros Y m; unfold svar_is_fresh_in; simpl; try set_solver.
case_match; auto; set_solver.
Qed.

(*If phi is a closed body, then (ex, phi) is closed too*)
Corollary wfc_body_to_wfc_ex phi:
wfc_body_ex phi ->
well_formed_closed (patt_exists phi) = true.
Proof.
intros WFE. unfold wfc_body_ex in WFE. unfold well_formed_closed. simpl.
unfold well_formed_closed in WFE.
pose proof (Htmp := WFE (fresh_evar phi) ltac:(apply set_evar_fresh_is_fresh)).
destruct_and!.
split_and.
2: { rewrite -> wfc_ex_aux_body_iff. eassumption. }
eapply wfc_mu_aux_body_ex_imp2. eassumption.
Qed.

(* Lemmas about wfc_ex and wfc_mu *)

(* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.4 (lc_abs_iff_body) *)
(*Conclusion*)
Corollary wfc_body_wfc_ex_iff: 
forall phi,
  well_formed_closed (patt_exists phi) = true <-> wfc_body_ex phi.
Proof.
split.
- apply wfc_ex_to_wfc_body.
- apply wfc_body_to_wfc_ex.
Qed.

End lemmas.