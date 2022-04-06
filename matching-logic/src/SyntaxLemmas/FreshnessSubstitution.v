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



  (* TODO make a wrapper that does not have the 'sz' variable *)
  Lemma bevar_subst_fresh_notin: 
    forall sz phi psi v,
      le (size phi) sz ->
      v ∉ (free_evars phi) ->
      v ∉ (free_evars psi) ->
      forall n,
        v ∉ (free_evars (bevar_subst phi psi n)).
  Proof.
    induction sz; destruct phi; intros psi v Hsz Hlsv Hneq n0; simpl in *; try inversion Hsz; auto.
    - case_match; set_solver.
    - case_match; set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (S n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (S n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0).
  Qed.

  Lemma bsvar_subst_fresh_notin: 
    forall sz phi psi v,
      le (size phi) sz ->
      v ∉ (free_svars phi) ->
      v ∉ (free_svars psi) ->
      forall n,
        v ∉ (free_svars (bsvar_subst phi psi n)).
  Proof.
    induction sz; destruct phi; intros psi v Hsz Hlsv Hneq n0; simpl in *; try inversion Hsz; auto.
    - case_match; set_solver.
    - case_match; set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - specialize (IHsz phi1 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH1.
      specialize (IHsz phi2 psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) n0) as IH2.
      set_solver.
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (S n0)).
    - now specialize (IHsz phi psi v ltac:(lia) ltac:(set_solver) ltac:(set_solver) (S n0)).
  Qed.

  Corollary evar_open_fresh_notin: 
    forall phi v w,
      v ∉ (free_evars phi) ->
      w ∉ (free_evars phi) ->
      (v <> w) ->
      forall n,
        v ∉ (free_evars (evar_open n w phi)).
  Proof.
    intros phi v w N1 N2 NEQ n. eapply bevar_subst_fresh_notin.
    reflexivity.
    auto.
    set_solver.
  Qed.

  Corollary svar_open_fresh_notin: 
    forall phi v w,
      v ∉ (free_svars phi) ->
      w ∉ (free_svars phi) ->
      (v <> w) ->
      forall n,
        v ∉ (free_svars (svar_open n w phi)).
  Proof.
    intros phi v w N1 N2 NEQ n.
    unfold svar_open. eapply bsvar_subst_fresh_notin.
    reflexivity.
    auto.
    set_solver.
  Qed.



  Lemma free_evars_svar_open : forall (psi : Pattern) (dbi :db_index) (X : svar),
      free_evars (svar_open dbi X psi) = free_evars psi.
  Proof.
    unfold svar_open.
    induction psi; intros dbi X; simpl; try reflexivity.
    * case_match; reflexivity.
    * rewrite -> IHpsi1. rewrite -> IHpsi2. reflexivity.
    * rewrite -> IHpsi1. rewrite -> IHpsi2. reflexivity.
    * rewrite -> IHpsi. reflexivity.
    * rewrite -> IHpsi. reflexivity.
  Qed.


End lemmas.