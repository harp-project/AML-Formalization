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



  Lemma fresh_evar_svar_open dbi X phi :
    fresh_evar (svar_open dbi X phi) = fresh_evar phi.
  Proof.
    unfold fresh_evar.
    apply f_equal.
    apply f_equal.
    apply free_evars_svar_open.
  Qed.

  Lemma fresh_svar_evar_open dbi x phi :
    fresh_svar (evar_open dbi x phi) = fresh_svar phi.
  Proof.
    unfold fresh_svar.
    apply f_equal.
    apply f_equal.
    apply free_svars_evar_open.
  Qed.

  Corollary svar_is_fresh_in_svar_open X Y dbi ϕ:
  X <> Y ->
  svar_is_fresh_in X ϕ ->
  svar_is_fresh_in X (svar_open dbi Y ϕ).
Proof.
  unfold svar_is_fresh_in.
  move=> Hneq Hfr.
  pose proof (H := @free_svars_svar_open Σ ϕ Y dbi).
  intros Contra.
  rewrite -> elem_of_subseteq in H.
  specialize (H X Contra). clear Contra.
  apply elem_of_union in H.
  destruct H.
  - apply elem_of_singleton_1 in H.
    contradiction.
  - contradiction.
Qed.

Corollary evar_is_fresh_in_evar_open x y dbi ϕ:
  x <> y ->
  evar_is_fresh_in x ϕ ->
  evar_is_fresh_in x (evar_open dbi y ϕ).
Proof.
  unfold evar_is_fresh_in.
  move=> Hneq Hfr.
  pose proof (H := @free_evars_evar_open Σ ϕ y dbi).
  intros Contra.
  rewrite -> elem_of_subseteq in H.
  specialize (H x Contra). clear Contra.
  apply elem_of_union in H.
  destruct H.
  - apply elem_of_singleton_1 in H.
    contradiction.
  - contradiction.
Qed.


Corollary evar_fresh_svar_open x X dbi ϕ:
evar_is_fresh_in x ϕ ->
evar_is_fresh_in x (svar_open dbi X ϕ).
Proof.
unfold evar_is_fresh_in.
  by rewrite free_evars_svar_open.
Qed.

Corollary svar_fresh_evar_open x X dbi ϕ:
svar_is_fresh_in X ϕ ->
svar_is_fresh_in X (evar_open dbi x ϕ).
Proof.
unfold svar_is_fresh_in.
  by rewrite free_svars_evar_open.
Qed.


Lemma evar_open_inj : ∀ phi psi x n,
evar_is_fresh_in x phi → evar_is_fresh_in x psi →
evar_open n x phi =
evar_open n x psi
→ phi = psi.
Proof.
induction phi; destruct psi;
intros x' n' H H0 H1;
try (cbn in H1; congruence);
try (cbn in H1; case_match; congruence); auto.
- cbn in H1. case_match; try congruence.
inversion H1. subst. unfold evar_is_fresh_in in H. simpl in H. apply not_elem_of_singleton_1 in H.
contradiction.
- cbn in H1. case_match; try congruence.
inversion H1. subst. unfold evar_is_fresh_in in H0. simpl in H0. apply not_elem_of_singleton_1 in H0.
contradiction.
- cbn in H1.
repeat case_match; auto; try congruence.
1-3: inversion H1; subst; try lia. assert (n = n0) by lia. auto.
- inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
apply evar_is_fresh_in_app_r in H. assumption.
apply evar_is_fresh_in_app_r in H0. assumption.
apply evar_is_fresh_in_app_l in H. assumption.
apply evar_is_fresh_in_app_l in H0. assumption.
- inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
apply evar_is_fresh_in_imp_r in H. assumption.
apply evar_is_fresh_in_imp_r in H0. assumption.
apply evar_is_fresh_in_imp_l in H. assumption.
apply evar_is_fresh_in_imp_l in H0. assumption.
- inversion H1. apply IHphi in H3. subst. reflexivity.
apply evar_is_fresh_in_exists in H. assumption.
apply evar_is_fresh_in_exists in H0. assumption.
- inversion H1. apply IHphi in H3. subst. reflexivity.
apply evar_is_fresh_in_mu in H. assumption.
apply evar_is_fresh_in_mu in H0. assumption.
Qed.

Lemma svar_open_inj : ∀ phi psi X n,
svar_is_fresh_in X phi → svar_is_fresh_in X psi →
svar_open n X phi =
svar_open n X psi
→ phi = psi.
Proof.
induction phi; destruct psi;
intros X' n' H H0 H1;
try (cbn in H1; congruence);
try (cbn in H1; case_match; congruence); auto.
- cbn in H1. case_match; try congruence.
inversion H1. subst. unfold svar_is_fresh_in in H. simpl in H. set_solver.
- cbn in H1. case_match; try congruence.
inversion H1. subst. unfold svar_is_fresh_in in H0. simpl in H0. set_solver.
- cbn in H1. repeat case_match; auto; try congruence.
1-3: inversion H1; subst; try lia. assert (n = n0) by lia. auto.
- inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
apply svar_is_fresh_in_app_r in H. assumption.
apply svar_is_fresh_in_app_r in H0. assumption.
apply svar_is_fresh_in_app_l in H. assumption.
apply svar_is_fresh_in_app_l in H0. assumption.
- inversion H1. apply IHphi1 in H3. apply IHphi2 in H4. subst. reflexivity.
apply svar_is_fresh_in_imp_r in H. assumption.
apply svar_is_fresh_in_imp_r in H0. assumption.
apply svar_is_fresh_in_imp_l in H. assumption.
apply svar_is_fresh_in_imp_l in H0. assumption.
- inversion H1. apply IHphi in H3. subst. reflexivity.
apply svar_is_fresh_in_exists in H. assumption.
apply svar_is_fresh_in_exists in H0. assumption.
- inversion H1. apply IHphi in H3. subst. reflexivity.
apply svar_is_fresh_in_mu in H. assumption.
apply svar_is_fresh_in_mu in H0. assumption.
Qed.



Lemma Private_evar_open_free_svar_subst_comm: ∀ sz phi psi fresh n X,
((size phi) <= sz) → (well_formed_closed_ex_aux psi 0) → evar_is_fresh_in fresh phi →
evar_is_fresh_in fresh (free_svar_subst phi psi X)
→
(evar_open n fresh (free_svar_subst phi psi X)) = (free_svar_subst (evar_open n fresh phi) psi X).
Proof.
induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf Hfresh1 Hfresh2; try inversion Hsz; auto.
- simpl. case_match.
+ rewrite -> evar_open_closed. reflexivity.
  assumption.
+ simpl. reflexivity.
- cbn. case_match; done.
- simpl. unfold evar_open in *. rewrite -> bevar_subst_app, -> (IHsz phi1), -> (IHsz phi2); try lia; try assumption. reflexivity.
apply (evar_is_fresh_in_app_r Hfresh1). simpl in Hfresh2.
apply (evar_is_fresh_in_app_r Hfresh2). apply (evar_is_fresh_in_app_l Hfresh1).
apply (evar_is_fresh_in_app_l Hfresh2).
reflexivity.
- simpl. unfold evar_open in *. rewrite -> bevar_subst_imp, -> (IHsz phi1), -> (IHsz phi2); try lia; try assumption. reflexivity.
apply (evar_is_fresh_in_imp_r Hfresh1). simpl in Hfresh2.
apply (evar_is_fresh_in_imp_r Hfresh2). apply (evar_is_fresh_in_app_l Hfresh1).
apply (evar_is_fresh_in_imp_l Hfresh2).
reflexivity.
- simpl. unfold evar_open in *. rewrite -> bevar_subst_exists, -> IHsz. reflexivity. lia. assumption.
apply evar_is_fresh_in_exists in Hfresh1. assumption.
simpl in Hfresh2. apply evar_is_fresh_in_exists in Hfresh1. assumption.
reflexivity.
- simpl. unfold evar_open in *. rewrite -> bevar_subst_mu.
f_equal.
rewrite -> IHsz; auto. lia.
reflexivity.
Qed.

Corollary evar_open_free_svar_subst_comm: ∀ phi psi fresh n X,
(well_formed_closed_ex_aux psi 0) → evar_is_fresh_in fresh phi →
evar_is_fresh_in fresh (free_svar_subst phi psi X)
→
(evar_open n fresh (free_svar_subst phi psi X)) = (free_svar_subst (evar_open n fresh phi) psi X).
Proof.
intros phi psi fresh n X H H0 H1. apply Private_evar_open_free_svar_subst_comm with (sz := (size phi)); try lia; try assumption.
Qed.

Lemma Private_svar_open_free_svar_subst_comm : ∀ sz phi psi fresh n X,
((size phi) <= sz) → (well_formed_closed_mu_aux psi 0) →  
svar_is_fresh_in fresh phi → svar_is_fresh_in fresh (free_svar_subst phi psi X) → (fresh ≠ X) 
→
(svar_open n fresh (free_svar_subst phi psi X)) = 
(free_svar_subst (svar_open n fresh phi) psi X).
Proof.
unfold free_svar_subst.
induction sz; destruct phi; intros psi fresh n0 X Hsz Hwf (* Hwfc *) Hfresh1 Hfresh2 Hneq; auto.
- simpl. case_match; auto.
rewrite -> svar_open_closed; auto.
- cbn. case_match; auto. simpl.
+ case_match.
  * congruence.
  * reflexivity.
- inversion Hsz.
- inversion Hsz.
- inversion Hsz.
- inversion Hsz.
- simpl. case_match; auto.
rewrite -> svar_open_closed; auto.
- cbn. case_match; auto. simpl.
+ case_match.
  * congruence.
  * reflexivity.
- simpl.
unfold svar_open in *. rewrite -> bsvar_subst_app, -> (IHsz phi1), -> (IHsz phi2); try lia; try assumption; try lia; try assumption.
reflexivity.
simpl in Hsz. lia.
simpl in Hfresh1. apply svar_is_fresh_in_app_r in Hfresh1. assumption.
simpl in Hfresh2. apply svar_is_fresh_in_app_r in Hfresh2. assumption.
simpl in Hsz. lia.
simpl in Hfresh1. apply svar_is_fresh_in_app_l in Hfresh1. assumption.
simpl in Hfresh2. apply svar_is_fresh_in_app_l in Hfresh2. assumption.
reflexivity.
- simpl.
unfold svar_open in *. rewrite -> bsvar_subst_imp, -> (IHsz phi1), -> (IHsz phi2); try lia; try assumption; try lia; try assumption.
reflexivity.
simpl in Hsz. lia.
simpl in Hfresh1. apply svar_is_fresh_in_app_r in Hfresh1. assumption.
simpl in Hfresh2. apply svar_is_fresh_in_app_r in Hfresh2. assumption.
simpl in Hsz. lia.
simpl in Hfresh1. apply svar_is_fresh_in_app_l in Hfresh1. assumption.
simpl in Hfresh2. apply svar_is_fresh_in_app_l in Hfresh2. assumption.
reflexivity.
- remember ((free_evars (svar_open n0 fresh (free_svar_subst phi psi X))) ∪
                                                                        (free_evars (free_svar_subst (svar_open n0 fresh phi) psi X))) as B.
simpl. unfold svar_open in *. rewrite -> bsvar_subst_exists by reflexivity. remember (@evar_fresh Σ (elements B)) as x.
assert(x ∉ B).
{
  subst. apply set_evar_fresh_is_fresh'.
}
subst B.  apply not_elem_of_union in H. destruct H.

fold free_svar_subst. (* this is needed *)
fold (svar_open n0 fresh (free_svar_subst phi psi X)). (* only this is not sufficient *)
erewrite (@evar_open_inj (svar_open n0 fresh (free_svar_subst phi psi X)) (free_svar_subst (svar_open n0 fresh phi) psi X) x 0 _ _ ).
reflexivity.
(*x needs to be fresh in ...*)
unfold svar_open in *.
rewrite -> IHsz. reflexivity. simpl in Hsz. lia. assumption. simpl in Hfresh2. apply svar_is_fresh_in_exists in Hfresh1. assumption.
apply svar_is_fresh_in_exists in Hfresh2. assumption. assumption.
- remember ((free_svars (svar_open (S n0) fresh (free_svar_subst phi psi X)) ∪
                      (free_svars (free_svar_subst (svar_open (S n0) fresh phi) psi X)))) as B.
simpl. remember (@svar_fresh Σ (elements B)) as X'.
assert(X' ∉ B).
{
  subst. apply set_svar_fresh_is_fresh'.
}
subst B.  apply not_elem_of_union in H. destruct H.
simpl. unfold svar_open in *. rewrite bsvar_subst_mu.

f_equal.
fold free_svar_subst.
fold (svar_open (S n0) fresh (free_svar_subst phi psi X)).
erewrite (@svar_open_inj (svar_open (S n0) fresh (free_svar_subst phi psi X)) (free_svar_subst (svar_open (S n0) fresh phi) psi X) X' 0 _ _ ).
{ reflexivity. }
(*x needs to be fresh in ...*)
unfold svar_open in *.
rewrite -> IHsz. reflexivity. simpl in Hsz. lia. assumption. simpl in Hfresh2. assumption.
simpl in Hfresh2.
apply -> svar_is_fresh_in_mu in Hfresh2. 2: auto.
fold free_svar_subst in *. auto.
Unshelve. all: assumption.
Qed.

Corollary svar_open_free_svar_subst_comm : ∀ phi psi fresh n X,
(well_formed_closed_mu_aux psi 0) →  
svar_is_fresh_in fresh phi → svar_is_fresh_in fresh (free_svar_subst phi psi X) → (fresh ≠ X) 
→
(svar_open n fresh (free_svar_subst phi psi X)) = 
(free_svar_subst (svar_open n fresh phi) psi X).
Proof.
intros phi psi fresh n X H H0 H1 H2. apply (Private_svar_open_free_svar_subst_comm) with (sz := (size phi)); try lia; try assumption.
Qed.



Lemma free_evar_subst_preserves_no_negative_occurrence x p q n:
well_formed_closed_mu_aux q 0 ->
no_negative_occurrence_db_b n p ->
no_negative_occurrence_db_b n (free_evar_subst p q x)
with
free_evar_subst_preserves_no_positive_occurrence x p q n:
well_formed_closed_mu_aux q 0 ->
no_positive_occurrence_db_b n p ->
no_positive_occurrence_db_b n (free_evar_subst p q x)
.
Proof.
- intros wfq nno.
  unfold free_evar_subst.
  induction p; cbn; auto.
  + destruct (decide (x = x0)); simpl; auto.
    apply wfc_impl_no_neg_occ; auto.
  + simpl in nno. apply andb_prop in nno. destruct nno as [nnop1 nnop2].
    rewrite IHp1. auto. rewrite IHp2. auto. reflexivity.
  + simpl in nno. apply andb_prop in nno. destruct nno as [nnop1 nnop2].
    rewrite IHp2. assumption.
    fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
    rewrite free_evar_subst_preserves_no_positive_occurrence; auto. 
- intros wfq npo.
  induction p; cbn; auto.
  + destruct (decide (x = x0)); simpl; auto.
    apply wfc_impl_no_pos_occ; auto.
  + simpl in npo. apply andb_prop in npo. destruct npo as [npop1 npop2].
    rewrite IHp1. auto. rewrite IHp2. auto. reflexivity.
  + simpl in npo. apply andb_prop in npo. destruct npo as [npop1 npop2].
    rewrite IHp2. assumption.
    fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
    rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
Qed.



Lemma Private_well_formed_free_evar_subst x p q n1 n2:
well_formed q ->
well_formed_positive p && well_formed_closed_mu_aux p n2 && well_formed_closed_ex_aux p n1 ->
no_negative_occurrence_db_b n2 (free_evar_subst p q x)
&& no_positive_occurrence_db_b n2 (free_evar_subst p q x)
&& well_formed_positive (free_evar_subst p q x)
&& well_formed_closed_mu_aux (free_evar_subst p q x) n2
&& well_formed_closed_ex_aux (free_evar_subst p q x) n1
= true.
Proof.
intros wfq wfp.
move: n1 n2 wfp.
induction p; intros n1 n2 wfp; cbn; auto.
- destruct (decide (x = x0)); simpl; auto.
  unfold well_formed in wfq. apply andb_prop in wfq. destruct wfq as [wfpq wfcq].
  rewrite wfpq.
  (* rewrite wfp_nest_ex_aux.
  rewrite wfpq. simpl in *.*)
  unfold well_formed_closed in wfcq. destruct_and!.
  pose proof (H1' := @well_formed_closed_mu_aux_ind Σ q 0 n2 ltac:(lia) H).
  pose proof (H2' := wfc_impl_no_neg_pos_occ H1').
  destruct_and!.
  
  split_and!; auto.
  + eapply well_formed_closed_ex_aux_ind.
    2: eassumption. lia.
- cbn in *.
  destruct_and!. split_and!; auto.
  repeat case_match; lia.
- unfold well_formed, well_formed_closed in *. simpl in *.
  destruct_and!.
  specialize (IHp1 n1 n2). specialize (IHp2 n1 n2).
  feed specialize IHp1.
  { split_and!; auto. }
  feed specialize IHp2.
  { split_and!; auto. }
  destruct_and!.
  cbn.
  split_and!; auto.
- unfold well_formed, well_formed_closed in *. simpl in *.
  destruct_and!.
  specialize (IHp1 n1 n2). specialize (IHp2 n1 n2).
  feed specialize IHp1.
  { split_and!; auto. }
  feed specialize IHp2.
  { split_and!; auto. }
  destruct_and!.
  cbn.
  split_and!; auto.
- unfold well_formed, well_formed_closed in *. simpl in *.
  destruct_and!.
  pose proof (IHp' := IHp).
  specialize (IHp n1 (S n2)).
  feed specialize IHp.
  { split_and!; auto. }
  destruct_and!.
  cbn in *.
  split_and!; auto.
  rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
Qed.

Lemma well_formed_free_evar_subst x p q:
well_formed q = true ->
well_formed p = true ->
well_formed (free_evar_subst p q x) = true.
Proof.
intros wfq wfp.
pose proof (H := @Private_well_formed_free_evar_subst x p q 0 0 wfq).
unfold well_formed,well_formed_closed in *.
destruct_and!.
feed specialize H.
{ split_and!; assumption. }
destruct_and!. split_and!; auto.
Qed.

Lemma well_formed_free_evar_subst_0 x p q:
well_formed q = true ->
well_formed p = true ->
well_formed (free_evar_subst p q x) = true.
Proof.
intros. apply well_formed_free_evar_subst; assumption.
Qed.


Lemma evar_quantify_fresh x n phi:
evar_is_fresh_in x phi ->
(evar_quantify x n phi) = phi.
Proof.
intros H.
move: n H.
induction phi; intros n' H; cbn; auto.
- destruct (decide (x = x0)); subst; simpl.
  + unfold evar_is_fresh_in in H. simpl in H. set_solver.
  + reflexivity.
- apply evar_is_fresh_in_app in H. destruct H as [H1 H2].
  rewrite IHphi1; auto.
  rewrite IHphi2; auto.
- apply evar_is_fresh_in_imp in H. destruct H as [H1 H2].
  rewrite IHphi1; auto.
  rewrite IHphi2; auto.
- apply evar_is_fresh_in_exists in H.
  rewrite IHphi; auto.
- apply evar_is_fresh_in_mu in H.
  rewrite IHphi; auto.
Qed.

Lemma svar_quantify_fresh X n phi:
svar_is_fresh_in X phi ->
(svar_quantify X n phi) = phi.
Proof.
intros H.
move: n H.
induction phi; intros n' H; cbn; auto.
- destruct (decide (X = x)); subst; simpl.
  + unfold svar_is_fresh_in in H. simpl in H. set_solver.
  + reflexivity.
- apply svar_is_fresh_in_app in H. destruct H as [H1 H2].
  rewrite IHphi1; auto.
  rewrite IHphi2; auto.
- apply svar_is_fresh_in_imp in H. destruct H as [H1 H2].
  rewrite IHphi1; auto.
  rewrite IHphi2; auto.
- apply svar_is_fresh_in_exists in H.
  rewrite IHphi; auto.
- apply svar_is_fresh_in_mu in H.
  rewrite IHphi; auto.
Qed.


End lemmas.


Lemma svar_hno_bsvar_subst {Σ : Signature} X ϕ ψ dbi:
  (svar_has_negative_occurrence X ψ = true -> no_positive_occurrence_db_b dbi ϕ = true) ->
  (svar_has_positive_occurrence X ψ = true -> no_negative_occurrence_db_b dbi ϕ = true) ->
  svar_has_negative_occurrence X ϕ = false ->
  svar_has_negative_occurrence X (bsvar_subst ϕ ψ dbi) = false
with svar_hpo_bsvar_subst {Σ : Signature} X ϕ ψ dbi:
       (svar_has_negative_occurrence X ψ = true -> no_negative_occurrence_db_b dbi ϕ = true) ->
       (svar_has_positive_occurrence X ψ = true -> no_positive_occurrence_db_b dbi ϕ = true) ->
       svar_has_positive_occurrence X ϕ = false ->
       svar_has_positive_occurrence X (bsvar_subst ϕ ψ dbi) = false.
Proof.
  -
    move: dbi.
    induction ϕ; intros dbi H1 H2 H3; cbn in *; auto.
    + case_match; auto. case_match; try lia.
      destruct (decide (svar_has_negative_occurrence X ψ = false)); auto.
      apply not_false_is_true in n0. specialize (H1 n0). congruence. case_match; auto. congruence.
    + apply orb_false_iff in H3.
      destruct_and!.
      rewrite IHϕ1; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
    + fold svar_has_positive_occurrence in *.
      fold no_positive_occurrence_db_b in *.
      fold no_negative_occurrence_db_b in *.
      apply orb_false_iff in H3.
      destruct_and!.
      rewrite svar_hpo_bsvar_subst; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
  -
    move: dbi.
    induction ϕ; intros dbi H1 H2 H3; cbn in *; auto.
    + case_match; auto. case_match; try lia.
      destruct (decide (svar_has_positive_occurrence X ψ = false)); auto.
      apply not_false_is_true in n0. specialize (H2 n0). congruence. case_match; auto. congruence.
    + apply orb_false_iff in H3.
      destruct_and!.
      rewrite IHϕ1; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
    + fold svar_has_positive_occurrence in *.
      fold svar_has_negative_occurrence in *.
      fold no_positive_occurrence_db_b in *.
      fold no_negative_occurrence_db_b in *.
      apply orb_false_iff in H3.
      destruct_and!.
      rewrite svar_hno_bsvar_subst; auto.
      { naive_bsolver. }
      { naive_bsolver. }
      rewrite IHϕ2; auto.
      { naive_bsolver. }
      { naive_bsolver. }
Qed.

Lemma svar_hno_false_if_fresh {Σ : Signature} X ϕ:
  svar_is_fresh_in X ϕ ->
  svar_has_negative_occurrence X ϕ = false
with svar_hpo_false_if_fresh {Σ : Signature} X ϕ:
       svar_is_fresh_in X ϕ ->
       svar_has_positive_occurrence X ϕ = false.
Proof.
  - unfold svar_is_fresh_in.
    induction ϕ; intros H; cbn in *; auto.
    + rewrite -> IHϕ1, -> IHϕ2; try reflexivity; set_solver.
    + fold svar_has_positive_occurrence.
      rewrite -> svar_hpo_false_if_fresh, -> IHϕ2; try reflexivity.
      * set_solver.
      * unfold svar_is_fresh_in. set_solver.
  - unfold svar_is_fresh_in.
    induction ϕ; intros H; cbn in *; auto.
    + case_match; auto. set_solver.
    + rewrite -> IHϕ1, -> IHϕ2; try reflexivity; set_solver.
    + fold svar_has_negative_occurrence.
      rewrite -> svar_hno_false_if_fresh, -> IHϕ2; try reflexivity.
      * set_solver.
      * unfold svar_is_fresh_in. set_solver.
Qed.


(* TODO remove the no-negative-ocurrence assumption from the svar version *)
Lemma wfp_free_evar_subst {Σ : Signature} ϕ ψ x:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  well_formed_positive (free_evar_subst ϕ ψ x) = true
with wfp_neg_free_evar_subst {Σ : Signature} ϕ ψ x:
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_positive ψ = true ->
  well_formed_positive ϕ = true ->
  well_formed_positive (free_evar_subst ϕ ψ x) = true.
Proof.
  -
    intros Hwfcψ Hwfpψ Hwfpϕ. (* Hnoneg.*)
    induction ϕ; simpl; auto.
    + case_match; [|reflexivity].
      assumption.
    + cbn in Hwfpϕ.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ.
      destruct_and!.
      pose proof (IH1 := wfp_neg_free_evar_subst Σ ϕ1 ψ x ltac:(assumption)).
      feed specialize IH1.
      { assumption. }
      { assumption. }
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ. destruct_and!.
      rewrite IHϕ. assumption. split_and!; auto.
      rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
  -
    intros Hwfcψ Hwfpψ Hwfpϕ.
    induction ϕ; simpl; auto.
    + case_match; [|reflexivity].
      assumption.
    + cbn in Hwfpϕ.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ.
      destruct_and!.
      pose proof (IH1 := wfp_free_evar_subst Σ ϕ1 ψ x ltac:(assumption)).
      feed specialize IH1.
      { assumption. }
      { assumption. }
      specialize (IHϕ2 ltac:(assumption)).
      split_and!; auto.
    + cbn in Hwfpϕ. destruct_and!.
      rewrite IHϕ. assumption. split_and!; auto.
      rewrite free_evar_subst_preserves_no_negative_occurrence; auto.
Qed.

#[export]
 Hint Resolve wfp_free_evar_subst : core.