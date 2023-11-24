From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base tactics sets.

Require Import MatchingLogic.Utils.extralibrary. (* compare_nat *)

From MatchingLogic Require Import
    Pattern.

Section subst.
    Context {Σ : Signature}.

     (* There are two substitution operations over patterns, [bevar_subst] and [bsvar_subst]. *)
  (* substitute bound variable x for psi in phi *)
  Fixpoint bevar_subst (psi : Pattern) (x : db_index) (phi : Pattern) :=
    match phi with
    | patt_free_evar x' => patt_free_evar x'
    | patt_free_svar x' => patt_free_svar x'
    | patt_bound_evar n => match compare_nat n x with
                           | Nat_less _ _ _ => patt_bound_evar n
                           | Nat_equal _ _ _ => psi
                           | Nat_greater _ _ _ => patt_bound_evar (Nat.pred n)
                           end
    | patt_bound_svar n => patt_bound_svar n
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (bevar_subst psi x phi1)
                                     (bevar_subst psi x phi2)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (bevar_subst psi x phi1) (bevar_subst psi x phi2)
    | patt_exists phi' => patt_exists (bevar_subst psi (S x) phi')
    | patt_mu phi' => patt_mu (bevar_subst psi x phi')
    end.

  Fixpoint bsvar_subst (psi : Pattern) (x : db_index) (phi : Pattern) :=
    match phi with
    | patt_free_evar x' => patt_free_evar x'
    | patt_free_svar x' => patt_free_svar x'
    | patt_bound_evar n => patt_bound_evar n
    | patt_bound_svar n => match compare_nat n x with
                           | Nat_less _ _ _ => patt_bound_svar n
                           | Nat_equal _ _ _ => psi
                           | Nat_greater _ _ _ => patt_bound_svar (Nat.pred n)
                           end
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (bsvar_subst psi x phi1)
                                     (bsvar_subst psi x phi2)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (bsvar_subst psi x phi1) (bsvar_subst psi x phi2)
    | patt_exists phi' => patt_exists (bsvar_subst psi x phi')
    | patt_mu phi' => patt_mu (bsvar_subst psi(S x) phi')
    end.


  Fixpoint bevar_occur (phi : Pattern) (x : db_index) : bool :=
    match phi with
    | patt_free_evar x' => false
    | patt_free_svar x' => false
    | patt_bound_evar n => if decide (n = x) is left _ then true else false
    | patt_bound_svar n => false
    | patt_sym sigma => false
    | patt_app phi1 phi2 => orb (bevar_occur phi1 x)
                                (bevar_occur phi2 x)
    | patt_bott => false
    | patt_imp phi1 phi2 => orb (bevar_occur phi1 x) (bevar_occur phi2 x)
    | patt_exists phi' => bevar_occur phi' (S x)
    | patt_mu phi' => bevar_occur phi' x
    end.

  Fixpoint bsvar_occur (phi : Pattern) (x : db_index) : bool :=
    match phi with
    | patt_free_evar x' => false
    | patt_free_svar x' => false
    | patt_bound_evar n => false
    | patt_bound_svar n => if (decide (n = x)) is left _ then true else false
    | patt_sym sigma => false
    | patt_app phi1 phi2 => orb (bsvar_occur phi1 x)
                                (bsvar_occur phi2 x)
    | patt_bott => false
    | patt_imp phi1 phi2 => orb (bsvar_occur phi1 x) (bsvar_occur phi2 x)
    | patt_exists phi' => bsvar_occur phi' x
    | patt_mu phi' => bsvar_occur phi' (S x)
    end.
  
  (* substitute free element variable x for psi in phi *)
  Fixpoint free_evar_subst (psi : Pattern) (x : evar) (phi : Pattern) :=
    match phi with
    | patt_free_evar x' => if decide (x = x') is left _ then psi else patt_free_evar x'
    | patt_free_svar X => patt_free_svar X
    | patt_bound_evar x' => patt_bound_evar x'
    | patt_bound_svar X => patt_bound_svar X
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (free_evar_subst psi x phi1)
                                     (free_evar_subst psi x phi2)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (free_evar_subst psi x phi1) (free_evar_subst psi x phi2)
    | patt_exists phi' => patt_exists (free_evar_subst psi x phi')
    | patt_mu phi' => patt_mu (free_evar_subst psi x phi')
    end.

  (* substitute free set variable X for psi in phi *)
  Fixpoint free_svar_subst (psi : Pattern) (X : svar) (phi : Pattern) : Pattern :=
    match phi with
    | patt_free_evar x => patt_free_evar x
    | patt_free_svar X' => if decide (X = X') is left _ then psi else patt_free_svar X'
    | patt_bound_evar x => patt_bound_evar x
    | patt_bound_svar X' => patt_bound_svar X'
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (free_svar_subst psi X phi1)
                                     (free_svar_subst psi X phi2)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (free_svar_subst psi X phi1) (free_svar_subst psi X phi2)
    | patt_exists phi' => patt_exists (free_svar_subst psi X phi')
    | patt_mu phi' => patt_mu (free_svar_subst psi X phi')
    end.


  (* instantiate exists x. p or mu x. p with psi for p *)
  Definition instantiate (phi psi : Pattern) :=
    match phi with
    | patt_exists phi' => bevar_subst psi 0 phi'
    | patt_mu phi' => bsvar_subst psi 0 phi'
    | _ => phi
    end.

      (* replace element variable x with de Bruijn index level *)
  Fixpoint evar_quantify (x : evar) (level : db_index)
           (p : Pattern) : Pattern :=
    match p with
    | patt_free_evar x' => if decide (x = x') is left _ then patt_bound_evar level else patt_free_evar x'
    | patt_free_svar x' => patt_free_svar x'
    | patt_bound_evar x' => patt_bound_evar x'
    | patt_bound_svar X => patt_bound_svar X
    | patt_sym s => patt_sym s
    | patt_app ls rs => patt_app (evar_quantify x level ls) (evar_quantify x level rs)
    | patt_bott => patt_bott
    | patt_imp ls rs => patt_imp (evar_quantify x level ls) (evar_quantify x level rs)
    | patt_exists p' => patt_exists (evar_quantify x (S level) p')
    | patt_mu p' => patt_mu (evar_quantify x level p')
    end.

  (* replace set variable X with de Bruijn index level *)
  Fixpoint svar_quantify (X : svar) (level : db_index)
           (p : Pattern) : Pattern :=
    match p with
    | patt_free_evar x' => patt_free_evar x'
    | patt_free_svar X' => if decide (X = X') is left _ then patt_bound_svar level else patt_free_svar X'
    | patt_bound_evar x' => patt_bound_evar x'
    | patt_bound_svar X => patt_bound_svar X
    | patt_sym s => patt_sym s
    | patt_app ls rs => patt_app (svar_quantify X level ls) (svar_quantify X level rs)
    | patt_bott => patt_bott
    | patt_imp ls rs => patt_imp (svar_quantify X level ls) (svar_quantify X level rs)
    | patt_exists p' => patt_exists (svar_quantify X level p')
    | patt_mu p' => patt_mu (svar_quantify X (S level) p')
    end.

      (* replace de Bruijn index k with element variable n *)
  Definition evar_open (x : evar) (k : db_index) (p : Pattern) : Pattern :=
    bevar_subst (patt_free_evar x) k p.


  (* replace de Bruijn index k with set variable n *)
  Definition svar_open (X : svar) (k : db_index) (p : Pattern) : Pattern :=
    bsvar_subst (patt_free_svar X) k p.
End subst.

Module Notations.

  Declare Scope ml_scope.
  Delimit Scope ml_scope with ml.
  Notation "e ^[ 'evar:' dbi ↦ e' ]" := (bevar_subst e' dbi e) (at level 2, e' at level 200, left associativity,
  format "e ^[ 'evar:' dbi ↦ e' ]" ) : ml_scope.
  Notation "e ^[ 'svar:' dbi ↦ e' ]" := (bsvar_subst e' dbi e) (at level 2, e' at level 200, left associativity,
  format "e ^[ 'svar:' dbi ↦ e' ]" ) : ml_scope.
  Notation "e ^[[ 'evar:' x ↦ e' ]]" := (free_evar_subst e' x e) (at level 2, e' at level 200, left associativity,
  format "e ^[[ 'evar:' x ↦ e' ]]" ) : ml_scope.
  Notation "e ^[[ 'svar:' X ↦ e' ]]" := (free_svar_subst e' X e) (at level 2, e' at level 200, left associativity,
  format "e ^[[ 'svar:' X ↦ e' ]]" ) : ml_scope.

  Notation "e ^{ 'evar:' db ↦ x }" := (evar_open x db e) (at level 2, x at level 200, left associativity,
  format "e ^{ 'evar:' db ↦ x }" ) : ml_scope.
  Notation "e ^{ 'svar:' db ↦ x }" := (svar_open x db e) (at level 2, x at level 200, left associativity,
  format "e ^{ 'svar:' db ↦ x }" ) : ml_scope.
  Notation "e ^{{ 'evar:' x ↦ db }}" := (evar_quantify x db e) (at level 2, x at level 200, left associativity,
  format "e ^{{ 'evar:' x ↦ db }}" ) : ml_scope.
  Notation "e ^{{ 'svar:' x ↦ db }}" := (svar_quantify x db e) (at level 2, x at level 200, left associativity,
  format "e ^{{ 'svar:' x ↦ db }}" ) : ml_scope.

  Notation "e ^ [ e' ]" := (instantiate e e') (at level 2, e' at level 200, left associativity) : ml_scope.

End Notations.

Section subst.
  Import Notations.
  Open Scope ml_scope.
  Context {Σ : Signature}.

  Definition exists_quantify (x : evar)
             (p : Pattern) : Pattern :=
    patt_exists (p^{{evar: x ↦ 0}}).

  Definition mu_quantify (X : svar)
             (p : Pattern) : Pattern :=
    patt_mu (p^{{svar: X ↦ 0}}).

  Lemma evar_open_size :
    forall (k : db_index) (n : evar) (p : Pattern),
      size p = size (p^{evar: k ↦ n}).
  Proof.
    intros k n p. generalize dependent k.
    induction p; intros k; cbn; try reflexivity.
    break_match_goal; reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp (S k)); reflexivity.
    rewrite (IHp k); reflexivity.
  Qed.

  Lemma svar_open_size :
    forall (k : db_index) (n : svar) (p : Pattern),
      size p = size (p^{svar: k ↦ n}).
  Proof.
    intros k n p. generalize dependent k.
    induction p; intros k; cbn; try reflexivity.
    break_match_goal; reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
    rewrite (IHp k); reflexivity.
    rewrite (IHp (S k)); reflexivity.
  Qed.


 
   (* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.3 (body def.) *)
   Definition wfc_body_ex phi  := forall x, 
   ~ elem_of x (free_evars phi) -> well_formed_closed (phi^{evar: 0 ↦ x}) = true.


   Lemma positive_negative_occurrence_evar_open_and : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
   (*le db1 db2 ->*)
   (no_positive_occurrence_db_b db1 phi -> no_positive_occurrence_db_b db1 (phi^{evar: db2 ↦ x}))
   /\ (no_negative_occurrence_db_b db1 phi -> no_negative_occurrence_db_b db1 (phi^{evar: db2 ↦ x})).
Proof.
 induction phi; intros db1 db2 x'; cbn; split; intro H; try lia; auto.
 * case_match; auto.
 * case_match; auto.
 * rewrite -> (proj1 (IHphi1 db1 db2 x')), -> (proj1 (IHphi2 db1 db2 x')); destruct_and!; auto.
 * rewrite -> (proj2 (IHphi1 db1 db2 x')), -> (proj2 (IHphi2 db1 db2 x')); destruct_and!; auto.
 * rewrite -> (proj2 (IHphi1 db1 db2 x')), -> (proj1 (IHphi2 db1 db2 x')); destruct_and!; auto.
 * rewrite -> (proj1 (IHphi1 db1 db2 x')), -> (proj2 (IHphi2 db1 db2 x')); destruct_and!; auto.
 * rewrite -> (proj1 (IHphi db1 (S db2) x')); auto.
 * rewrite -> (proj2 (IHphi db1 (S db2) x')); auto.
 * rewrite -> (proj1 (IHphi (S db1) db2 x')); auto.
 * rewrite -> (proj2 (IHphi (S db1) db2 x')); auto.
Qed.

Lemma no_negative_occurrence_evar_open phi db1 db2 x:
 no_negative_occurrence_db_b db1 phi = true ->
 no_negative_occurrence_db_b db1 (phi^{evar: db2 ↦ x}) = true.
Proof.
 apply positive_negative_occurrence_evar_open_and.
Qed.

Lemma no_positive_occurrence_evar_open phi db1 db2 x:
 no_positive_occurrence_db_b db1 phi = true ->
 no_positive_occurrence_db_b db1 (phi^{evar: db2 ↦ x}) = true.
Proof.
 apply positive_negative_occurrence_evar_open_and.
Qed.


(*Helper lemma for wf_body_to_wf_ex*)
Lemma wfc_ex_aux_body_ex_imp2:
 forall phi n x,
   well_formed_closed_ex_aux (phi^{evar: n ↦ x}) n = true
   ->
   well_formed_closed_ex_aux phi (S n) = true.
Proof using .
 induction phi; firstorder.
 - simpl. cbn in H. unfold well_formed_closed_ex_aux.
   repeat case_match; simpl; auto; try lia.
   unfold well_formed_closed_ex_aux in H. case_match; auto. lia.
 - simpl in H. simpl.
   apply andb_true_iff in H. destruct H as [H1 H2].
   erewrite IHphi1. 2: apply H1.
   erewrite IHphi2. 2: apply H2.
   reflexivity.
 - simpl in H. simpl.
   apply andb_true_iff in H. destruct H as [H1 H2].
   erewrite IHphi1. 2: apply H1.
   erewrite IHphi2. 2: apply H2.
   reflexivity.
Qed.

(*Helper lemma for wf_body_to_wf_ex*)
Lemma wfc_mu_aux_body_ex_imp2:
 forall phi n n' x,
   well_formed_closed_mu_aux (phi^{evar: n ↦ x}) n' = true
   ->
   well_formed_closed_mu_aux phi n' = true.
Proof using .
 induction phi; firstorder.
 - simpl in H. simpl.
   apply andb_true_iff in H. destruct H as [H1 H2].
   erewrite IHphi1. 2: apply H1.
   erewrite IHphi2. 2: apply H2.
   reflexivity.
 - simpl in H. simpl.
   apply andb_true_iff in H. destruct H as [H1 H2].
   erewrite IHphi1. 2: apply H1.
   erewrite IHphi2. 2: apply H2.
   reflexivity.
Qed.

Lemma wfc_ex_aux_body_mu_imp2:
 forall phi n n' X,
   well_formed_closed_ex_aux (phi^{svar: n ↦ X}) n' = true
   ->
   well_formed_closed_ex_aux phi n' = true.
Proof using .
 induction phi; firstorder.
 - simpl in H. simpl.
   destruct_and!.
   erewrite IHphi1. 2: eassumption.
   erewrite IHphi2. 2: eassumption.
   reflexivity.
 - simpl in H. simpl.
   destruct_and!.
   erewrite IHphi1. 2: eassumption.
   erewrite IHphi2. 2: eassumption.
   reflexivity.
Qed.

Lemma wfc_mu_aux_body_mu_imp2:
 forall phi n X,
   well_formed_closed_mu_aux (phi^{svar: n ↦ X}) n = true
   ->
   well_formed_closed_mu_aux phi (S n) = true.
Proof using .
 induction phi; firstorder.
 - simpl. cbn in H. unfold well_formed_closed_mu_aux.
   repeat case_match; simpl; auto; try lia.
   unfold well_formed_closed_mu_aux in H. case_match; auto. lia.
 - simpl in H. simpl.
   apply andb_true_iff in H. destruct H as [H1 H2].
   erewrite IHphi1. 2: apply H1.
   erewrite IHphi2. 2: apply H2.
   reflexivity.
 - simpl in H. simpl.
   apply andb_true_iff in H. destruct H as [H1 H2].
   erewrite IHphi1. 2: apply H1.
   erewrite IHphi2. 2: apply H2.
   reflexivity.
Qed.


Lemma wfc_ex_aux_bevar_subst :
forall phi psi n,
  well_formed_closed_ex_aux phi (S n) = true
  -> well_formed_closed_ex_aux psi n = true
  -> well_formed_closed_ex_aux (phi^[evar: n ↦ psi]) n = true.
Proof.
intros phi psi n H H0. 
generalize dependent n. generalize dependent psi.
induction phi; intros psi n' H H0; try lia; auto.
- simpl in *. unfold well_formed_closed_ex_aux. repeat case_match; simpl; auto. lia.
- simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
  rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
  reflexivity.
- simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
  rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
  reflexivity.
- simpl. simpl in H. rewrite IHphi. assumption. 2: reflexivity.
  eapply well_formed_closed_ex_aux_ind. 2: apply H0. lia.
- simpl. simpl in H.
  rewrite IHphi. apply H.
  eapply well_formed_closed_ex_aux_ind. 2: apply H0. lia.
  reflexivity.
Qed.

Lemma wfc_mu_aux_bevar_subst :
forall phi psi n n',
  well_formed_closed_mu_aux phi n' = true
  -> well_formed_closed_mu_aux psi n' = true
  -> well_formed_closed_mu_aux (phi^[evar: n ↦ psi]) n' = true.
Proof.
intros phi psi n n' H H0. 
generalize dependent n. generalize dependent n'. generalize dependent psi.
induction phi; intros psi n' H n'' H0; try lia; auto.
- simpl in *. unfold well_formed_closed_mu_aux. repeat case_match; simpl; auto.
- simpl. simpl in H.
  rewrite IHphi1; auto with nocore. 2: rewrite IHphi2; auto. all: destruct_and!; auto.
- simpl. simpl in H. destruct_and!.
  rewrite IHphi1; auto with nocore. rewrite IHphi2; auto.
- simpl. simpl in H. rewrite IHphi. assumption. 2: reflexivity.
  eauto using well_formed_closed_ex_aux_ind.
- simpl. simpl in H.
  rewrite IHphi. apply H. 2: reflexivity.
  eapply well_formed_closed_mu_aux_ind.
  2: eassumption. lia.
Qed.


Lemma wfc_ex_aux_bsvar_subst :
forall phi psi n n',
  well_formed_closed_ex_aux phi n = true
  -> well_formed_closed_ex_aux psi n = true
  -> well_formed_closed_ex_aux (phi^[svar: n' ↦ psi]) n = true.
Proof.
intros phi psi n n' H H0. 
generalize dependent n. generalize dependent n'. generalize dependent psi.
induction phi; intros psi n' n'' H H0; try lia; auto.
- simpl in *. unfold well_formed_closed_ex_aux. repeat case_match; simpl; auto.
- simpl. simpl in H. destruct_and!. split_and; auto.
- simpl. simpl in H. destruct_and!. split_and; auto.
- simpl. simpl in H. rewrite IHphi. assumption.
  eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia. reflexivity.
- simpl. simpl in H.
  rewrite IHphi. apply H.
  eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia. reflexivity.
Qed.

Lemma wfc_mu_aux_bsvar_subst :
forall phi psi n',
  well_formed_closed_mu_aux phi (S n') = true
  -> well_formed_closed_mu_aux psi n' = true
  -> well_formed_closed_mu_aux (phi^[svar: n' ↦ psi]) n' = true.
Proof.
intros phi psi n' H H0. 
generalize dependent n'. generalize dependent psi.
induction phi; intros psi n' H H0; try lia; auto.
- simpl in *. unfold well_formed_closed_mu_aux. repeat case_match; simpl; auto. lia.
- simpl. simpl in H. destruct_and!.
  rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
  reflexivity.
- simpl. simpl in H. destruct_and!.
  rewrite IHphi1. apply H1. assumption. rewrite IHphi2. apply H2. assumption.
  reflexivity.
- simpl. simpl in H. rewrite IHphi. assumption.
  assumption. reflexivity.
- simpl. simpl in H.
  rewrite IHphi. apply H.
  eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia. reflexivity.
Qed.


(*Helper lemma for wf_ex_to_wf_body *)
Corollary wfc_ex_aux_body_ex_imp1:
forall phi n x,
  well_formed_closed_ex_aux phi (S n) = true
  ->
  well_formed_closed_ex_aux (phi^{evar: n ↦ x}) n = true.
Proof using .
intros. apply wfc_ex_aux_bevar_subst; auto.
Qed.

Corollary wfc_mu_aux_body_ex_imp1:
forall phi n n' x,
  well_formed_closed_mu_aux phi n' = true
  ->
  well_formed_closed_mu_aux (phi^{evar: n ↦ x}) n' = true.
Proof using .
intros. now apply wfc_mu_aux_bevar_subst.
Qed.

Corollary wfc_ex_aux_body_mu_imp1:
forall phi n n' X,
  well_formed_closed_ex_aux phi n' = true
  ->
  well_formed_closed_ex_aux (phi^{svar: n ↦ X}) n' = true.
Proof using .
intros. now apply wfc_ex_aux_bsvar_subst.
Qed.

Corollary wfc_mu_aux_body_mu_imp1:
forall phi n X,
  well_formed_closed_mu_aux phi (S n) = true
  ->
  well_formed_closed_mu_aux (phi^{svar: n ↦ X}) n = true.
Proof using .
intros. now apply wfc_mu_aux_bsvar_subst.
Qed.

Lemma wfc_mu_aux_bsvar_subst_le :
forall phi psi n n', n' <= n ->
  well_formed_closed_mu_aux phi (S n) = true ->
  well_formed_closed_mu_aux psi n
  ->
  well_formed_closed_mu_aux (phi^[svar:n' ↦ psi]) n = true.
Proof using .
induction phi; intros psi n0 n' H Hwf1 Hwf2; try lia; auto.
- simpl. case_match; auto. simpl. case_match; try lia.
  simpl in Hwf1. case_match; try lia. simpl. case_match; lia.
- simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
  rewrite (IHphi1 _ _ n'); auto with nocore. rewrite (IHphi2 _ _ n'); auto.
- simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
  rewrite (IHphi1 _ _ n'); auto with nocore. rewrite (IHphi2 _ _ n'); auto.
- simpl. simpl in Hwf1. rewrite (IHphi _ _ n'); auto.
- simpl. simpl in Hwf1. rewrite (IHphi _ _ (S n')); auto. lia.
  eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
Qed.

Lemma wfc_ex_aux_bsvar_subst_le:
forall phi psi n n', n' <= n ->
  well_formed_closed_ex_aux phi (S n) = true ->
  well_formed_closed_ex_aux psi n = true
  ->
  well_formed_closed_ex_aux (phi^[evar:n'↦psi]) n = true.
Proof using .
induction phi; intros psi n0 n' H Hwf1 Hwf2; try lia; auto.
- simpl. case_match; auto. simpl. case_match; try lia.
  simpl in Hwf1. case_match; try lia. simpl. case_match; lia.
- simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
  rewrite (IHphi1 _ _ n'); auto with nocore. rewrite (IHphi2 _ _ n'); auto.
- simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
  rewrite (IHphi1 _ _ n'); auto with nocore. rewrite (IHphi2 _ _ n'); auto.
- simpl. simpl in Hwf1. rewrite (IHphi _ _ (S n')); auto. lia.
  eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
- simpl. simpl in Hwf1. rewrite (IHphi _ _ n'); auto.
Qed.

Corollary wfc_mu_aux_body_mu_imp3:
forall phi n n' X, n' <= n ->
  well_formed_closed_mu_aux phi (S n) = true
  ->
  well_formed_closed_mu_aux (phi^{svar: n' ↦ X}) n = true.
Proof using .
intros. now apply wfc_mu_aux_bsvar_subst_le.
Qed.

Corollary wfc_mu_aux_body_ex_imp3:
forall phi n n' X, n' <= n ->
  well_formed_closed_ex_aux phi (S n) = true
  ->
  well_formed_closed_ex_aux (phi^{evar: n' ↦ X}) n = true.
Proof using .
intros. now apply wfc_ex_aux_bsvar_subst_le.
Qed.

Corollary wfc_ex_aux_body_iff: 
forall phi n x,
  well_formed_closed_ex_aux phi (S n) = true
  <->
  well_formed_closed_ex_aux (phi^{evar: n ↦ x}) n = true.
Proof.
split.
apply wfc_ex_aux_body_ex_imp1.
apply wfc_ex_aux_body_ex_imp2.
Qed.

Corollary wfc_mu_aux_body_iff: 
forall phi n X,
  well_formed_closed_mu_aux phi (S n) = true
  <->
  well_formed_closed_mu_aux (phi^{svar: n ↦ X}) n = true.
Proof.
split.
apply wfc_mu_aux_body_mu_imp1.
apply wfc_mu_aux_body_mu_imp2.
Qed.


(*If (ex, phi) is closed, then its body is closed too*)
Corollary wfc_ex_to_wfc_body:
forall phi, well_formed_closed (patt_exists phi) = true -> wfc_body_ex phi.
Proof.
intros phi WFE.
unfold wfc_body_ex. intros x H.
unfold well_formed_closed in *. simpl in WFE.
apply andb_prop in WFE. destruct WFE as [WFE1 WFE2].
rewrite wfc_ex_aux_body_ex_imp1. auto.
rewrite wfc_mu_aux_body_ex_imp1. auto.
reflexivity.
Qed.



Lemma no_neg_occ_db_bevar_subst phi psi dbi1 dbi2:
well_formed_closed_mu_aux psi 0 = true ->
no_negative_occurrence_db_b dbi1 phi = true ->
no_negative_occurrence_db_b dbi1 (phi^[evar: dbi2 ↦ psi]) = true
with no_pos_occ_db_bevar_subst  phi psi dbi1 dbi2:
   well_formed_closed_mu_aux psi 0 = true ->
   no_positive_occurrence_db_b dbi1 phi = true ->
   no_positive_occurrence_db_b dbi1 (phi^[evar: dbi2 ↦ psi]) = true.
Proof.
- move: dbi1 dbi2.
induction phi; intros dbi1 dbi2 Hwfcpsi Hnonegphi; cbn in *; auto with nocore.
+ case_match; auto. now apply wfc_impl_no_neg_occ.
+ destruct_and!.
rewrite -> IHphi1, -> IHphi2; auto.
+ destruct_and!.
fold (no_positive_occurrence_db_b dbi1 (phi1^[evar: dbi2 ↦ psi]) ).
rewrite no_pos_occ_db_bevar_subst; auto with nocore.
rewrite -> IHphi2; auto.
- move: dbi1 dbi2.
induction phi; intros dbi1 dbi2 Hwfcpsi Hnonegphi; cbn in *; auto with nocore.
+ repeat case_match; auto.
apply wfc_impl_no_pos_occ. assumption.
+ destruct_and!.
rewrite -> IHphi1, -> IHphi2; auto.
+ destruct_and!.
fold (no_negative_occurrence_db_b dbi1 (phi1^[evar: dbi2 ↦ psi]) ).
rewrite no_neg_occ_db_bevar_subst; auto with nocore.
rewrite -> IHphi2; auto.
Qed.

Lemma bevar_subst_positive_2 :
forall φ ψ n,
well_formed_closed_mu_aux ψ 0 = true ->
well_formed_positive φ = true ->
well_formed_positive ψ = true ->
well_formed_positive (φ^[evar: n ↦ ψ])  = true.
Proof.
induction φ; intros ψ n' H0 H1 H2; cbn in *; auto with nocore.
* break_match_goal; auto.
* destruct_and!. rewrite -> IHφ1, -> IHφ2; auto.
* destruct_and!. rewrite -> IHφ1, -> IHφ2; auto.
* destruct_and!.
rewrite IHφ; auto with nocore.
rewrite andb_true_r.
rewrite no_neg_occ_db_bevar_subst; auto.
Qed.

Corollary wfp_evar_open : forall phi x n,
well_formed_positive phi = true ->
well_formed_positive (phi^{evar: n ↦ x}) = true.
Proof.
intros phi x n WF. apply bevar_subst_positive_2; auto.
Qed.

(* Additional lemmas: evar_open, svar_open, freshness, well_formedness, etc. *)

(* evar_open and evar_quantify are inverses *)
Lemma evar_open_evar_quantify x n phi:
well_formed_closed_ex_aux phi n ->
((phi^{{evar: x ↦ n}})^{evar: n ↦ x}) = phi.
Proof.
intros H.
(*apply wfc_wfc_ind in H.*)
move: n H.
induction phi; intros n' H; cbn; auto.
- destruct (decide (x = x0)); subst; simpl.
+ break_match_goal; auto; lia.
+ reflexivity.
- simpl in *. repeat case_match; simpl; auto with nocore; try lia; congruence.
- cbn in H. simpl. unfold evar_open, evar_quantify in IHphi1, IHphi2.
apply andb_true_iff in H.
destruct H as [H1 H2].
erewrite -> IHphi1, IHphi2 by eassumption.
reflexivity.
- simpl in H. unfold evar_open, evar_quantify in IHphi1, IHphi2.
apply andb_true_iff in H.
destruct H as [H1 H2].
erewrite -> IHphi1, IHphi2 by eassumption.
reflexivity.
- simpl in H. unfold evar_open, evar_quantify in IHphi.
erewrite -> IHphi by eassumption. reflexivity.
- simpl in H. apply IHphi in H. unfold evar_open in H. rewrite H. reflexivity.
Qed.

Lemma svar_open_svar_quantify X n phi:
well_formed_closed_mu_aux phi n ->
((phi^{{svar: X ↦ n}})^{svar: n ↦ X}) = phi.
Proof.
intros H.
(*apply wfc_wfc_ind in H.*)
move: n H.
induction phi; intros n' H; cbn; auto.
- destruct (decide (X = x)); subst; simpl.
+ break_match_goal; auto; lia.
+ reflexivity.
- simpl in *. repeat case_match; simpl; auto; subst; try lia; try congruence.
- cbn in H. simpl. unfold svar_open in IHphi1, IHphi2.
apply andb_true_iff in H.
destruct H as [H1 H2].
erewrite -> IHphi1, IHphi2 by eassumption.
reflexivity.
- simpl in H. unfold svar_open in IHphi1, IHphi2.
apply andb_true_iff in H.
destruct H as [H1 H2].
erewrite -> IHphi1, IHphi2 by eassumption.
reflexivity.
- simpl in H. unfold svar_open in IHphi.
erewrite -> IHphi by eassumption. reflexivity.
- simpl in H. apply IHphi in H. unfold svar_open in H. rewrite H. reflexivity.
Qed.

Lemma evar_quantify_evar_open x n phi:
x ∉ free_evars phi -> well_formed_closed_ex_aux phi (S n) ->
((phi^{evar: n ↦ x})^{{evar: x ↦ n}}) = phi.
Proof.
revert n.
induction phi; intros n' H0 H1; simpl; auto.
- destruct (decide (x = x0)); simpl.
+ subst. simpl in H0. apply sets.not_elem_of_singleton_1 in H0. congruence.
+ reflexivity.
- simpl in *. unfold evar_quantify,evar_open. simpl.
repeat case_match; auto; try congruence. lia.
- unfold evar_open in IHphi1, IHphi2.
rewrite sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
rewrite -> IHphi1, IHphi2.
reflexivity.
all: auto; apply andb_true_iff in H1; apply H1.
- unfold evar_open in IHphi1, IHphi2.
rewrite sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
rewrite -> IHphi1, IHphi2.
reflexivity.
all: auto; apply andb_true_iff in H1; apply H1.
- simpl in H0. unfold evar_open in IHphi.
rewrite -> IHphi by assumption. reflexivity.
- simpl in H0. unfold evar_open in IHphi.
rewrite -> IHphi by assumption. reflexivity.
Qed.

Lemma svar_quantify_svar_open X n phi:
X ∉ free_svars phi -> well_formed_closed_mu_aux phi (S n) ->
((phi^{svar: n ↦ X})^{{svar: X ↦ n}}) = phi.
Proof.
revert n.
induction phi; intros n' H0 H1; simpl; auto.
- destruct (decide (X = x)); simpl.
+ subst. simpl in H0. apply sets.not_elem_of_singleton_1 in H0. congruence.
+ reflexivity.
- simpl in *. unfold svar_quantify,svar_open,bsvar_subst.
repeat case_match; auto; try congruence. lia.
- unfold svar_open in IHphi1, IHphi2.
rewrite sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
rewrite -> IHphi1, IHphi2.
reflexivity.
all: auto; apply andb_true_iff in H1; apply H1.
- unfold svar_open in IHphi1, IHphi2.
rewrite sets.not_elem_of_union in H0. destruct H0 as [E1 E2].
rewrite -> IHphi1, IHphi2.
reflexivity.
all: auto; apply andb_true_iff in H1; apply H1.
- simpl in H0. unfold svar_open in IHphi.
erewrite -> IHphi by assumption. reflexivity.
- simpl in H0. unfold svar_open in IHphi.
erewrite -> IHphi by assumption. reflexivity.
Qed.

Lemma double_evar_quantify φ : forall x n,
φ^{{evar: x ↦ n}}^{{evar: x ↦ n}} = φ^{{evar: x ↦ n}}.
Proof.
induction φ; intros x' n'; simpl; auto.
* unfold evar_quantify. repeat case_match; auto. contradiction.
* now rewrite -> IHφ1, -> IHφ2.
* now rewrite -> IHφ1, -> IHφ2.
* now rewrite IHφ.
* now rewrite IHφ.
Qed.

Lemma double_svar_quantify φ : forall X n,
φ^{{svar: X ↦ n}}^{{svar: X ↦ n}} = φ^{{svar: X ↦ n}}.
Proof.
induction φ; intros x' n'; simpl; auto.
* unfold svar_quantify. repeat case_match; auto. contradiction.
* now rewrite -> IHφ1, -> IHφ2.
* now rewrite -> IHφ1, -> IHφ2.
* now rewrite IHφ.
* now rewrite IHφ.
Qed.

Lemma well_formed_bevar_subst φ : forall ψ n m,
m >= n -> well_formed_closed_ex_aux φ n ->
(φ^[evar: m ↦ ψ]) = φ.
Proof.
induction φ; intros ψ n' m' H H0; simpl; auto.
* simpl in H0. repeat case_match; auto; try lia; congruence.
* simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
3: apply eq_sym, H1.
4: apply eq_sym, H0. all: auto.
* simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
3: apply eq_sym, H1.
4: apply eq_sym, H0. all: auto.
* simpl in H0. erewrite IHφ. 3: apply H0. auto. lia.
* simpl in H0. erewrite IHφ. 3: apply H0. all: auto.
Qed.

Lemma well_formed_bsvar_subst φ : forall ψ k m,
m >= k -> well_formed_closed_mu_aux φ k ->
(φ^[svar: m ↦ ψ]) = φ.
Proof.
induction φ; intros ψ k' m' H H0; simpl; auto.
* simpl in H0. repeat case_match; auto; try lia; congruence.
* simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
3: apply eq_sym, H1.
4: apply eq_sym, H0. all: auto.
* simpl in H0. apply eq_sym, andb_true_eq in H0. destruct H0. erewrite IHφ1, IHφ2.
3: apply eq_sym, H1.
4: apply eq_sym, H0. all: auto.
* simpl in H0. erewrite IHφ. 3: apply H0. auto. lia.
* simpl in H0. erewrite IHφ. 3: apply H0. all: auto. lia.
Qed.

(* bevar_subst is identity if n does not occur in phi *)
Corollary bevar_subst_not_occur n ψ ϕ :
well_formed_closed_ex_aux ϕ n ->
(ϕ^[evar: n ↦ ψ]) = ϕ.
Proof.
intro H. eapply well_formed_bevar_subst; eauto.
Qed.

(* evar_open is identity if n does not occur in phi *)
Corollary evar_open_not_occur n x ϕ :
well_formed_closed_ex_aux ϕ n ->
ϕ^{evar: n ↦ x} = ϕ.
Proof.
apply bevar_subst_not_occur.
Qed.

(* bsvar_subst is identity if n does not occur in phi *)
Corollary bsvar_subst_not_occur n ψ ϕ :
well_formed_closed_mu_aux ϕ n ->
(ϕ^[svar: n ↦ ψ]) = ϕ.
Proof.
intro H. eapply well_formed_bsvar_subst; eauto.
Qed.

(* evar_open is identity if n does not occur in phi *)
Corollary svar_open_not_occur n x ϕ :
well_formed_closed_mu_aux ϕ n ->
ϕ^{svar: n ↦ x} = ϕ.
Proof.
apply bsvar_subst_not_occur.
Qed.

(* opening on closed patterns is identity *)
Lemma evar_open_closed :
forall phi,
well_formed_closed_ex_aux phi 0 ->
forall n v,
  phi^{evar: n ↦ v} = phi.
Proof.
intros phi H n v. unfold evar_open. erewrite well_formed_bevar_subst. 3: exact H.
auto. lia.
Qed.

Lemma svar_open_closed :
forall phi,
well_formed_closed_mu_aux phi 0 ->
forall n v,
  phi^{svar: n ↦ v} = phi.
Proof. 
intros phi H n v. unfold svar_open. erewrite well_formed_bsvar_subst. 3: exact H.
auto. lia.
Qed.

Lemma bevar_subst_comm_higher :
forall phi psi1 psi2 n m, 
n > m -> well_formed_closed_ex_aux psi1 0 -> well_formed_closed_ex_aux psi2 0 ->
(phi^[evar: n ↦ psi1])^[evar: m ↦ psi2] = 
(phi^[evar: m ↦ psi2])^[evar: pred n ↦ psi1].
Proof.
induction phi; intros psi1 psi2 n0 m0 NEQ Hwf1 Hwf2; simpl; auto.
- repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto; subst; try congruence.
all:  repeat case_match; try lia; auto.
1-2: subst; erewrite well_formed_bevar_subst; try eassumption; auto; lia.
- rewrite -> IHphi1, -> IHphi2; auto.
- rewrite -> IHphi1, -> IHphi2; auto.
- rewrite -> IHphi; auto; try lia.
replace (pred (S n0)) with n0 by lia.
now replace (S (pred n0)) with n0 by lia.
- rewrite -> IHphi; auto.
Qed.

Lemma bevar_subst_comm_lower :
forall phi psi1 psi2 n m, 
n < m -> well_formed_closed_ex_aux psi1 0 -> well_formed_closed_ex_aux psi2 0 ->
(phi^[evar: n ↦ psi1])^[evar: m ↦ psi2] = 
(phi^[evar: S m ↦ psi2])^[evar: n ↦ psi1].
Proof.
induction phi; intros psi1 psi2 n0 m0 NEQ Hwf1 Hwf2; simpl; auto.
- repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto; subst; try congruence.
all:  repeat case_match; try lia; auto.
1-2: subst; erewrite well_formed_bevar_subst; try eassumption; auto. 2: lia.
eapply well_formed_closed_ex_aux_ind. 2: exact Hwf1. lia.
- rewrite -> IHphi1, -> IHphi2; auto.
- rewrite -> IHphi1, -> IHphi2; auto.
- rewrite -> IHphi; auto; try lia.
- rewrite -> IHphi; auto.
Qed.

Lemma bsvar_subst_comm_higher :
forall phi psi1 psi2 n m, 
n > m -> well_formed_closed_mu_aux psi1 0 -> well_formed_closed_mu_aux psi2 0 ->
(phi^[svar: n ↦ psi1])^[svar: m ↦ psi2] = 
(phi^[svar: m ↦ psi2])^[svar: pred n ↦ psi1].
Proof.
induction phi; intros psi1 psi2 n0 m0 NEQ Hwf1 Hwf2; simpl; auto.
- repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto; subst; try congruence.
all:  repeat case_match; try lia; auto.
1-2: subst; erewrite well_formed_bsvar_subst; try eassumption; auto; lia.
- rewrite -> IHphi1, -> IHphi2; auto.
- rewrite -> IHphi1, -> IHphi2; auto.
- rewrite -> IHphi; auto.
- rewrite -> IHphi; auto. 2: lia.
replace (pred (S n0)) with n0 by lia.
now replace (S (pred n0)) with n0 by lia.
Qed.

Lemma bsvar_subst_comm_lower :
forall phi psi1 psi2 n m, 
n < m -> well_formed_closed_mu_aux psi1 0 -> well_formed_closed_mu_aux psi2 0 ->
(phi^[svar: n ↦ psi1])^[svar: m ↦ psi2] = 
(phi^[svar: S m ↦ psi2])^[svar: n ↦ psi1].
Proof.
induction phi; intros psi1 psi2 n0 m0 NEQ Hwf1 Hwf2; simpl; auto.
- repeat case_match; simpl; try rewrite -> Heqc; try rewrite -> Heqc0; auto; subst; try congruence.
all:  repeat case_match; try lia; auto.
1-2: subst; erewrite well_formed_bsvar_subst; try eassumption; auto. 2: lia.
eapply well_formed_closed_mu_aux_ind. 2: exact Hwf1. lia.
- rewrite -> IHphi1, -> IHphi2; auto.
- rewrite -> IHphi1, -> IHphi2; auto.
- rewrite -> IHphi; auto.
- rewrite -> IHphi; auto. lia.
Qed.

Corollary evar_open_comm_higher:
forall n m,
n < m 
->
forall x y phi,
  phi^{evar: m ↦ y}^{evar: n ↦ x} = phi^{evar: n ↦ x}^{evar: pred m ↦ y}.
Proof.
intros n m Hneqnm x y phi. apply bevar_subst_comm_higher; auto.
Qed.

Corollary evar_open_comm_lower:
forall n m,
n > m 
->
forall x y phi,
  phi^{evar: m ↦ y}^{evar: n ↦ x} = phi^{evar: S n ↦ x}^{evar: m ↦ y}.
Proof.
intros n m Hneqnm x y phi. apply bevar_subst_comm_lower; auto.
Qed.

Corollary svar_open_comm_higher:
forall n m,
n < m 
->
forall X Y phi,
   phi^{svar: m ↦ Y}^{svar: n ↦ X} = phi^{svar: n ↦ X}^{svar: pred m ↦ Y} .
Proof.
intros n m Hneqnm x y phi. apply bsvar_subst_comm_higher; auto.
Qed.

Corollary svar_open_comm_lower:
forall n m,
n > m
->
forall X Y phi,
  phi^{svar: m ↦ Y} ^{svar: n ↦ X} = phi^{svar: S n ↦ X} ^{svar: m ↦ Y}.
Proof.
intros n m Hneqnm x y phi. apply bsvar_subst_comm_lower; auto.
Qed.

Lemma bevar_subst_bsvar_subst phi psi1 psi2 dbi1 dbi2
: well_formed_closed psi1 -> well_formed_closed psi2 ->
(phi^[svar: dbi1 ↦ psi1])^[evar: dbi2 ↦ psi2] = 
(phi^[evar: dbi2 ↦ psi2])^[svar: dbi1 ↦ psi1].
Proof.
generalize dependent dbi1. generalize dependent dbi2.
induction phi; intros dbi1 dbi2 Hwf1 Hwf2; simpl; auto.
* break_match_goal; auto. erewrite well_formed_bsvar_subst; auto.
unfold well_formed_closed in *. destruct_and!.
eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
* break_match_goal; auto. erewrite well_formed_bevar_subst; auto.
unfold well_formed_closed in *. destruct_and!.
eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
* simpl. rewrite -> IHphi1, -> IHphi2; auto.
* simpl. rewrite -> IHphi1, -> IHphi2; auto.
* simpl. rewrite IHphi; auto.
* simpl. rewrite IHphi; auto.
Qed.

Corollary svar_open_evar_open_comm
: forall (phi : Pattern) (dbi1 : db_index)(x : evar)(dbi2 : db_index)(X : svar),
  phi^{svar: dbi2 ↦ X}^{evar: dbi1 ↦ x}  = phi^{evar: dbi1 ↦ x}^{svar: dbi2 ↦ X} .
Proof.
intros phi dbi1 x dbi2 X. apply bevar_subst_bsvar_subst; auto.
Qed.


Lemma free_svars_evar_open : forall (ϕ : Pattern) (dbi :db_index) (x : evar),
free_svars ϕ^{evar: dbi ↦ x} = free_svars ϕ.
Proof.
unfold evar_open.
induction ϕ; intros dbi x'; simpl; try reflexivity.
* case_match; reflexivity.
* rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
* rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
* rewrite -> IHϕ. reflexivity.
* rewrite -> IHϕ. reflexivity.
Qed.


Lemma positive_negative_occurrence_db_named :
forall (phi : Pattern) (dbi : db_index) (X : svar),
  (no_positive_occurrence_db_b dbi phi ->
   svar_has_positive_occurrence X phi = false ->
   svar_has_positive_occurrence X (phi^{svar: dbi ↦ X}) = false)
  /\ (no_negative_occurrence_db_b dbi phi ->
      svar_has_negative_occurrence X phi = false ->
      svar_has_negative_occurrence X (phi^{svar: dbi ↦ X}) = false).
Proof.
unfold svar_open.
induction phi; intros dbi X; split; simpl; try firstorder; cbn in *.
* do 2 case_match; auto; congruence.
* case_match; auto; congruence.
* destruct_and!. apply orb_false_iff in H0 as [H01 H02].
  erewrite -> (proj1 (IHphi1 _ _)), -> (proj1 (IHphi2 _ _)); auto.
* destruct_and!. apply orb_false_iff in H0 as [H01 H02].
  erewrite -> (proj2 (IHphi1 _ _)), -> (proj2 (IHphi2 _ _)); auto.
* destruct_and!. apply orb_false_iff in H0 as [H01 H02].
  erewrite -> (proj2 (IHphi1 _ _)), -> (proj1 (IHphi2 _ _)); auto.
* destruct_and!. apply orb_false_iff in H0 as [H01 H02].
  erewrite -> (proj1 (IHphi1 _ _)), -> (proj2 (IHphi2 _ _)); auto.
Qed.

Lemma positive_negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
  (svar_has_positive_occurrence X (ϕ^{evar: dbi ↦ x}) = false <-> svar_has_positive_occurrence X ϕ = false)
  /\ (svar_has_negative_occurrence X (ϕ^{evar: dbi ↦ x}) = false <-> svar_has_negative_occurrence X ϕ = false).
Proof.
unfold evar_open.
induction ϕ; intros dbi X; split; simpl; auto; cbn.
* case_match; auto; congruence.
* case_match; auto; congruence.
* split.
  - intro H. apply orb_false_iff in H as [? ?].
    erewrite -> (proj1 (proj1 (IHϕ1 _ _ _))), -> (proj1 (proj1 (IHϕ2 _ _ _))); eauto.
  - intro H. apply orb_false_iff in H as [? ?].
    erewrite -> (proj2 (proj1 (IHϕ1 _ _ _))), -> (proj2 (proj1 (IHϕ2 _ _ _))); eauto.
* split.
  - intro H. apply orb_false_iff in H as [? ?].
    erewrite -> (proj1 (proj2 (IHϕ1 _ _ _))), -> (proj1 (proj2 (IHϕ2 _ _ _))); eauto.
  - intro H. apply orb_false_iff in H as [? ?].
    erewrite -> (proj2 (proj2 (IHϕ1 _ _ _))), -> (proj2 (proj2 (IHϕ2 _ _ _))); eauto.
* split.
  - intro H. apply orb_false_iff in H as [? ?].
    erewrite -> (proj1 (proj2 (IHϕ1 _ _ _))), -> (proj1 (proj1 (IHϕ2 _ _ _))); eauto.
  - intro H. apply orb_false_iff in H as [? ?].
    erewrite -> (proj2 (proj2 (IHϕ1 _ _ _))), -> (proj2 (proj1 (IHϕ2 _ _ _))); eauto.
* split.
  - intro H. apply orb_false_iff in H as [? ?].
    erewrite -> (proj1 (proj1 (IHϕ1 _ _ _))), -> (proj1 (proj2 (IHϕ2 _ _ _))); eauto.
  - intro H. apply orb_false_iff in H as [? ?].
    erewrite -> (proj2 (proj1 (IHϕ1 _ _ _))), -> (proj2 (proj2 (IHϕ2 _ _ _))); eauto.
* split.
  - intro H. erewrite -> (proj1 (proj1 (IHϕ _ _ _))); eauto.
  - intro H. erewrite -> (proj2 (proj1 (IHϕ _ _ _))); eauto.
* split.
  - intro H. erewrite -> (proj1 (proj2 (IHϕ _ _ _))); eauto.
  - intro H. erewrite -> (proj2 (proj2 (IHϕ _ _ _))); eauto.
* split.
  - intro H. erewrite -> (proj1 (proj1 (IHϕ _ _ _))); eauto.
  - intro H. erewrite -> (proj2 (proj1 (IHϕ _ _ _))); eauto.
* split.
  - intro H. erewrite -> (proj1 (proj2 (IHϕ _ _ _))); eauto.
  - intro H. erewrite -> (proj2 (proj2 (IHϕ _ _ _))); eauto.
Qed.

Corollary positive_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
  svar_has_positive_occurrence X (ϕ^{evar: dbi ↦ x}) = false <-> svar_has_positive_occurrence X ϕ = false.
Proof.
apply positive_negative_occurrence_evar_open.
Qed.

Corollary negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
  svar_has_negative_occurrence X (ϕ^{evar: dbi ↦ x}) = false <-> svar_has_negative_occurrence X ϕ = false.
Proof.
apply positive_negative_occurrence_evar_open.
Qed.

Lemma positive_negative_occurrence_db_svar_open_le : forall (phi : Pattern) (dbi1 dbi2 : db_index) (X : svar),
  dbi1 < dbi2 ->
  (
    no_positive_occurrence_db_b dbi1 phi ->
    no_positive_occurrence_db_b dbi1 (phi^{svar: dbi2 ↦ X})
  )
  /\ (no_negative_occurrence_db_b dbi1 phi -> no_negative_occurrence_db_b dbi1 (phi^{svar: dbi2 ↦ X})).
Proof.
unfold svar_open.
induction phi; intros dbi1 dbi2 X Hneq; split; intros H; simpl in *; auto; cbn in *.
+ do 2 case_match; auto; cbn; case_match; auto. lia.
+ case_match; constructor; auto.
+ destruct_and!; split_and!.
  - now apply IHphi1.
  - now apply IHphi2.
+ destruct_and!; split_and!.
  - now apply IHphi1.
  - now apply IHphi2.
+ destruct_and!; split_and!.
  - now apply IHphi1.
  - now apply IHphi2.
+ destruct_and!; split_and!.
  - now apply IHphi1.
  - now apply IHphi2.
+ now apply IHphi.
+ now apply IHphi.
+ apply IHphi; auto. lia.
+ apply IHphi; auto. lia.
Qed.

Lemma wfp_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar),
  well_formed_positive phi = true ->
  well_formed_positive (phi^{svar: dbi ↦ X}) = true.
Proof.
unfold svar_open.
induction phi; simpl; intros dbi X H.
+ constructor.
+ constructor.
+ constructor.
+ simpl. case_match; constructor.
+ constructor.
+ inversion H. apply andb_true_iff in H1. destruct H1 as [H1 H2].
  rewrite IHphi1. assumption. rewrite IHphi2. assumption.
  destruct_and!. symmetry. simpl. split_and!; auto.
+ constructor.
+ apply andb_true_iff in H. destruct H as [H1 H2]. rewrite IHphi1. apply H1. rewrite IHphi2. apply H2.
  reflexivity.
+ simpl in H. simpl. auto.
+ simpl in H. simpl. apply andb_true_iff in H. destruct H as [H1 H2].
  rewrite IHphi. apply H2. rewrite andb_true_r.
  apply positive_negative_occurrence_db_svar_open_le; auto. lia.
Qed.

Lemma positive_negative_occurrence_named_svar_open :
forall (phi : Pattern) (X Y : svar) (dbi : db_index),
  X <> Y ->
  (
    svar_has_negative_occurrence X phi = false ->
    svar_has_negative_occurrence X (phi^{svar: dbi ↦ Y}) = false
  ) /\ (
    svar_has_positive_occurrence X phi = false ->
    svar_has_positive_occurrence X (phi^{svar: dbi ↦ Y}) = false
  ).
Proof.
unfold svar_open.
induction phi; intros X Y dbi XneY; split; intros Hneg; simpl in *; auto; try firstorder.
- now case_match.
- case_match; try auto. cbn. case_match; auto. congruence.
- apply orb_false_iff in Hneg as [H1 H2].
  cbn.
  now erewrite -> (proj1 (IHphi1 X Y dbi XneY)), -> (proj1 (IHphi2 X Y dbi XneY)).
- apply orb_false_iff in Hneg as [H1 H2].
  cbn.
  now erewrite -> (proj2 (IHphi1 X Y dbi XneY)), -> (proj2 (IHphi2 X Y dbi XneY)).
- apply orb_false_iff in Hneg as [H1 H2]. cbn. fold svar_has_positive_occurrence.
  now erewrite -> (proj2 (IHphi1 X Y dbi XneY)), -> (proj1 (IHphi2 X Y dbi XneY)).
- apply orb_false_iff in Hneg as [H1 H2]. cbn. fold svar_has_negative_occurrence.
  now erewrite -> (proj1 (IHphi1 X Y dbi XneY)), -> (proj2 (IHphi2 X Y dbi XneY)).
Qed.

Corollary evar_open_wfc_aux db1 db2 X phi :
db1 <= db2 ->
well_formed_closed_ex_aux phi db1 ->
phi^{evar: db2 ↦ X} = phi.
Proof.
intros H H0. unfold evar_open. eapply well_formed_bevar_subst. 2: eassumption. auto.
Qed.

Corollary evar_open_wfc m X phi : well_formed_closed_ex_aux phi 0 -> phi^{evar: m ↦ X} = phi.
Proof.
intros H.
unfold well_formed_closed in H.
apply evar_open_wfc_aux with (X := X)(db2 := m) in H.
2: lia.
auto.
Qed.

Corollary svar_open_wfc_aux db1 db2 X phi :
db1 <= db2 ->
well_formed_closed_mu_aux phi db1 ->
phi^{svar: db2 ↦ X} = phi.
Proof.
intros H H0. unfold evar_open. eapply well_formed_bsvar_subst. 2: eassumption. auto.
Qed.

Corollary svar_open_wfc m X phi : well_formed_closed_mu_aux phi 0 -> phi^{svar: m ↦ X} = phi.
Proof.
intros H.
unfold well_formed_closed in H.
apply svar_open_wfc_aux with (X := X)(db2 := m) in H.
2: lia.
auto.
Qed.

Corollary evar_open_bsvar_subst m phi1 phi2 dbi X
: well_formed_closed phi2 ->
  phi1^[svar: dbi ↦ phi2]^{evar: m ↦ X}
  = phi1^{evar: m ↦ X}^[svar: dbi ↦ phi2].
Proof.
intro H. apply bevar_subst_bsvar_subst; auto.
Qed.

Corollary svar_open_bevar_subst m phi1 phi2 dbi X
  : well_formed_closed phi2 ->
    phi1^[evar: dbi ↦ phi2]^{svar: m ↦ X}
    = phi1^{svar: m ↦ X}^[evar: dbi ↦ phi2].
Proof.
  intro H. apply eq_sym, bevar_subst_bsvar_subst; auto.
Qed.

Corollary svar_open_bsvar_subst_higher m phi1 phi2 dbi X
  : well_formed_closed phi2 ->
    m < dbi ->
    phi1^[svar: dbi ↦ phi2]^{svar: m ↦ X}
    = phi1^{svar: m ↦ X}^[svar: pred dbi ↦ phi2].
Proof.
  intros H H0. apply bsvar_subst_comm_higher; auto.
  unfold well_formed_closed in *. destruct_and!. auto.
Qed.

Corollary svar_open_bsvar_subst_lower m phi1 phi2 dbi X
  : well_formed_closed phi2 ->
    m > dbi ->
    phi1^[svar: dbi ↦ phi2]^{svar: m ↦ X}
    = phi1^{svar: S m ↦ X}^[svar: dbi ↦ phi2].
Proof.
  intros H H0. apply bsvar_subst_comm_lower; auto.
  unfold well_formed_closed in *. destruct_and!. auto.
Qed.

Corollary evar_open_bevar_subst_higher m phi1 phi2 dbi X
  : well_formed_closed_ex_aux phi2 0 ->
    m < dbi ->
    phi1^[evar: dbi ↦ phi2]^{evar: m ↦ X}
    = phi1^{evar: m ↦ X}^[evar: pred dbi ↦ phi2].
Proof.
  intros H H0. apply bevar_subst_comm_higher; auto.
Qed.

Corollary evar_open_bevar_subst_lower m phi1 phi2 dbi X
  : well_formed_closed phi2 ->
    m > dbi ->
    phi1^[evar: dbi ↦ phi2]^{evar: m ↦ X}
    = phi1^{evar: S m ↦ X}^[evar: dbi ↦ phi2].
Proof.
  intros H H0. apply bevar_subst_comm_lower; auto.
  unfold well_formed_closed in *. destruct_and!. auto.
Qed.



Lemma free_svars_bsvar_subst' :
  forall φ ψ dbi X,
    (X ∈ free_svars (φ^[svar: dbi ↦ ψ])) <->
    ((X ∈ (free_svars ψ) /\ bsvar_occur φ dbi) \/ (X ∈ (free_svars φ))).
Proof.
  induction φ; intros ψ dbi X; simpl.
  - split; intros H; auto.
    destruct H.
    destruct H. congruence. assumption.
  - split; intros H; auto.
    destruct H; auto.
    destruct H; congruence.
  - split; intros H; auto.
    destruct H; auto.
    destruct H; congruence.
  - case_match; split; intros H'.
    + simpl in H'. set_solver.
    + destruct H' as [H'|H'].
      * destruct H'; auto. case_match; auto; subst. lia. congruence.
      * set_solver.
    + left. split; auto. case_match; auto.
    + simpl in H. set_solver.
    + simpl in H. set_solver.
    + destruct H' as [H'|H'].
      * destruct H'. case_match; try lia; congruence.
      * set_solver.
  - split; intros H'; auto.
    destruct H' as [H'|H'].
    + destruct H'. congruence.
    + set_solver.
  - rewrite elem_of_union.
    rewrite elem_of_union.
    rewrite IHφ1.
    rewrite IHφ2.
    split; intros H.
    + destruct H.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. auto.
        -- right. left. assumption.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. apply orbT.
        -- right. right. assumption.
    + destruct H.
      * destruct H as [H1 H2].
        destruct (decide (bsvar_occur φ1 dbi)).
        -- left. left. split; assumption.
        -- destruct (decide (bsvar_occur φ2 dbi)).
          2: { apply orb_prop in H2. destruct H2.
                rewrite H in n. congruence.
                rewrite H in n0. congruence.
          }
          right.
          left. split; assumption.
      * destruct H.
        -- left. right. assumption.
        -- right. right. assumption.
  - split; intros H; auto.
    destruct H.
    + destruct H. congruence.
    + set_solver.
  - rewrite elem_of_union.
    rewrite elem_of_union.
    rewrite IHφ1.
    rewrite IHφ2.
    split; intros H.
    + destruct H.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. auto.
        -- right. left. assumption.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. apply orbT.
        -- right. right. assumption.
    + destruct H.
      * destruct H as [H1 H2].
        destruct (decide (bsvar_occur φ1 dbi)).
        -- left. left. split; assumption.
        -- destruct (decide (bsvar_occur φ2 dbi)).
          2: { apply orb_prop in H2. destruct H2.
                rewrite H in n. congruence.
                rewrite H in n0. congruence.
          }
          right.
          left. split; assumption.
      * destruct H.
        -- left. right. assumption.
        -- right. right. assumption.
  - rewrite IHφ. auto.
  - rewrite IHφ. auto.
Qed.

Lemma free_evars_bsvar_subst' :
  forall φ ψ dbi x,
    (x ∈ free_evars (φ^[svar: dbi ↦ ψ])) <->
    ((x ∈ (free_evars ψ) /\ bsvar_occur φ dbi) \/ (x ∈ (free_evars φ))).
Proof.
  induction φ; intros ψ dbi X; simpl.
  - split; intros H; auto.
    destruct H.
    destruct H. congruence. assumption.
  - split; intros H; auto.
    destruct H; auto.
    destruct H; congruence.
  - split; intros H; auto.
    destruct H; auto.
    destruct H; congruence.
  - case_match; split; intros H'.
    + simpl in H'. set_solver.
    + destruct H' as [H'|H'].
      * destruct H'; auto. case_match; auto; subst. lia. congruence.
      * set_solver.
    + left. split; auto. case_match; auto.
    + simpl in H. set_solver.
    + simpl in H. set_solver.
    + destruct H' as [H'|H'].
      * destruct H'. case_match; try lia; congruence.
      * set_solver.
  - split; intros H'; auto.
    destruct H' as [H'|H'].
    + destruct H'. congruence.
    + set_solver.
  - rewrite elem_of_union.
    rewrite elem_of_union.
    rewrite IHφ1.
    rewrite IHφ2.
    split; intros H.
    + destruct H.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. auto.
        -- right. left. assumption.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. apply orbT.
        -- right. right. assumption.
    + destruct H.
      * destruct H as [H1 H2].
        destruct (decide (bsvar_occur φ1 dbi)).
        -- left. left. split; assumption.
        -- destruct (decide (bsvar_occur φ2 dbi)).
          2: { apply orb_prop in H2. destruct H2.
                rewrite H in n. congruence.
                rewrite H in n0. congruence.
          }
          right.
          left. split; assumption.
      * destruct H.
        -- left. right. assumption.
        -- right. right. assumption.
  - split; intros H; auto.
    destruct H.
    + destruct H. congruence.
    + set_solver.
  - rewrite elem_of_union.
    rewrite elem_of_union.
    rewrite IHφ1.
    rewrite IHφ2.
    split; intros H.
    + destruct H.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. auto.
        -- right. left. assumption.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. apply orbT.
        -- right. right. assumption.
    + destruct H.
      * destruct H as [H1 H2].
        destruct (decide (bsvar_occur φ1 dbi)).
        -- left. left. split; assumption.
        -- destruct (decide (bsvar_occur φ2 dbi)).
          2: { apply orb_prop in H2. destruct H2.
                rewrite H in n. congruence.
                rewrite H in n0. congruence.
          }
          right.
          left. split; assumption.
      * destruct H.
        -- left. right. assumption.
        -- right. right. assumption.
  - rewrite IHφ. auto.
  - rewrite IHφ. auto.
Qed.

Lemma free_evars_bevar_subst' :
  forall φ ψ dbi X,
    (X ∈ free_evars (φ^[evar: dbi ↦ ψ])) <->
    ((X ∈ (free_evars ψ) /\ bevar_occur φ dbi) \/ (X ∈ (free_evars φ))).
Proof.
  induction φ; intros ψ dbi X; simpl.
  - split; intros H; auto.
    destruct H.
    destruct H. congruence. assumption.
  - split; intros H; auto.
    destruct H; auto.
    destruct H; congruence.
  - case_match; split; intros H'.
    + simpl in H'. set_solver.
    + destruct H' as [H'|H'].
      * destruct H'; auto. case_match; auto; subst. lia. congruence.
      * set_solver.
    + left. split; auto. case_match; auto.
    + simpl in H'. set_solver.
    + simpl in H'. set_solver.
    + destruct H' as [H'|H'].
      * destruct H'. case_match; try lia; congruence.
      * set_solver.
  - split; intros H; auto.
    destruct H; auto.
    destruct H; congruence.
  - split; intros H; auto.
    destruct H.
    + destruct H. congruence.
    + set_solver.
  - rewrite elem_of_union.
    rewrite elem_of_union.
    rewrite IHφ1.
    rewrite IHφ2.
    split; intros H.
    + destruct H.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. auto.
        -- right. left. assumption.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. apply orbT.
        -- right. right. assumption.
    + destruct H.
      * destruct H as [H1 H2].
        destruct (decide (bevar_occur φ1 dbi)).
        -- left. left. split; assumption.
        -- destruct (decide (bevar_occur φ2 dbi)).
          2: { apply orb_prop in H2. destruct H2.
                rewrite H in n. congruence.
                rewrite H in n0. congruence.
          }
          right.
          left. split; assumption.
      * destruct H.
        -- left. right. assumption.
        -- right. right. assumption.
  - split; intros H; auto.
    destruct H.
    + destruct H. congruence.
    + set_solver.
  - rewrite elem_of_union.
    rewrite elem_of_union.
    rewrite IHφ1.
    rewrite IHφ2.
    split; intros H.
    + destruct H.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. auto.
        -- right. left. assumption.
      * destruct H.
        -- left. destruct H.
          split; auto. rewrite H0. apply orbT.
        -- right. right. assumption.
    + destruct H.
      * destruct H as [H1 H2].
        destruct (decide (bevar_occur φ1 dbi)).
        -- left. left. split; assumption.
        -- destruct (decide (bevar_occur φ2 dbi)).
          2: { apply orb_prop in H2. destruct H2.
                rewrite H in n. congruence.
                rewrite H in n0. congruence.
          }
          right.
          left. split; assumption.
      * destruct H.
        -- left. right. assumption.
        -- right. right. assumption.
  - rewrite IHφ. auto.
  - rewrite IHφ. auto.
Qed.


Lemma free_svars_bsvar_subst :
  forall φ ψ dbi,
  free_svars (φ^[svar: dbi ↦ ψ]) ⊆ union (free_svars ψ) (free_svars φ).
Proof.
  induction φ; intros ψ dbi; simpl; try set_solver.
  case_match; simpl; set_solver.
Qed.

Lemma free_evars_bevar_subst :
  forall φ ψ dbi,
  free_evars (φ^[evar: dbi ↦ ψ]) ⊆ union (free_evars ψ) (free_evars φ).
Proof.
  induction φ; intros ψ dbi Hwf; simpl; try set_solver.
  case_match; simpl; set_solver.
Qed.

Lemma free_svars_svar_open'' :
forall φ dbi X Y,
  (X ∈ free_svars (φ^{svar: dbi ↦ Y})) <->
  (((X = Y) /\ (bsvar_occur φ dbi)) \/ (X ∈ (free_svars φ))).
Proof.
  intros φ dbi X Y.
  unfold svar_open.
  pose proof (Htmp := free_svars_bsvar_subst' φ (patt_free_svar Y) dbi X).
  simpl in Htmp.
  assert (X ∈ @singleton _ SVarSet _ Y <-> X = Y) by set_solver.
  tauto.
Qed.

Corollary free_svars_svar_open ϕ X dbi :
  free_svars (ϕ^{svar: dbi ↦ X}) ⊆ union (singleton X) (free_svars ϕ).
Proof.
  apply free_svars_bsvar_subst; auto.
Qed.

Lemma free_evars_evar_open'' :
forall φ dbi x y,
  (x ∈ free_evars (φ^{evar: dbi ↦ y})) <->
  ((x = y /\ bevar_occur φ dbi) \/ (x ∈ (free_evars φ))).
Proof.
  intros φ dbi x y.
  unfold evar_open.
  pose proof (Htmp := free_evars_bevar_subst' φ (patt_free_evar y) dbi x).
  simpl in Htmp.
  assert (x ∈ @singleton _ EVarSet _ y <-> x = y) by set_solver;
  tauto.
Qed.

Corollary free_evars_evar_open ϕ x dbi :
  free_evars (ϕ^{evar: dbi ↦ x}) ⊆ union (singleton x) (free_evars ϕ).
Proof.
  apply free_evars_bevar_subst; auto.
Qed.

Lemma free_evars_evar_open' ϕ x dbi:
  free_evars ϕ ⊆ free_evars (ϕ^{evar: dbi ↦ x}).
Proof.
  move: dbi.
  induction ϕ; intros dbi; simpl; try apply empty_subseteq.
  - apply PreOrder_Reflexive.
  - apply union_least.
    + eapply PreOrder_Transitive. apply IHϕ1.
      apply union_subseteq_l.
    + eapply PreOrder_Transitive. apply IHϕ2.
      apply union_subseteq_r.
  - apply union_least.
    + eapply PreOrder_Transitive. apply IHϕ1.
      apply union_subseteq_l.
    + eapply PreOrder_Transitive. apply IHϕ2.
      apply union_subseteq_r.
  - set_solver.
  - set_solver.
Qed.

Lemma free_evar_subst_no_occurrence x p q:
  x ∉ free_evars p ->
  p^[[evar:x ↦ q]] = p.
Proof.
  intros H.
  remember (size' p) as sz.
  assert (Hsz: size' p <= sz) by lia.
  clear Heqsz.

  move: p Hsz H.
  induction sz; intros p Hsz H; destruct p; simpl in *; try lia; auto.
  - simpl in H. simpl.
    destruct (decide (x = x0)).
    + subst x0. set_solver.
    + reflexivity.
  - rewrite IHsz. lia. set_solver. rewrite IHsz. lia. set_solver. reflexivity.
  - rewrite IHsz. lia. set_solver. rewrite IHsz. lia. set_solver. reflexivity.
  - f_equal. rewrite IHsz. lia. exact H. reflexivity.
  - rewrite IHsz; auto. lia.
Qed.


Lemma Private_bsvar_occur_evar_open sz dbi1 dbi2 X phi:
size phi <= sz ->
bsvar_occur phi dbi1 = false ->
bsvar_occur (phi^{evar: dbi2 ↦ X}) dbi1 = false.
Proof.
move: phi dbi1 dbi2.
induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H; firstorder.
2: { simpl. lia. }
cbn. case_match; reflexivity.
Qed.

Corollary bsvar_occur_evar_open dbi1 dbi2 X phi:
bsvar_occur phi dbi1 = false ->
bsvar_occur (phi^{evar: dbi2 ↦ X}) dbi1 = false.
Proof.
apply Private_bsvar_occur_evar_open with (sz := size phi). lia.
Qed.

Lemma Private_bevar_occur_svar_open sz dbi1 dbi2 X phi:
size phi <= sz ->
bevar_occur phi dbi1 = false ->
bevar_occur (phi^{svar: dbi2 ↦ X}) dbi1 = false.
Proof.
move: phi dbi1 dbi2.
induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H; firstorder.
{ cbn. case_match; reflexivity. }
simpl. lia.
Qed.

Corollary bevar_occur_svar_open dbi1 dbi2 X phi:
bevar_occur phi dbi1 = false ->
bevar_occur (phi^{svar: dbi2 ↦ X}) dbi1 = false.
Proof.
apply Private_bevar_occur_svar_open with (sz := size phi). lia.
Qed.

Lemma Private_bevar_occur_evar_open sz dbi1 dbi2 X phi:
size phi <= sz -> dbi1 < dbi2 ->
bevar_occur phi dbi1 = false ->
bevar_occur (phi^{evar: dbi2 ↦ X}) dbi1 = false.
Proof.
move: phi dbi1 dbi2.
induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H H1; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H1; firstorder.
{ cbn. repeat case_match; simpl; auto; try lia.
  { rewrite H0. reflexivity. }
  { case_match; try lia. }
}
simpl. lia.
Qed.

Corollary bevar_occur_evar_open dbi1 dbi2 X phi:
bevar_occur phi dbi1 = false -> dbi1 < dbi2 ->
bevar_occur (phi^{evar: dbi2 ↦ X}) dbi1 = false.
Proof.
intros H H0. apply Private_bevar_occur_evar_open with (sz := size phi); auto.
Qed.

Lemma well_formed_positive_bevar_subst φ : forall n ψ,
mu_free φ ->
well_formed_positive φ = true -> well_formed_positive ψ = true
->
well_formed_positive (φ^[evar: n ↦ ψ]) = true.
Proof.
induction φ; intros n' ψ H H0 H1; simpl; auto.
2-3: apply andb_true_iff in H as [E1 E2];
     simpl in H0; apply eq_sym, andb_true_eq in H0; destruct H0; 
     rewrite -> IHφ1, -> IHφ2; auto.
* break_match_goal; auto.
Qed.

Lemma mu_free_bevar_subst :
forall φ ψ, mu_free φ -> mu_free ψ -> forall n, mu_free (φ^[evar: n ↦ ψ]).
Proof.
induction φ; intros ψ H H0 n'; simpl; try now constructor.
* break_match_goal; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
* simpl in H. now apply IHφ.
* inversion H.
Qed.

Corollary mu_free_evar_open :
forall φ, mu_free φ -> forall x n, mu_free (φ^{evar: n ↦ x}).
Proof.
intros φ H x n. apply mu_free_bevar_subst; auto.
Qed.

Theorem evar_open_free_evar_subst_swap :
forall φ x n ψ y, x <> y -> well_formed ψ ->
  φ^[[evar: y ↦ ψ]]^{evar: n ↦ x} = φ^{evar: n ↦ x}^[[evar: y ↦ ψ]].
Proof.
induction φ; intros x' n' ψ y H H0; simpl; auto.
* destruct (decide (y = x)); simpl.
  ** rewrite evar_open_wfc; auto. unfold well_formed,well_formed_closed in H0. destruct_and!.
     assumption.
  ** reflexivity.
* cbn. break_match_goal; simpl; auto. destruct (decide (y = x')); auto.
  congruence.
* unfold evar_open in *. simpl. now rewrite -> IHφ1, -> IHφ2.
* unfold evar_open in *. simpl. now rewrite -> IHφ1, -> IHφ2.
* unfold evar_open in *. simpl. now rewrite -> IHφ.
* unfold evar_open in *. simpl. now rewrite -> IHφ.
Qed.

Lemma free_evars_free_evar_subst : forall φ ψ x,
free_evars (φ^[[evar: x ↦ ψ]]) ⊆ free_evars φ ∪ free_evars ψ.
Proof.
induction φ; intros ψ x'; simpl.
2-5, 7: apply empty_subseteq.
* destruct (decide (x' = x)); simpl.
  ** apply union_subseteq_r.
  ** apply union_subseteq_l.
* specialize (IHφ1 ψ x'). specialize (IHφ2 ψ x').
  set_solver.
* specialize (IHφ1 ψ x'). specialize (IHφ2 ψ x').
  set_solver.
* apply IHφ.
* apply IHφ.
Qed.


Lemma bound_to_free_variable_subst :
forall φ x m n ψ,
  m > n ->
  well_formed_closed_ex_aux ψ 0 ->
  well_formed_closed_ex_aux φ m -> x ∉ free_evars φ ->
  φ^[evar: n ↦ ψ] = φ^{evar: n ↦ x}^[[evar: x ↦ ψ]].
Proof.
induction φ; intros x' m n' ψ H WFψ H0 H1; cbn; auto.
- destruct (decide (x' = x)); simpl.
  + simpl in H1. apply not_elem_of_singleton_1 in H1. congruence.
  + reflexivity.
- case_match; auto. simpl. case_match; auto; simpl in H0; case_match; auto.
  contradiction. lia.
- simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
  apply andb_true_iff in H0. destruct H0.
  erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
- simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
  apply andb_true_iff in H0. destruct H0.
  erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
- simpl in H0, H1. erewrite IHφ. reflexivity. instantiate (1 := S m). 
  all: try eassumption. lia.
- simpl in H0, H1. erewrite IHφ. reflexivity. all: eassumption.
Qed.

Lemma bound_to_free_set_variable_subst :
forall φ X m n ψ,
  m > n ->
  well_formed_closed_mu_aux ψ 0 ->
  well_formed_closed_mu_aux φ m -> X ∉ free_svars φ ->
  φ^[svar: n ↦ ψ] = φ^{svar: n ↦ X}^[[svar: X ↦ ψ]].
Proof.
induction φ; intros x' m n' ψ H WFψ H0 H1; cbn; auto.
- destruct (decide (x' = x)); simpl.
  + simpl in H1. apply not_elem_of_singleton_1 in H1. congruence.
  + reflexivity.
- case_match; auto. simpl. case_match; auto; simpl in H0; case_match; auto.
  contradiction. lia.
- simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
  apply andb_true_iff in H0. destruct H0.
  erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
- simpl in H1. apply not_elem_of_union in H1. destruct H1. simpl in H0.
  apply andb_true_iff in H0. destruct H0.
  erewrite -> IHφ1, -> IHφ2. reflexivity. all: eassumption.
- simpl in H0, H1. erewrite IHφ. reflexivity. all: eassumption.
- simpl in H0, H1. erewrite IHφ. reflexivity. instantiate (1 := S m). 
  all: try eassumption. lia.
Qed.

Lemma evar_open_no_negative_occurrence :
forall φ db1 db2 x,
  (no_negative_occurrence_db_b db1 (φ^{evar: db2 ↦ x}) ->
  no_negative_occurrence_db_b db1 φ) /\
  (no_positive_occurrence_db_b db1 (φ^{evar: db2 ↦ x}) ->
  no_positive_occurrence_db_b db1 φ).
Proof.
induction φ; intros db1 db2 x'; simpl; auto.
* split; intros.
  - apply andb_true_iff in H as [E1 E2].
    apply IHφ1 in E1. apply IHφ2 in E2.
    cbn.
    now rewrite -> E1, -> E2.
  - apply andb_true_iff in H as [E1 E2].
    apply IHφ1 in E1. apply IHφ2 in E2.
    cbn.
    now rewrite -> E1, -> E2.
* split; intros.
  - apply andb_true_iff in H as [E1 E2].
    apply IHφ1 in E1. apply IHφ2 in E2.
    cbn.
    now rewrite -> E1, -> E2.
  - apply andb_true_iff in H as [E1 E2].
    apply IHφ1 in E1. apply IHφ2 in E2.
    cbn. now rewrite -> E1, -> E2.
* cbn. split; intros; eapply IHφ; eassumption.
* cbn. split; intros; eapply IHφ; eassumption.
Qed.

Lemma evar_open_positive : forall φ n x,
well_formed_positive (φ^{evar: n ↦ x}) = true ->
well_formed_positive φ = true.
Proof.
induction φ; intros n' x' H; cbn; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2].
  erewrite -> IHφ1, -> IHφ2; eauto.
* simpl in H. apply andb_true_iff in H as [E1 E2].
  erewrite -> IHφ1, -> IHφ2; eauto.
* simpl in H. eapply IHφ; eauto.
* simpl in H. apply andb_true_iff in H as [E1 E2].
  apply andb_true_iff. split.
  eapply evar_open_no_negative_occurrence. eassumption.
  eapply IHφ; eauto.
Qed.

Lemma bevar_subst_closed_mu :
forall φ ψ n m,
well_formed_closed_mu_aux φ m = true ->
well_formed_closed_mu_aux ψ m = true
->
well_formed_closed_mu_aux (φ^[evar: n ↦ ψ]) m = true.
Proof.
induction φ; intros ψ n' m H H0; cbn; auto.
* break_match_goal; simpl in H0, H; simpl; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
* simpl in H. rewrite -> IHφ; auto. eapply well_formed_closed_mu_aux_ind.
  2: eassumption. lia.
Qed.

Lemma bevar_subst_closed_ex :
forall φ ψ n,
well_formed_closed_ex_aux φ (S n) = true ->
well_formed_closed_ex_aux ψ n = true
->
well_formed_closed_ex_aux (φ^[evar: n ↦ ψ]) n = true.
Proof.
induction φ; intros ψ n' H H0; cbn; auto.
* break_match_goal; simpl in H0, H; simpl; auto.
  repeat case_match; auto. do 2 case_match; auto; lia.
* simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2]. erewrite IHφ1, IHφ2; auto.
* simpl in H. rewrite -> IHφ; auto. eapply well_formed_closed_ex_aux_ind.
  2: eassumption. lia.
Qed.

Lemma bevar_subst_positive :
forall φ ψ n, mu_free φ ->
well_formed_positive φ = true -> well_formed_positive ψ = true
->
well_formed_positive (φ^[evar: n ↦ ψ]) = true.
Proof.
induction φ; intros ψ n' H H0 H1; cbn; auto.
* break_match_goal; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2].
  apply andb_true_iff in H0 as [E1' E2'].
  rewrite -> IHφ1, -> IHφ2; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2].
  apply andb_true_iff in H0 as [E1' E2'].
  now rewrite -> IHφ1, -> IHφ2.
Qed.

Theorem evar_quantify_closed_ex :
forall φ x n, well_formed_closed_ex_aux φ n ->
well_formed_closed_ex_aux (φ^{{evar: x ↦ n}}) (S n) = true.
Proof.
induction φ; intros x' n' H; cbn; auto.
* destruct (decide (x' = x)); simpl; auto.
  case_match; try lia.
* simpl in H. repeat case_match; auto; lia.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2. 
Qed.

Theorem svar_quantify_closed_mu :
forall φ X n, well_formed_closed_mu_aux φ n ->
well_formed_closed_mu_aux (φ^{{svar: X ↦ n}}) (S n) = true.
Proof.
induction φ; intros x' n' H; cbn; auto.
* destruct (decide (x' = x)); simpl; auto.
  case_match; try lia.
* simpl in H. repeat case_match; auto; lia.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2. 
Qed.

Theorem evar_quantify_closed_mu :
forall φ x n m, well_formed_closed_mu_aux φ m ->
well_formed_closed_mu_aux (φ^{{evar: x ↦ n}}) m = true.
Proof.
induction φ; intros x' n' m H; cbn; auto.
- destruct (decide (x' = x)); simpl; auto.
- simpl in H. repeat case_match; auto.
  destruct_and!. split_and!.
  + apply IHφ1. assumption.
  + apply IHφ2. assumption.
- simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
Qed.

Theorem svar_quantify_closed_ex :
forall φ X n m, well_formed_closed_ex_aux φ m ->
well_formed_closed_ex_aux (φ^{{svar: X ↦ n}}) m = true.
Proof.
induction φ; intros x' n' m H; cbn; auto.
- destruct (decide (x' = x)); simpl; auto.
- simpl in H. repeat case_match; auto.
  destruct_and!. split_and!.
  + apply IHφ1. assumption.
  + apply IHφ2. assumption.
- simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
Qed.

Theorem no_occ_quantify : 
∀ (φ : Pattern) (db1 db2 : db_index) (x : evar),
(no_negative_occurrence_db_b db1 φ
 → no_negative_occurrence_db_b db1 (φ^{{evar: x ↦ db2}}))
∧ (no_positive_occurrence_db_b db1 φ
   → no_positive_occurrence_db_b db1 (φ^{{evar: x ↦ db2}})).
Proof.
induction φ; split; intros H; cbn; auto.
1-2: destruct (decide (x0 = x)); simpl; auto.
1-4: simpl in H; apply andb_true_iff in H as [E1 E2];
     specialize (IHφ1 db1 db2 x) as [IH1 IH2];
     specialize (IHφ2 db1 db2 x) as [IH1' IH2'];
     try rewrite -> IH1; try rewrite -> IH1'; 
     try rewrite -> IH2; try rewrite -> IH2'; auto.
1-4: simpl in H; now apply IHφ.
Qed.


Theorem evar_quantify_positive :
forall φ x n, well_formed_positive φ ->
well_formed_positive (φ^{{evar: x ↦ n}}) = true.
Proof.
induction φ; intros x' n' H; cbn; auto.
* destruct (decide (x' = x)); simpl; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
* simpl in H. apply andb_true_iff in H as [E1 E2]. apply andb_true_iff. split.
  - now apply no_occ_quantify.
  - now apply IHφ.
Qed.

Corollary evar_quantify_well_formed :
forall φ x, well_formed φ ->
  well_formed (patt_exists (φ^{{evar: x ↦ 0}})) = true.
Proof.
intros φ x H.
unfold well_formed, well_formed_closed in *.
destruct_and!.
split_and!; simpl.
- apply evar_quantify_positive. assumption.
- apply evar_quantify_closed_mu. assumption.
- apply evar_quantify_closed_ex. assumption.
Qed.

Theorem evar_quantify_no_occurrence :
forall φ x n, x ∉ (free_evars (φ^{{evar: x ↦ n}})).
Proof.
induction φ; intros x' n'; simpl.
2-5, 7: apply not_elem_of_empty.
* destruct (decide (x' = x)); simpl.
  - apply not_elem_of_empty.
  - subst. now apply not_elem_of_singleton_2.
* apply not_elem_of_union. split. apply IHφ1. apply IHφ2.
* apply not_elem_of_union. split. apply IHφ1. apply IHφ2.
* apply IHφ.
* apply IHφ.
Qed.

Theorem svar_quantify_not_free :
forall φ X n, X ∉ (free_svars (φ^{{svar: X ↦ n}})).
Proof.
induction φ; intros x' n'; simpl; try set_solver.
case_match; simpl; set_solver.
Qed.

Lemma evar_quantify_not_free_evars :
  forall φ x n,
  x ∉ free_evars φ ->
  φ^{{evar: x ↦ n}} = φ.
Proof.
  induction φ; intros x' n' H; simpl; auto.
  - destruct (decide (x = x')).
    + set_solver.
    + destruct (decide (x' = x)); cbn; auto. set_solver.
  - rewrite IHφ1. set_solver. rewrite IHφ2. set_solver. reflexivity.
  - rewrite IHφ1. set_solver. rewrite IHφ2. set_solver. reflexivity.
  - rewrite IHφ. set_solver. reflexivity.
  - rewrite IHφ. set_solver. reflexivity.
Qed.


Lemma wf_ex_evar_quantify x p:
well_formed p = true ->
well_formed (patt_exists (p^{{evar: x ↦ 0}})) = true.
Proof.
intros Hwf.
unfold well_formed,well_formed_closed in Hwf. simpl in Hwf.
apply andb_prop in Hwf.
destruct Hwf as [Hwfp Hwfc].
simpl in Hwfp.
unfold well_formed,well_formed_closed. simpl.
apply andb_true_intro.
split.
- simpl. apply evar_quantify_positive. apply Hwfp.
- unfold well_formed_closed.
  simpl.
  destruct_and!.
  split_and!.
  + apply evar_quantify_closed_mu. assumption.
  + apply evar_quantify_closed_ex. assumption.
Qed.


Lemma free_evars_evar_quantify x n p:
  free_evars (p^{{evar: x ↦ n}}) = free_evars p ∖ {[x]}.
Proof.
  move: n.
  induction p; intros n'; simpl; try set_solver.
  destruct (decide (x = x0)).
    + subst. simpl. set_solver.
    + simpl. set_solver.
Qed.

Lemma free_svars_svar_quantify X n p:
  free_svars (p^{{svar: X ↦ n}}) = free_svars p ∖ {[X]}.
Proof.
  move: n.
  induction p; intros n'; simpl; try set_solver.
  destruct (decide (X = x)).
    + subst. simpl. set_solver.
    + simpl. set_solver.
Qed.


Lemma no_neg_occ_db_bsvar_subst phi psi dbi1 dbi2:
well_formed_closed_mu_aux psi 0 = true -> dbi1 < dbi2 ->
(no_negative_occurrence_db_b dbi1 phi = true ->
 no_negative_occurrence_db_b dbi1 (phi^[svar: dbi2 ↦ psi]) = true)
/\ (no_positive_occurrence_db_b dbi1 phi = true ->
    no_positive_occurrence_db_b dbi1 (phi^[svar: dbi2 ↦ psi]) = true).
Proof.
intros Hwfcpsi.
move: dbi1 dbi2.

induction phi; intros dbi1 dbi2 H; simpl; auto.
-
  case_match; auto.
  + split; intros H0'.
    * apply wfc_impl_no_neg_occ. apply Hwfcpsi.
    * apply wfc_impl_no_pos_occ. apply Hwfcpsi.
  + split; intros H0'.
    * auto.
    * cbn. repeat case_match. lia. reflexivity.
- specialize (IHphi1 dbi1 dbi2).
  specialize (IHphi2 dbi1 dbi2).
  destruct (IHphi1 H) as [IHphi11 IHphi12].
  destruct (IHphi2 H) as [IHphi21 IHphi22].
  split; intro H0.
  + eapply elimT in H0.
    2: apply andP.
    destruct H0 as [H1 H2].
    specialize (IHphi11 H1).
    specialize (IHphi21 H2).
    cbn.
    rewrite IHphi11 IHphi21. reflexivity.
  + eapply elimT in H0.
    2: apply andP.
    destruct H0 as [H1 H2].
    specialize (IHphi12 H1).
    specialize (IHphi22 H2).
    cbn.
    rewrite IHphi12 IHphi22. reflexivity.
- specialize (IHphi1 dbi1 dbi2).
  specialize (IHphi2 dbi1 dbi2).
  destruct (IHphi1 H) as [IHphi11 IHphi12].
  destruct (IHphi2 H) as [IHphi21 IHphi22].
  split; intro H0.
  + eapply elimT in H0.
    2: apply andP.
    destruct H0 as [H1 H2].
    specialize (IHphi12 H1).
    specialize (IHphi21 H2).
    cbn. fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
    rewrite IHphi12 IHphi21. reflexivity.
  + eapply elimT in H0.
    2: apply andP.
    destruct H0 as [H1 H2].
    specialize (IHphi11 H1).
    specialize (IHphi22 H2).
    cbn. fold no_negative_occurrence_db_b no_positive_occurrence_db_b.
    rewrite IHphi11 IHphi22. reflexivity.
- split; intros H0; apply IHphi; auto; lia.
- apply IHphi. lia.
Qed.


Lemma Private_wfp_bsvar_subst (phi psi : Pattern) (n : nat) :
well_formed_positive psi ->
well_formed_closed_mu_aux psi 0 ->
well_formed_positive phi ->
(
  no_negative_occurrence_db_b n phi ->
  well_formed_positive (phi^[svar: n ↦ psi]) )
/\ (no_positive_occurrence_db_b n phi ->
    forall phi',
      well_formed_positive phi' ->
      well_formed_positive (patt_imp (phi^[svar: n ↦ psi]) phi')
   )
.
Proof.
intros Hwfppsi Hwfcpsi.
move: n.
induction phi; intros n' Hwfpphi; cbn in *; auto.
- split.
  + intros _. case_match; auto.
  + intros H phi' Hwfphi'.
    cbn in *.
    do 2 case_match; auto.
- split.
  + intros Hnoneg.
    apply andb_prop in Hnoneg. destruct Hnoneg as [Hnoneg1 Hnoneg2].
    apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
    
    specialize (IHphi1 n' Hwfpphi1).
    destruct IHphi1 as [IHphi11 IHphi12].
    specialize (IHphi11 Hnoneg1).
    rewrite IHphi11.

    specialize (IHphi2 n' Hwfpphi2).
    destruct IHphi2 as [IHphi21 IHphi22].
    specialize (IHphi21 Hnoneg2).
    rewrite IHphi21.
    auto.
    
  + intros Hnopos.
    apply andb_prop in Hnopos. destruct Hnopos as [Hnopos1 Hnopos2].
    apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
    intros phi' Hwfpphi'.

    specialize (IHphi1 n' Hwfpphi1).
    specialize (IHphi2 n' Hwfpphi2).
    destruct IHphi1 as [IHphi11 IHphi12].
    destruct IHphi2 as [IHphi21 IHphi22].
    rewrite IHphi12. fold no_negative_occurrence_db_b no_positive_occurrence_db_b in *.
    { rewrite Hnopos1. auto. }
    specialize (IHphi22 Hnopos2 phi' Hwfpphi').
    apply andb_prop in IHphi22. destruct IHphi22 as [IHphi221 IHphi222].
    rewrite IHphi221. auto.
    rewrite Hwfpphi'. auto.

- split.
  + intros Hnoposneg.
    apply andb_prop in Hnoposneg. destruct Hnoposneg as [Hnopos1 Hnoneg2].
    apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
    specialize (IHphi1 n' Hwfpphi1).
    specialize (IHphi2 n' Hwfpphi2).
    destruct IHphi1 as [IHphi11 IHphi12].
    destruct IHphi2 as [IHphi21 IHphi22].
    specialize (IHphi12 Hnopos1). clear IHphi11.
    specialize (IHphi21 Hnoneg2). clear IHphi22.
    rewrite IHphi21.

    specialize (IHphi12 patt_bott). simpl in IHphi12.
    assert (Htrue: is_true true).
    { auto. }
    specialize (IHphi12 Htrue).
    rewrite IHphi12.
    auto.
  + intros Hnoposneg phi' Hwfpphi'.
    apply andb_prop in Hnoposneg. destruct Hnoposneg as [Hnopos1 Hnoneg2].
    apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
    specialize (IHphi1 n' Hwfpphi1).
    specialize (IHphi2 n' Hwfpphi2).
    destruct IHphi1 as [IHphi11 IHphi12].
    destruct IHphi2 as [IHphi21 IHphi22].
    specialize (IHphi11 Hnopos1). clear IHphi12.
    specialize (IHphi22 Hnoneg2). clear IHphi21.
    rewrite IHphi11. rewrite IHphi22; auto.
- apply andb_prop in Hwfpphi. destruct Hwfpphi as [Hwfpphi1 Hwfpphi2].
  pose proof (IHphi' := IHphi (S n') Hwfpphi2).
  destruct IHphi' as [IHphi1' IHphi2'].
  assert (H: no_negative_occurrence_db_b 0 (phi^[svar: S n' ↦ psi])).
  { clear IHphi1' IHphi2'.
    apply no_neg_occ_db_bsvar_subst; auto. lia.
  }
  split.
  + intros Hnonegphi.
    specialize (IHphi1' Hnonegphi).
    rewrite IHphi1'.
    rewrite H.
    auto.
  + intros Hnopos phi' Hwfpphi'.
    rewrite H.
    rewrite IHphi2'.
    rewrite Hnopos.
    2: rewrite Hwfpphi'.
    1,2,3: auto.
Qed.

Corollary wfp_bsvar_subst (phi psi : Pattern) :
well_formed_positive (patt_mu phi) ->
well_formed_positive psi ->
well_formed_closed_mu_aux psi 0 ->
well_formed_positive (phi^[svar: 0 ↦ psi]).
Proof.
intros H1 H2 H3.
simpl in H1.
eapply elimT in H1. 2: apply andP.
destruct H1 as [Hnonegphi Hwfpphi].
pose proof (H4 := Private_wfp_bsvar_subst).
specialize (H4 phi psi 0 H2 H3 Hwfpphi).
destruct H4 as [H41 H42].
apply H41.
apply Hnonegphi.
Qed.

Lemma bevar_subst_evar_quantify_free_evar x dbi ϕ:
  well_formed_closed_ex_aux ϕ dbi ->
  (ϕ^{{evar: x ↦ dbi}})^[evar: dbi ↦ patt_free_evar x] = ϕ.
Proof.
  move: dbi.
  induction ϕ; intros dbi Hwf; simpl in *; auto.
  - case_match; simpl;[|reflexivity].
    case_match; simpl; try lia. subst. auto.
  - do 2 case_match; try lia; auto. congruence. congruence.
  - apply andb_true_iff in Hwf.
    destruct_and!.
    rewrite IHϕ1;[assumption|].
    rewrite IHϕ2;[assumption|].
    reflexivity.
  - apply andb_true_iff in Hwf.
    destruct_and!.
    rewrite IHϕ1;[assumption|].
    rewrite IHϕ2;[assumption|].
    reflexivity.
  - rewrite IHϕ;[assumption|reflexivity].
  - rewrite IHϕ;[assumption|reflexivity].
Qed.

Lemma bsvar_subst_svar_quantify_free_svar X dbi ϕ:
  well_formed_closed_mu_aux ϕ dbi ->
  (ϕ^{{svar: X ↦ dbi}})^[svar: dbi ↦ (patt_free_svar X)]  = ϕ.
Proof.
  move: dbi.
  induction ϕ; intros dbi Hwf; simpl in *; auto.
  - case_match; simpl;[|reflexivity].
    case_match; simpl; try lia. subst. auto.
  - do 2 case_match; try lia; auto. congruence. congruence.
  - apply andb_true_iff in Hwf.
    destruct_and!.
    rewrite IHϕ1;[assumption|].
    rewrite IHϕ2;[assumption|].
    reflexivity.
  - apply andb_true_iff in Hwf.
    destruct_and!.
    rewrite IHϕ1;[assumption|].
    rewrite IHϕ2;[assumption|].
    reflexivity.
  - rewrite IHϕ;[assumption|reflexivity].
  - rewrite IHϕ;[assumption|reflexivity].
Qed.



Lemma free_svar_subst_fresh phi psi X:
  svar_is_fresh_in X phi ->
  phi^[[svar: X ↦ psi]] = phi.
Proof.
  intros Hfresh.
  unfold svar_is_fresh_in in Hfresh.
  induction phi; simpl in *; auto.
  - case_match.
    + subst. set_solver.
    + reflexivity.
  - specialize (IHphi1 ltac:(set_solver)).
    specialize (IHphi2 ltac:(set_solver)).
    rewrite IHphi1. rewrite IHphi2.
    reflexivity.
  - specialize (IHphi1 ltac:(set_solver)).
    specialize (IHphi2 ltac:(set_solver)).
    rewrite IHphi1. rewrite IHphi2.
    reflexivity.
  - specialize (IHphi ltac:(assumption)).
    rewrite IHphi.
    reflexivity.
  - specialize (IHphi ltac:(assumption)).
    rewrite IHphi.
    reflexivity.
Qed.


Lemma wfc_mu_free_svar_subst level ϕ ψ X:
  well_formed_closed_mu_aux ϕ level ->
  well_formed_closed_mu_aux ψ level ->
  well_formed_closed_mu_aux (ϕ^[[svar: X ↦ ψ]]) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto with nocore.
  - case_match; [|reflexivity].
    assumption.
  - destruct_and!.
    rewrite IHϕ1; auto with nocore.
    rewrite IHϕ2; auto with nocore.
    reflexivity.
  - destruct_and!.
    rewrite IHϕ1; auto with nocore.
    rewrite IHϕ2; auto with nocore.
    reflexivity.
  - rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hψ. lia.
Qed.

Lemma wfc_ex_free_svar_subst level ϕ ψ X:
  well_formed_closed_ex_aux ϕ level ->
  well_formed_closed_ex_aux ψ level ->
  well_formed_closed_ex_aux (ϕ^[[svar: X ↦ ψ]]) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    assumption.
  - destruct_and!.
    rewrite IHϕ1; auto with nocore.
    rewrite IHϕ2; auto with nocore.
    reflexivity.
  - destruct_and!.
    rewrite IHϕ1; auto with nocore.
    rewrite IHϕ2; auto with nocore.
    reflexivity.
  - rewrite IHϕ; auto. eapply well_formed_closed_ex_aux_ind. 2: exact Hψ. lia.
Qed.

Lemma wfc_ex_free_evar_subst_2 level ϕ ψ x:
  well_formed_closed_ex_aux ϕ level ->
  well_formed_closed_ex_aux ψ level ->
  well_formed_closed_ex_aux (ϕ^[[evar: x ↦ ψ]]) level = true.
Proof.
  intros Hϕ Hψ.
  move: level Hϕ Hψ.
  induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
  - case_match; [|reflexivity].
    repeat case_match; auto.
  - destruct_and!.
    rewrite IHϕ1; auto with nocore.
    rewrite IHϕ2; auto with nocore.
    reflexivity.
  - destruct_and!.
    rewrite IHϕ1; auto with nocore.
    rewrite IHϕ2; auto with nocore.
    reflexivity.
  - rewrite IHϕ; auto. eapply well_formed_closed_ex_aux_ind. 2: exact Hψ. lia.
Qed.

Lemma wfc_mu_free_evar_subst level ϕ ψ x:
well_formed_closed_mu_aux ϕ level ->
well_formed_closed_mu_aux ψ level ->
well_formed_closed_mu_aux (ϕ^[[evar: x ↦ ψ]]) level = true.
Proof.
intros Hϕ Hψ.
move: level Hϕ Hψ.
induction ϕ; intros level Hϕ Hψ; simpl in *; auto.
- case_match; [|reflexivity].
  assumption.
- destruct_and!.
  rewrite IHϕ1; auto with nocore.
  rewrite IHϕ2; auto with nocore.
  reflexivity.
- destruct_and!.
  rewrite IHϕ1; auto with nocore.
  rewrite IHϕ2; auto with nocore.
  reflexivity.
- apply IHϕ; auto.
  eapply well_formed_closed_mu_aux_ind.
  2: eassumption. lia.
Qed.


Lemma wf_evar_open_from_wf_ex x ϕ:
  well_formed (patt_exists ϕ) ->
  well_formed (ϕ^{evar: 0 ↦ x}).
Proof.
  intros H.
  unfold well_formed, well_formed_closed in *.
  destruct_and!. cbn in *. split_and!.
  - apply wfp_evar_open. assumption.
  - apply wfc_mu_aux_body_ex_imp1. assumption.
  - apply wfc_mu_aux_body_ex_imp3. lia. assumption.
Qed.

Lemma evar_open_size' :
  forall (k : db_index) (n : evar) (p : Pattern),
    size' (p^{evar: k ↦ n}) = size' p.
Proof.
  intros k n p. generalize dependent k.
  induction p; intros k; cbn; try reflexivity.
  break_match_goal; reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp (S k)); reflexivity.
  rewrite (IHp k); reflexivity.
Qed.

Lemma svar_open_size' :
  forall (k : db_index) (n : svar) (p : Pattern),
    size' (p^{svar: k ↦ n}) = size' p.
Proof.
  intros k n p. generalize dependent k.
  induction p; intros k; cbn; try reflexivity.
  break_match_goal; reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp k); reflexivity.
  rewrite (IHp (S k)); reflexivity.
Qed.

Definition bcmcloseex
    (l : list (prod db_index evar))
    (ϕ : Pattern) : Pattern
:= fold_left (λ ϕ' p, ϕ'^{evar: p.1 ↦ p.2}) l ϕ.

Lemma bcmcloseex_append (l₁ l₂ : list (prod db_index evar)) (ϕ : Pattern) :
  bcmcloseex (l₁ ++ l₂) ϕ = bcmcloseex l₂ (bcmcloseex l₁ ϕ).
Proof.
  unfold bcmcloseex. rewrite fold_left_app. reflexivity.
Qed.

(*
Lemma bmcloseex_wfcex
  {Σ : Signature}
  (l : list (prod db_index evar))
  (ϕ : Pattern)
  : well_formed_closed_ex_aux ϕ from ->
  (bcmcloseex from l ϕ) = ϕ.
Proof.
  intros H.
  induction l.
  { reflexivity. }
  { simpl. rewrite IHl. by rewrite evar_open_not_occur. }
Qed.
*)
Lemma bcmcloseex_bott
  (l : list (prod db_index evar))
  : bcmcloseex l patt_bott = patt_bott.
Proof.
  induction l.
  { reflexivity. }
  { simpl. rewrite IHl. reflexivity. }
Qed.

Lemma bcmcloseex_sym
  (l : list (prod db_index evar))
  (s : symbols)
  : bcmcloseex l (patt_sym s) = (patt_sym s).
Proof.
  induction l.
  { reflexivity. }
  { simpl. rewrite IHl. reflexivity. }
Qed.

Lemma bcmcloseex_imp
  (l : list (prod db_index evar))
  (p q : Pattern)
  : bcmcloseex l (patt_imp p q) = patt_imp (bcmcloseex l p) (bcmcloseex l q).
Proof.
  move: p q.
  induction l; intros p q.
  { reflexivity. }
  { simpl. unfold evar_open. simpl. rewrite IHl. reflexivity. }
Qed.

Lemma bcmcloseex_app
  (l : list (prod db_index evar))
  (p q : Pattern)
  : bcmcloseex l (patt_app p q) = patt_app (bcmcloseex l p) (bcmcloseex l q).
Proof.
  move: p q.
  induction l; intros p q.
  { reflexivity. }
  { simpl. unfold evar_open. simpl. rewrite IHl. reflexivity. }
Qed.

Lemma bcmcloseex_ex
  (l : list (prod db_index evar))
  (q : Pattern)
  : bcmcloseex l (patt_exists q) = patt_exists (bcmcloseex (map (λ p, (S p.1,p.2)) l) q).
Proof.
  move: q.
  induction l; intros q.
  { reflexivity. }
  { simpl. rewrite IHl. reflexivity. }
Qed.

Lemma bcmcloseex_mu
  (l : list (prod db_index evar))
  (q : Pattern)
  : bcmcloseex l (patt_mu q) = patt_mu (bcmcloseex l q).
Proof.
  move: q.
  induction l; intros q.
  { reflexivity. }
  { simpl. rewrite IHl. reflexivity. }
Qed.

Lemma wfc_ex_aux_S_bevar_subst_fe k ϕ x:
  well_formed_closed_ex_aux ϕ^[evar:k↦patt_free_evar x] k = true ->
  well_formed_closed_ex_aux ϕ (S k) = true.  
Proof.
  intros H. move: k H.
  induction ϕ; intros k H; simpl in *; auto with nocore.
  { repeat case_match; auto; try lia. simpl in H. case_match; lia. }
  { destruct_and!. rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity. }
  { destruct_and!. rewrite IHϕ1;[assumption|]. rewrite IHϕ2;[assumption|]. reflexivity. }
Qed.

Lemma wfc_ex_aux_evar_open_gt dbi x k ϕ:
  k > dbi ->
  well_formed_closed_ex_aux (ϕ^{evar: dbi ↦ x}) k ->
  well_formed_closed_ex_aux ϕ (S k).
Proof.
  unfold evar_open.
  intros H1 H2.
  move: k dbi H1 H2.
  induction ϕ; intros k dbi H1 H2; simpl in *; auto.
  { 
    repeat case_match; simpl; repeat case_match; auto; try lia.
    simpl in H2. case_match; try lia. apply H2.
  }
  {
    destruct_and!.
    rewrite (IHϕ1 k dbi);[assumption|assumption|].
    rewrite (IHϕ2 k dbi);[assumption|assumption|].
    reflexivity.
  }
  {
    destruct_and!.
    rewrite (IHϕ1 k dbi);[assumption|assumption|].
    rewrite (IHϕ2 k dbi);[assumption|assumption|].
    reflexivity.
  }
  {
    rewrite (IHϕ (S k) (S dbi));[lia|assumption|].
    reflexivity.
  }
  {
    eapply IHϕ;[|eassumption]. lia.
  }
Qed.

Lemma wfc_ex_aux_evar_open_lt dbi x k ϕ:
  k < dbi ->
  well_formed_closed_ex_aux (ϕ^{evar: dbi ↦ x}) k = true ->
  well_formed_closed_ex_aux ϕ (S dbi) = true.
Proof.
  intros H1 H2.
  move: k dbi H1 H2.
  induction ϕ; intros k dbi H1 H2; simpl in *; auto.
  {
    unfold evar_open in H2. simpl in H2. repeat case_match; auto; try lia.
    simpl in H2. case_match; lia.
  }
  {
    destruct_and!.
    rewrite (IHϕ1 k dbi);[assumption|assumption|].
    rewrite (IHϕ2 k dbi);[assumption|assumption|].
    reflexivity.
  }
  {
    destruct_and!.
    rewrite (IHϕ1 k dbi);[assumption|assumption|].
    rewrite (IHϕ2 k dbi);[assumption|assumption|].
    reflexivity.
  }
  {
    rewrite (IHϕ (S k) (S dbi));[lia|assumption|].
    reflexivity.
  }
  {
    eapply IHϕ;[|eassumption]. lia.
  }
Qed.

Lemma evar_open_twice_not_occur n x y ϕ:
  bevar_occur ϕ n = false ->
  ϕ^{evar: n ↦ x}^{evar: n ↦ y} = ϕ^{evar: S n ↦ y}^{evar: n ↦ x}.
Proof.
  unfold evar_open.
  move: n.
  induction ϕ; intros n' Hnoc; simpl in *; auto.
  {
    repeat case_match; simpl; auto; try lia; repeat case_match; auto; try congruence; lia.
  }
  {
    apply orb_false_elim in Hnoc.
    destruct_and!.
    rewrite (IHϕ1 n'); [assumption|].
    rewrite (IHϕ2 n'); [assumption|].
    reflexivity.
  }
  {
    apply orb_false_elim in Hnoc.
    destruct_and!.
    rewrite (IHϕ1 n'); [assumption|].
    rewrite (IHϕ2 n'); [assumption|].
    reflexivity.
  }
  {
    rewrite (IHϕ (S n'));[assumption|].
    reflexivity.
  }
  {
    rewrite IHϕ;[assumption|].
    reflexivity.
  }
Qed.

Lemma wfc_ex_aux_bcmcloseex l k ϕ:
  Forall (λ p : nat * evar, p.1 ≤ k) l ->
  well_formed_closed_ex_aux (bcmcloseex l (patt_exists ϕ)) k = true ->
  well_formed_closed_ex_aux (bcmcloseex (map (λ p : nat * evar, (S p.1, p.2)) l) ϕ) (S k) = true.
Proof.
  intros Hk H.
  move: ϕ k Hk H.
  induction l; intros ϕ k Hk H.
  { simpl. simpl in H. apply H. }
  {
    destruct a as [dbi x].
    simpl. simpl in H.
    apply IHl.
    { inversion Hk. subst. assumption. }
    { apply H. }
  }
Qed.

Lemma free_svars_free_evar_subst ϕ x ψ:
  free_svars (ϕ^[[evar: x ↦ ψ]]) ⊆ free_svars ϕ ∪ free_svars ψ.
Proof.
  induction ϕ; simpl; try set_solver.
  {
    case_match.
    {
      subst. set_solver.
    }
    {
      simpl. set_solver.
    }
  }
Qed.


Lemma no_neg_occ_quan_impl_no_neg_occ x n1 n2 ϕ:
no_negative_occurrence_db_b n1 (ϕ^{{evar: x ↦ n2}}) = true ->
no_negative_occurrence_db_b n1 ϕ = true
with no_pos_occ_quan_impl_no_pos_occ x n1 n2 ϕ:
no_positive_occurrence_db_b n1 (ϕ^{{evar: x ↦ n2}}) = true ->
no_positive_occurrence_db_b n1 ϕ = true.
Proof.
- intros H.
  move: n1 n2 H.
  induction ϕ; intros n1 n2 H; simpl in *; auto.
  + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
    destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  + unfold no_negative_occurrence_db_b in *. simpl in *.
    fold no_negative_occurrence_db_b no_positive_occurrence_db_b in *.
    destruct_and!.
    erewrite -> no_pos_occ_quan_impl_no_pos_occ by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
    erewrite -> IHϕ by eassumption.
    reflexivity.
  + unfold no_negative_occurrence_db_b in *. simpl in *. fold no_negative_occurrence_db_b in *.
    erewrite -> IHϕ by eassumption.
    reflexivity.
- intros H.
  move: n1 n2 H.
  induction ϕ; intros n1 n2 H; simpl in *; auto.
  + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
    destruct_and!.
    erewrite -> IHϕ1 by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  + unfold no_positive_occurrence_db_b in *. simpl in *.
    fold no_positive_occurrence_db_b no_negative_occurrence_db_b in *.
    destruct_and!.
    erewrite -> no_neg_occ_quan_impl_no_neg_occ by eassumption.
    erewrite -> IHϕ2 by eassumption.
    reflexivity.
  + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
    erewrite -> IHϕ by eassumption.
    reflexivity.
  + unfold no_positive_occurrence_db_b in *. simpl in *. fold no_positive_occurrence_db_b in *.
    erewrite -> IHϕ by eassumption.
    reflexivity.
Qed.

Lemma wfp_evar_quan_impl_wfp x n ϕ:
 well_formed_positive (ϕ^{{evar: x ↦ n}}) = true ->
 well_formed_positive ϕ.
Proof.
 intros H.
 move: n H.
 induction ϕ; intros n' H; simpl in *; auto.
 - destruct_and!.
   erewrite -> IHϕ1 by eassumption.
   erewrite -> IHϕ2 by eassumption.
   reflexivity.
 - destruct_and!.
   erewrite -> IHϕ1 by eassumption.
   erewrite -> IHϕ2 by eassumption.
   reflexivity.
 - erewrite IHϕ by eassumption.
   reflexivity.
 - simpl.
   destruct_and!.
   erewrite -> IHϕ by eassumption.
   erewrite -> no_neg_occ_quan_impl_no_neg_occ by eassumption.
   reflexivity.
Qed.

Lemma wfp_evar_quan x n ϕ:
 well_formed_positive (ϕ^{{evar: x ↦ n}}) = well_formed_positive ϕ.
Proof.
 destruct (well_formed_positive (ϕ^{{evar: x ↦ n}})) eqn:H1,(well_formed_positive ϕ) eqn:H2;
   try reflexivity.
 {
   apply wfp_evar_quan_impl_wfp in H1.
   congruence.
 }
 {
   apply evar_quantify_positive with (x := x) (n := n) in H2.
   congruence.
 }
Qed.

Lemma wfcmu_evar_quan_impl_wfcmu x n dbi ϕ:
    well_formed_closed_mu_aux (ϕ^{{evar: x ↦ n}}) dbi = true ->
    well_formed_closed_mu_aux ϕ dbi.
  Proof.
    intros H.
    move: n dbi H.
    induction ϕ; intros n' dbi H; simpl in *; auto.
    - destruct_and!.
      erewrite -> IHϕ1 by eassumption.
      erewrite -> IHϕ2 by eassumption.
      reflexivity.
    - destruct_and!.
      erewrite -> IHϕ1 by eassumption.
      erewrite -> IHϕ2 by eassumption.
      reflexivity.
    - erewrite IHϕ by eassumption.
      reflexivity.
    - simpl.
      erewrite -> IHϕ by eassumption.
      reflexivity.
  Qed.



  Lemma wfcmu_evar_quan x n dbi ϕ:
    well_formed_closed_mu_aux (ϕ^{{evar: x ↦ n}}) dbi
    = well_formed_closed_mu_aux ϕ dbi.
  Proof.
    destruct (well_formed_closed_mu_aux (ϕ^{{evar: x ↦ n}}) dbi) eqn:H1,
             (well_formed_closed_mu_aux ϕ dbi) eqn:H2;
    try reflexivity.
  {
    apply wfcmu_evar_quan_impl_wfcmu in H1.
    congruence.
  }
  {
    apply evar_quantify_closed_mu with (x := x) (n := n) in H2.
    congruence.
  }
 Qed.

 Lemma wfcex_evar_quan_impl_wfcex x n dbi ϕ:
 well_formed_closed_ex_aux (ϕ^{{evar: x ↦ n}}) dbi = true ->
 well_formed_closed_ex_aux ϕ dbi.
Proof.
 intros H.
 move: n dbi H.
 induction ϕ; intros n' dbi H; simpl in *; auto.
 - destruct_and!.
   erewrite -> IHϕ1 by eassumption.
   erewrite -> IHϕ2 by eassumption.
   reflexivity.
 - destruct_and!.
   erewrite -> IHϕ1 by eassumption.
   erewrite -> IHϕ2 by eassumption.
   reflexivity.
 - erewrite IHϕ by eassumption.
   reflexivity.
 - simpl.
   erewrite -> IHϕ by eassumption.
   reflexivity.
Qed.


Lemma nno_free_svar_subst dbi ϕ ψ X:
well_formed_closed_mu_aux ψ dbi ->
no_negative_occurrence_db_b dbi (ϕ^[[svar: X ↦ ψ]])
= no_negative_occurrence_db_b dbi ϕ
with npo_free_svar_subst dbi ϕ ψ X:
well_formed_closed_mu_aux ψ dbi ->
no_positive_occurrence_db_b dbi (ϕ^[[svar: X ↦ ψ]])
= no_positive_occurrence_db_b dbi ϕ.
Proof.
- move: dbi.
  induction ϕ; intros dbi Hwf; simpl; auto.
  + case_match; cbn; [|reflexivity].
    eapply Private_wfc_impl_no_neg_pos_occ. exact Hwf. lia.
  + cbn. rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  + cbn.
    fold (no_positive_occurrence_db_b).
    rewrite nno_free_svar_subst; auto.
    rewrite npo_free_svar_subst; auto.
  + cbn.
    rewrite IHϕ; auto.
  + cbn.
    rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hwf. lia.
- move: dbi.
  induction ϕ; intros dbi Hwf; simpl; auto.
  + case_match; cbn; [|reflexivity].
    eapply Private_wfc_impl_no_neg_pos_occ. exact Hwf. lia.
  + cbn. rewrite IHϕ1; auto. rewrite IHϕ2; auto.
  + cbn.
    fold (no_negative_occurrence_db_b).
    rewrite nno_free_svar_subst; auto.
    rewrite IHϕ2; auto.
  + cbn.
    rewrite IHϕ; auto.
  + cbn.
    rewrite IHϕ; auto. eapply well_formed_closed_mu_aux_ind. 2: exact Hwf. lia.
Qed.

Lemma wfp_free_svar_subst_1 ϕ ψ X:
well_formed_closed ψ = true ->
well_formed_positive ψ = true ->
well_formed_positive ϕ = true ->
well_formed_positive (ϕ^[[svar: X ↦ ψ]]) = true.
Proof.
intros wfcψ wfpψ wfpϕ.
induction ϕ; simpl; auto.
- case_match; auto.
- simpl in wfpϕ. destruct_and!.
  rewrite -> IHϕ1 by assumption.
  rewrite -> IHϕ2 by assumption.
  reflexivity.
- simpl in wfpϕ. destruct_and!.
  rewrite -> IHϕ1 by assumption.
  rewrite -> IHϕ2 by assumption.
  reflexivity.
- simpl in wfpϕ. destruct_and!.
  specialize (IHϕ H0).
  rewrite -> IHϕ.
  rewrite nno_free_svar_subst.
  { apply andb_true_iff in wfcψ. apply wfcψ. }
  rewrite H.
  reflexivity.
Qed.

Lemma Private_no_negative_occurrence_svar_quantify ϕ level X:
    (
      no_negative_occurrence_db_b level ϕ = true ->
      svar_has_negative_occurrence X ϕ = false ->
      no_negative_occurrence_db_b level (ϕ^{{svar: X ↦ level}}) = true
    )
    /\
    (
      no_positive_occurrence_db_b level ϕ = true ->
      svar_has_positive_occurrence X ϕ = false ->
      no_positive_occurrence_db_b level (ϕ^{{svar: X ↦ level}}) = true
    ).
  Proof.
    move: level.
    induction ϕ; intros level; split; intros HnoX Hnolevel; cbn in *; auto.
    - case_match; reflexivity.
    - case_match; cbn. 2: reflexivity. congruence.
    - apply orb_false_iff in Hnolevel. destruct_and!.
      pose proof (IH1 := IHϕ1 level).
      destruct IH1 as [IH11 _].
      specialize (IH11 ltac:(assumption) ltac:(assumption)).
      pose proof (IH2 := IHϕ2 level).
      destruct IH2 as [IH21 _].
      specialize (IH21 ltac:(assumption) ltac:(assumption)).
      split_and!; assumption.
    - apply orb_false_iff in Hnolevel. destruct_and!.
      pose proof (IH1 := IHϕ1 level).
      destruct IH1 as [_ IH12].
      specialize (IH12 ltac:(assumption) ltac:(assumption)).
      pose proof (IH2 := IHϕ2 level).
      destruct IH2 as [_ IH22].
      specialize (IH22 ltac:(assumption) ltac:(assumption)).
      split_and!; assumption.
    - apply orb_false_iff in Hnolevel. destruct_and!.
      pose proof (IH1 := IHϕ1 level).
      destruct IH1 as [_ IH12].
      specialize (IH12 ltac:(assumption) ltac:(assumption)).
      pose proof (IH2 := IHϕ2 level).
      destruct IH2 as [IH21 _].
      specialize (IH21 ltac:(assumption) ltac:(assumption)).
      split_and!; assumption.
    - apply orb_false_iff in Hnolevel. destruct_and!.
      pose proof (IH1 := IHϕ1 level).
      destruct IH1 as [IH11 _].
      specialize (IH11 ltac:(assumption) ltac:(assumption)).
      pose proof (IH2 := IHϕ2 level).
      destruct IH2 as [_ IH22].
      specialize (IH22 ltac:(assumption) ltac:(assumption)).
      split_and!; assumption.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
  Qed.

  Lemma no_negative_occurrence_svar_quantify ϕ level X:
    no_negative_occurrence_db_b level ϕ = true ->
    svar_has_negative_occurrence X ϕ = false ->
    no_negative_occurrence_db_b level (ϕ^{{svar: X ↦ level}}) = true.
  Proof.
    intros H1 H2.
    pose proof (Htmp :=Private_no_negative_occurrence_svar_quantify ϕ level X).
    destruct Htmp as [Htmp1 Htmp2].
    auto.
  Qed.

  Lemma no_positive_occurrence_svar_quantify ϕ level X:
      no_positive_occurrence_db_b level ϕ = true ->
      svar_has_positive_occurrence X ϕ = false ->
      no_positive_occurrence_db_b level (ϕ^{{svar: X ↦ level}}) = true.
  Proof.
    intros H1 H2.
    pose proof (Htmp :=Private_no_negative_occurrence_svar_quantify ϕ level X).
    destruct Htmp as [Htmp1 Htmp2].
    auto.
  Qed.


  Lemma no_negative_occurrence_svar_quantify_2 X dbi1 dbi2 ϕ:
    dbi1 <> dbi2 ->
    no_negative_occurrence_db_b dbi1 (ϕ^{{svar: X ↦ dbi2}}) = no_negative_occurrence_db_b dbi1 ϕ
  with no_positive_occurrence_svar_quantify_2  X dbi1 dbi2 ϕ:
    dbi1 <> dbi2 ->
    no_positive_occurrence_db_b dbi1 (ϕ^{{svar: X ↦ dbi2}}) = no_positive_occurrence_db_b dbi1 ϕ.
  Proof.
    - move: dbi1 dbi2.
      induction ϕ; intros dbi1 dbi2 Hdbi; simpl; auto.
      + case_match; reflexivity.
      + cbn. rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
      + unfold no_negative_occurrence_db_b at 1.
        fold (no_positive_occurrence_db_b dbi1 (ϕ1^{{svar: X ↦ dbi2}})).
        fold (no_negative_occurrence_db_b dbi1 (ϕ2^{{svar: X ↦ dbi2}})).
        rewrite no_positive_occurrence_svar_quantify_2. lia. rewrite IHϕ2. lia. reflexivity.
      + cbn. rewrite IHϕ. lia. reflexivity.
      + cbn. rewrite IHϕ. lia. reflexivity.
    - move: dbi1 dbi2.
      induction ϕ; intros dbi1 dbi2 Hdbi; simpl; auto.
      + case_match; cbn. 2: reflexivity. case_match; congruence.
      + cbn. rewrite IHϕ1. lia. rewrite IHϕ2. lia. reflexivity.
      + unfold no_positive_occurrence_db_b at 1.
        fold (no_negative_occurrence_db_b dbi1 (ϕ1^{{svar: X ↦ dbi2}})).
        fold (no_positive_occurrence_db_b dbi1 (ϕ2^{{svar: X ↦ dbi2}})).
        rewrite no_negative_occurrence_svar_quantify_2. lia. rewrite IHϕ2. lia. reflexivity.
      + cbn. rewrite IHϕ. lia. reflexivity.
      + cbn. rewrite IHϕ. lia. reflexivity.
  Qed.

  Lemma well_formed_positive_svar_quantify X dbi ϕ:
    well_formed_positive ϕ ->
    well_formed_positive (ϕ^{{svar: X ↦ dbi}}) = true.
  Proof.
    intros Hϕ.
    move: dbi.
    induction ϕ; intros dbi; simpl; auto.
    - case_match; reflexivity.
    - simpl in Hϕ.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption)).
      rewrite IHϕ1. rewrite IHϕ2.
      reflexivity.
    - simpl in Hϕ.
      destruct_and!.
      specialize (IHϕ1 ltac:(assumption)).
      specialize (IHϕ2 ltac:(assumption)).
      rewrite IHϕ1. rewrite IHϕ2.
      reflexivity.
    - simpl in Hϕ.
      destruct_and!.
      specialize (IHϕ ltac:(assumption)).
      rewrite IHϕ.
      rewrite no_negative_occurrence_svar_quantify_2. lia.
      split_and!; auto.
  Qed.

  Lemma free_evar_subst_free_evar_subst φ ψ η x n :
    well_formed_closed_ex_aux ψ n ->
    x ∉ free_evars η ->
    φ^[[evar:x ↦ ψ]]^[evar:n ↦ η] =
    φ^[evar:n ↦ η]^[[evar:x ↦ ψ]].
  Proof.
    generalize dependent n.
    induction φ; intros; simpl; auto.
    * case_match. now rewrite bevar_subst_not_occur.
      now simpl.
    * case_match; simpl; auto.
      now rewrite free_evar_subst_no_occurrence.
    * erewrite IHφ1, IHφ2. reflexivity. all: auto.
    * erewrite IHφ1, IHφ2. reflexivity. all: auto.
    * erewrite IHφ; auto.
      eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
    * erewrite IHφ; auto.
  Defined.

  Lemma subst_svar_evar_svar ϕ x ψ n :
    x ∉ free_evars ϕ ->
    ϕ^[svar:n↦patt_free_evar x]^[[evar:x↦ψ]] = ϕ^[svar:n↦ψ].
  Proof.
    intro H.
    generalize dependent n.
    induction ϕ; try reflexivity; intro n'.
    + cbn. destruct (decide (x = x0)).
      - set_solver.
      - reflexivity.
    + simpl. destruct compare_nat.
      - reflexivity.
      - simpl. destruct decide.
        * reflexivity.
        * congruence.
      - reflexivity.
    + simpl in *. rewrite IHϕ1. 2: rewrite IHϕ2. 1-2: set_solver. reflexivity.
    + simpl in *. rewrite IHϕ1. 2: rewrite IHϕ2. 1-2: set_solver. reflexivity.
    + simpl in *. rewrite IHϕ. set_solver. reflexivity.
    + simpl in *. rewrite IHϕ. set_solver. reflexivity.
  Defined.

  Lemma no_neg_svar_subst ϕ x n :
    x ∉ free_evars ϕ ->
    no_negative_occurrence_db_b n ϕ = true ->
    ~~evar_has_negative_occurrence x ϕ^[svar:n↦patt_free_evar x]
    with
    no_pos_svar_subst ϕ x n :
    x ∉ free_evars ϕ ->
    no_positive_occurrence_db_b n ϕ = true ->
    ~~evar_has_positive_occurrence x ϕ^[svar:n↦patt_free_evar x].
  Proof.
    {
      clear no_neg_svar_subst.
      generalize dependent n.
      induction ϕ; intros n' H0 H; simpl in *; auto.
      * case_match; auto.
      * cbn. cbn in H.
        rewrite negb_orb. unfold is_true in *.
        rewrite IHϕ1; auto with nocore. 1: clear -H0; set_solver.
        2: rewrite IHϕ2; auto. 2: clear -H0; set_solver.
        all: clear -H; apply andb_true_iff in H; apply H.
      * cbn. fold evar_has_positive_occurrence.
        cbn in H. fold no_positive_occurrence_db_b in H.
        destruct_and! H.
        rewrite negb_orb. unfold is_true in *.
        rewrite IHϕ2; auto. clear -H0. set_solver.
        rewrite no_pos_svar_subst; auto. clear -H0. set_solver.
      * cbn in *. now apply IHϕ.
      * cbn in *. now apply IHϕ.
    }
    {
      clear no_pos_svar_subst.
      generalize dependent n.
      induction ϕ; intros n' H0 H; simpl in *; auto.
      * cbn. case_match; auto. set_solver.
      * case_match; auto. cbn in *. subst.
        destruct (decide (n' = n')); congruence.
      * cbn in H.
        rewrite negb_orb. fold evar_has_positive_occurrence.
        unfold is_true in *. destruct_and! H.
        rewrite IHϕ1; auto.
        2: rewrite IHϕ2; auto.
        all: clear -H0; set_solver.
      * cbn. fold evar_has_negative_occurrence.
        cbn in H. fold no_negative_occurrence_db_b in H.
        destruct_and! H.
        rewrite negb_orb. unfold is_true in *.
        rewrite IHϕ2; auto. clear -H0. set_solver.
        rewrite no_neg_svar_subst; auto. clear -H0. set_solver.
      * cbn in *. now apply IHϕ.
      * cbn in *. now apply IHϕ.
    }
  Defined.

End subst.


(*
#[export]
 Hint Resolve wfc_mu_free_svar_subst : core.
#[export]
 Hint Resolve wfc_mu_free_svar_subst : core.
#[export]
 Hint Resolve wfc_ex_free_evar_subst_2 : core.
*)