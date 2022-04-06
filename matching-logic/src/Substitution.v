From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base tactics.

Require Import MatchingLogic.Utils.extralibrary. (* compare_nat *)

From MatchingLogic Require Import
    Pattern.

Section subst.
    Context {Σ : Signature}.

     (* There are two substitution operations over patterns, [bevar_subst] and [bsvar_subst]. *)
  (* substitute bound variable x for psi in phi *)
  Fixpoint bevar_subst (phi psi : Pattern) (x : db_index) :=
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
    | patt_app phi1 phi2 => patt_app (bevar_subst phi1 psi x)
                                     (bevar_subst phi2 psi x)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (bevar_subst phi1 psi x) (bevar_subst phi2 psi x)
    | patt_exists phi' => patt_exists (bevar_subst phi' psi (S x))
    | patt_mu phi' => patt_mu (bevar_subst phi' psi x)
    end.

  Fixpoint bsvar_subst (phi psi : Pattern) (x : db_index) :=
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
    | patt_app phi1 phi2 => patt_app (bsvar_subst phi1 psi x)
                                     (bsvar_subst phi2 psi x)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (bsvar_subst phi1 psi x) (bsvar_subst phi2 psi x)
    | patt_exists phi' => patt_exists (bsvar_subst phi' psi x)
    | patt_mu phi' => patt_mu (bsvar_subst phi' psi (S x))
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
  Fixpoint free_evar_subst (phi psi : Pattern) (x : evar) :=
    match phi with
    | patt_free_evar x' => if decide (x = x') is left _ then psi else patt_free_evar x'
    | patt_free_svar X => patt_free_svar X
    | patt_bound_evar x' => patt_bound_evar x'
    | patt_bound_svar X => patt_bound_svar X
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (free_evar_subst phi1 psi x)
                                     (free_evar_subst phi2 psi x)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (free_evar_subst phi1 psi x) (free_evar_subst phi2 psi x)
    | patt_exists phi' => patt_exists (free_evar_subst phi' psi x)
    | patt_mu phi' => patt_mu (free_evar_subst phi' psi x)
    end.

  (* substitute free set variable X for psi in phi *)
  Fixpoint free_svar_subst (phi psi : Pattern) (X : svar) : Pattern :=
    match phi with
    | patt_free_evar x => patt_free_evar x
    | patt_free_svar X' => if decide (X = X') is left _ then psi else patt_free_svar X'
    | patt_bound_evar x => patt_bound_evar x
    | patt_bound_svar X' => patt_bound_svar X'
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (free_svar_subst phi1 psi X)
                                     (free_svar_subst phi2 psi X)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (free_svar_subst phi1 psi X) (free_svar_subst phi2 psi X)
    | patt_exists phi' => patt_exists (free_svar_subst phi' psi X)
    | patt_mu phi' => patt_mu (free_svar_subst phi' psi X)
    end.

  (* instantiate exists x. p or mu x. p with psi for p *)
  Definition instantiate (phi psi : Pattern) :=
    match phi with
    | patt_exists phi' => bevar_subst phi' psi 0
    | patt_mu phi' => bsvar_subst phi' psi 0
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

  Definition exists_quantify (x : evar)
             (p : Pattern) : Pattern :=
    patt_exists (evar_quantify x 0 p).

  Definition mu_quantify (X : svar)
             (p : Pattern) : Pattern :=
    patt_mu (svar_quantify X 0 p).


  
  (* replace de Bruijn index k with element variable n *)
  Definition evar_open (k : db_index) (x : evar) (p : Pattern) : Pattern :=
    bevar_subst p (patt_free_evar x) k.


  (* replace de Bruijn index k with set variable n *)
  Definition svar_open (k : db_index) (X : svar) (p : Pattern) : Pattern :=
    bsvar_subst p (patt_free_svar X) k.

  Lemma evar_open_free_evar k n x: evar_open k n (patt_free_evar x) = patt_free_evar x.
  Proof. reflexivity. Qed.
  Lemma evar_open_free_svar k n X: evar_open k n (patt_free_svar X) = patt_free_svar X.
  Proof. reflexivity. Qed.
  Lemma evar_open_bound_evar k n x: evar_open k n (patt_bound_evar x) = 
                           match compare_nat x k with
                           | Nat_less _ _ _ => patt_bound_evar x
                           | Nat_equal _ _ _ => patt_free_evar n
                           | Nat_greater _ _ _ => patt_bound_evar (Nat.pred x)
                           end.
  Proof.
    cbn. case_match; done.
  Qed.
  Lemma evar_open_bound_svar k n X: evar_open k n (patt_bound_svar X) = patt_bound_svar X.
  Proof. reflexivity. Qed.
  Lemma evar_open_sym k n s: evar_open k n (patt_sym s) = patt_sym s.
  Proof. reflexivity. Qed.
  Lemma evar_open_app k n ls rs: evar_open k n (patt_app ls rs) = patt_app (evar_open k n ls) (evar_open k n rs).
  Proof. reflexivity. Qed.
  Lemma evar_open_bott k n: evar_open k n patt_bott = patt_bott.
  Proof. reflexivity. Qed.
  Lemma evar_open_imp k n ls rs: evar_open k n (patt_imp ls rs) = patt_imp (evar_open k n ls) (evar_open k n rs).
  Proof. reflexivity. Qed.
  Lemma evar_open_exists k n p': evar_open k n (patt_exists p') = patt_exists (evar_open (S k) n p').
  Proof. reflexivity. Qed.
  Lemma evar_open_mu k n p': evar_open k n (patt_mu p') = patt_mu (evar_open k n p').
  Proof. reflexivity. Qed.

  (* More trivial but useful lemmas *)
  Lemma svar_open_free_evar k n x: svar_open k n (patt_free_evar x) = patt_free_evar x.
  Proof. reflexivity. Qed.
  Lemma svar_open_free_svar k n X: svar_open k n (patt_free_svar X) = patt_free_svar X.
  Proof. reflexivity. Qed.
  Lemma svar_open_bound_evar k n x: svar_open k n (patt_bound_evar x) = patt_bound_evar x.
  Proof. reflexivity. Qed.
  Lemma svar_open_bound_svar k n X: svar_open k n (patt_bound_svar X) = 
                                    match compare_nat X k with
                                    | Nat_less _ _ _ => patt_bound_svar X
                                    | Nat_equal _ _ _ => patt_free_svar n
                                    | Nat_greater _ _ _ => patt_bound_svar (Nat.pred X)
                                    end.
  Proof.
    reflexivity.
  Qed.
  Lemma svar_open_sym k n s: svar_open k n (patt_sym s) = patt_sym s.
  Proof. reflexivity. Qed.
  Lemma svar_open_app k n ls rs: svar_open k n (patt_app ls rs) = patt_app (svar_open k n ls) (svar_open k n rs).
  Proof. reflexivity. Qed.
  Lemma svar_open_bott k n: svar_open k n patt_bott = patt_bott.
  Proof. reflexivity. Qed.
  Lemma svar_open_imp k n ls rs: svar_open k n (patt_imp ls rs) = patt_imp (svar_open k n ls) (svar_open k n rs).
  Proof. reflexivity. Qed.
  Lemma svar_open_exists k n p': svar_open k n (patt_exists p') = patt_exists (svar_open k n p').
  Proof. reflexivity. Qed.
  Lemma svar_open_mu k n p': svar_open k n (patt_mu p') = patt_mu (svar_open (S k) n p').
  Proof. reflexivity. Qed.


  Lemma evar_open_size :
    forall (k : db_index) (n : evar) (p : Pattern),
      size p = size (evar_open k n p).
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
      size p = size (svar_open k n p).
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
   ~ elem_of x (free_evars phi) -> well_formed_closed (evar_open 0 x phi) = true.


   Lemma positive_negative_occurrence_evar_open_and : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
   (*le db1 db2 ->*)
   (no_positive_occurrence_db_b db1 phi -> no_positive_occurrence_db_b db1 (evar_open db2 x phi))
   /\ (no_negative_occurrence_db_b db1 phi -> no_negative_occurrence_db_b db1 (evar_open db2 x phi)).
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
 no_negative_occurrence_db_b db1 (evar_open db2 x phi) = true.
Proof.
 apply positive_negative_occurrence_evar_open_and.
Qed.

Lemma no_positive_occurrence_evar_open phi db1 db2 x:
 no_positive_occurrence_db_b db1 phi = true ->
 no_positive_occurrence_db_b db1 (evar_open db2 x phi) = true.
Proof.
 apply positive_negative_occurrence_evar_open_and.
Qed.


(*Helper lemma for wf_body_to_wf_ex*)
Lemma wfc_ex_aux_body_ex_imp2:
 forall phi n x,
   well_formed_closed_ex_aux (evar_open n x phi) n = true
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
   well_formed_closed_mu_aux (evar_open n x phi) n' = true
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
   well_formed_closed_ex_aux (svar_open n X phi) n' = true
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
   well_formed_closed_mu_aux (svar_open n X phi) n = true
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


  (* The following lemmas are trivial but useful for [rewrite !simpl_evar_open]. *)

  Lemma bevar_subst_free_evar ψ (pf : well_formed_closed ψ) n x :
    bevar_subst (patt_free_evar x) ψ n = patt_free_evar x.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_free_svar ψ (pf : well_formed_closed ψ) n X :
    bevar_subst (patt_free_svar X) ψ n = patt_free_svar X.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_bound_evar ψ (pf : well_formed_closed ψ) n x :
    bevar_subst (patt_bound_evar x) ψ n = match compare_nat x n with
                                          | Nat_less _ _ _ => patt_bound_evar x
                                          | Nat_equal _ _ _ => ψ
                                          | Nat_greater _ _ _ => patt_bound_evar (pred x)
                                          end.
  Proof.
    cbn. case_match; done.
  Qed.

  Lemma bevar_subst_bound_svar ψ (pf : well_formed_closed ψ) n X :
    bevar_subst (patt_bound_svar X) ψ n = patt_bound_svar X.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_sym ψ (pf : well_formed_closed ψ) n s :
    bevar_subst (patt_sym s) ψ n = patt_sym s.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_app ψ (pf : well_formed_closed ψ) n ls rs :
    bevar_subst (patt_app ls rs) ψ n = patt_app (bevar_subst ls ψ n) (bevar_subst rs ψ n).
  Proof. reflexivity. Qed.

  Lemma bevar_subst_bott ψ (pf : well_formed_closed ψ) n:
    bevar_subst patt_bott ψ n = patt_bott.
  Proof. reflexivity. Qed.

  Lemma bevar_subst_imp ψ (pf : well_formed_closed ψ) n ls rs :
    bevar_subst (patt_imp ls rs) ψ n = patt_imp (bevar_subst ls ψ n) (bevar_subst rs ψ n).
  Proof. reflexivity. Qed.

  Lemma bevar_subst_exists ψ (pf : well_formed_closed ψ) n ϕ :
    bevar_subst (patt_exists ϕ) ψ n = patt_exists (bevar_subst ϕ ψ (S n)).
  Proof. reflexivity. Qed.

  Lemma bevar_subst_mu ψ (pf : well_formed_closed ψ) n ϕ :
    bevar_subst (patt_mu ϕ) ψ n = patt_mu (bevar_subst ϕ ψ n).
  Proof. reflexivity. Qed.

  (* More trivial but useful lemmas *)
  Lemma bsvar_subst_free_evar ψ (pf : well_formed_closed ψ) n x :
    bsvar_subst (patt_free_evar x) ψ n = patt_free_evar x.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_free_svar ψ (pf : well_formed_closed ψ) n X :
    bsvar_subst (patt_free_svar X) ψ n = patt_free_svar X.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_bound_evar ψ (pf : well_formed_closed ψ) n x :
    bsvar_subst (patt_bound_evar x) ψ n = patt_bound_evar x.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_bound_svar ψ (pf : well_formed_closed ψ) n X :
    bsvar_subst (patt_bound_svar X) ψ n = match compare_nat X n with
                                          | Nat_less _ _ _ => patt_bound_svar X
                                          | Nat_equal _ _ _ => ψ
                                          | Nat_greater _ _ _ => patt_bound_svar (pred X)
                                          end.
  Proof.
    reflexivity.
  Qed.

  Lemma bsvar_subst_sym ψ (pf : well_formed_closed ψ) n s :
    bsvar_subst (patt_sym s) ψ n = patt_sym s.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_app ψ (pf : well_formed_closed ψ) n ls rs :
    bsvar_subst (patt_app ls rs) ψ n = patt_app (bsvar_subst ls ψ n) (bsvar_subst rs ψ n).
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_bott ψ (pf : well_formed_closed ψ) n :
    bsvar_subst patt_bott ψ n = patt_bott.
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_imp ψ (pf : well_formed_closed ψ) n ls rs:
    bsvar_subst (patt_imp ls rs) ψ n = patt_imp (bsvar_subst ls ψ n) (bsvar_subst rs ψ n).
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_exists ψ (pf : well_formed_closed ψ) n ϕ :
    bsvar_subst (patt_exists ϕ) ψ n = patt_exists (bsvar_subst ϕ ψ n).
  Proof. reflexivity. Qed.

  Lemma bsvar_subst_mu ψ (pf : well_formed_closed ψ) n ϕ :
    bsvar_subst (patt_mu ϕ) ψ n = patt_mu (bsvar_subst ϕ ψ (S n)).
  Proof. reflexivity. Qed.


End subst.

Module Notations.

Notation "e .[ 'evar:' dbi ↦ e' ]" := (bevar_subst e e' dbi) (at level 2, e' at level 200, left associativity,
format "e .[ 'evar:' dbi ↦ e' ]" ).
Notation "e .[ 'svar:' dbi ↦ e' ]" := (bsvar_subst e e' dbi) (at level 2, e' at level 200, left associativity,
format "e .[ 'svar:' dbi ↦ e' ]" ).
Notation "e .[[ 'evar:' x ↦ e' ]]" := (free_evar_subst e e' x) (at level 2, e' at level 200, left associativity,
format "e .[[ 'evar:' x ↦ e' ]]" ).
Notation "e .[[ 'svar:' X ↦ e' ]]" := (free_svar_subst e e' X) (at level 2, e' at level 200, left associativity,
format "e .[[ 'svar:' X ↦ e' ]]" ).
Notation "e . [ e' ]" := (instantiate e e') (at level 2, e' at level 200, left associativity).

End Notations.