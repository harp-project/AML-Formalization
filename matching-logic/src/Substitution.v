From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base tactics sets.

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

Import Notations.

Section subst.
    Context {Σ : Signature}.


Lemma wfc_ex_aux_bevar_subst :
forall phi psi n,
  well_formed_closed_ex_aux phi (S n) = true
  -> well_formed_closed_ex_aux psi n = true
  -> well_formed_closed_ex_aux (bevar_subst phi psi n) n = true.
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
  -> well_formed_closed_mu_aux (bevar_subst phi psi n) n' = true.
Proof.
intros phi psi n n' H H0. 
generalize dependent n. generalize dependent n'. generalize dependent psi.
induction phi; intros psi n' H n'' H0; try lia; auto.
- simpl in *. unfold well_formed_closed_mu_aux. repeat case_match; simpl; auto.
- simpl. simpl in H.
  rewrite IHphi1; auto. 2: rewrite IHphi2; auto. all: destruct_and!; auto.
- simpl. simpl in H. destruct_and!.
  rewrite IHphi1; auto. rewrite IHphi2; auto.
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
  -> well_formed_closed_ex_aux (bsvar_subst phi psi n') n = true.
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
  -> well_formed_closed_mu_aux (bsvar_subst phi psi n') n' = true.
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
  well_formed_closed_ex_aux (evar_open n x phi) n = true.
Proof using .
intros. apply wfc_ex_aux_bevar_subst; auto.
Qed.

Corollary wfc_mu_aux_body_ex_imp1:
forall phi n n' x,
  well_formed_closed_mu_aux phi n' = true
  ->
  well_formed_closed_mu_aux (evar_open n x phi) n' = true.
Proof using .
intros. now apply wfc_mu_aux_bevar_subst.
Qed.

Corollary wfc_ex_aux_body_mu_imp1:
forall phi n n' X,
  well_formed_closed_ex_aux phi n' = true
  ->
  well_formed_closed_ex_aux (svar_open n X phi) n' = true.
Proof using .
intros. now apply wfc_ex_aux_bsvar_subst.
Qed.

Corollary wfc_mu_aux_body_mu_imp1:
forall phi n X,
  well_formed_closed_mu_aux phi (S n) = true
  ->
  well_formed_closed_mu_aux (svar_open n X phi) n = true.
Proof using .
intros. now apply wfc_mu_aux_bsvar_subst.
Qed.

Lemma wfc_mu_aux_bsvar_subst_le :
forall phi psi n n', n' <= n ->
  well_formed_closed_mu_aux phi (S n) = true ->
  well_formed_closed_mu_aux psi n
  ->
  well_formed_closed_mu_aux (phi.[svar:n' ↦ psi]) n = true.
Proof using .
induction phi; intros psi n0 n' H Hwf1 Hwf2; try lia; auto.
- simpl. case_match; auto. simpl. case_match; try lia.
  simpl in Hwf1. case_match; try lia. simpl. case_match; lia.
- simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
  rewrite (IHphi1 _ _ n'); auto. rewrite (IHphi2 _ _ n'); auto.
- simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
  rewrite (IHphi1 _ _ n'); auto. rewrite (IHphi2 _ _ n'); auto.
- simpl. simpl in Hwf1. rewrite (IHphi _ _ n'); auto.
- simpl. simpl in Hwf1. rewrite (IHphi _ _ (S n')); auto. lia.
  eapply well_formed_closed_mu_aux_ind. 2: eassumption. lia.
Qed.

Lemma wfc_ex_aux_bsvar_subst_le:
forall phi psi n n', n' <= n ->
  well_formed_closed_ex_aux phi (S n) = true ->
  well_formed_closed_ex_aux psi n = true
  ->
  well_formed_closed_ex_aux (phi.[evar:n'↦psi]) n = true.
Proof using .
induction phi; intros psi n0 n' H Hwf1 Hwf2; try lia; auto.
- simpl. case_match; auto. simpl. case_match; try lia.
  simpl in Hwf1. case_match; try lia. simpl. case_match; lia.
- simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
  rewrite (IHphi1 _ _ n'); auto. rewrite (IHphi2 _ _ n'); auto.
- simpl. simpl in H. simpl in Hwf1. apply andb_true_iff in Hwf1 as [H1 H2].
  rewrite (IHphi1 _ _ n'); auto. rewrite (IHphi2 _ _ n'); auto.
- simpl. simpl in Hwf1. rewrite (IHphi _ _ (S n')); auto. lia.
  eapply well_formed_closed_ex_aux_ind. 2: eassumption. lia.
- simpl. simpl in Hwf1. rewrite (IHphi _ _ n'); auto.
Qed.

Corollary wfc_mu_aux_body_mu_imp3:
forall phi n n' X, n' <= n ->
  well_formed_closed_mu_aux phi (S n) = true
  ->
  well_formed_closed_mu_aux (svar_open n' X phi) n = true.
Proof using .
intros. now apply wfc_mu_aux_bsvar_subst_le.
Qed.

Corollary wfc_mu_aux_body_ex_imp3:
forall phi n n' X, n' <= n ->
  well_formed_closed_ex_aux phi (S n) = true
  ->
  well_formed_closed_ex_aux (evar_open n' X phi) n = true.
Proof using .
intros. now apply wfc_ex_aux_bsvar_subst_le.
Qed.

Corollary wfc_ex_aux_body_iff: 
forall phi n x,
  well_formed_closed_ex_aux phi (S n) = true
  <->
  well_formed_closed_ex_aux (evar_open n x phi) n = true.
Proof.
split.
apply wfc_ex_aux_body_ex_imp1.
apply wfc_ex_aux_body_ex_imp2.
Qed.

Corollary wfc_mu_aux_body_iff: 
forall phi n X,
  well_formed_closed_mu_aux phi (S n) = true
  <->
  well_formed_closed_mu_aux (svar_open n X phi) n = true.
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
no_negative_occurrence_db_b dbi1 (bevar_subst phi psi dbi2) = true
with no_pos_occ_db_bevar_subst  phi psi dbi1 dbi2:
   well_formed_closed_mu_aux psi 0 = true ->
   no_positive_occurrence_db_b dbi1 phi = true ->
   no_positive_occurrence_db_b dbi1 (bevar_subst phi psi dbi2) = true.
Proof.
- move: dbi1 dbi2.
induction phi; intros dbi1 dbi2 Hwfcpsi Hnonegphi; cbn in *; auto.
+ case_match; auto. now apply wfc_impl_no_neg_occ.
+ destruct_and!.
rewrite -> IHphi1, -> IHphi2; auto.
+ destruct_and!.
fold (no_positive_occurrence_db_b dbi1 (bevar_subst phi1 psi dbi2)).
rewrite no_pos_occ_db_bevar_subst; auto.
rewrite -> IHphi2; auto.
- move: dbi1 dbi2.
induction phi; intros dbi1 dbi2 Hwfcpsi Hnonegphi; cbn in *; auto.
+ repeat case_match; auto.
apply wfc_impl_no_pos_occ. assumption.
+ destruct_and!.
rewrite -> IHphi1, -> IHphi2; auto.
+ destruct_and!.
fold (no_negative_occurrence_db_b dbi1 (bevar_subst phi1 psi dbi2)).
rewrite no_neg_occ_db_bevar_subst; auto.
rewrite -> IHphi2; auto.
Qed.

Lemma bevar_subst_positive_2 :
forall φ ψ n,
well_formed_closed_mu_aux ψ 0 = true ->
well_formed_positive φ = true ->
well_formed_positive ψ = true ->
well_formed_positive (bevar_subst φ ψ n) = true.
Proof.
induction φ; intros ψ n' H0 H1 H2; cbn in *; auto.
* break_match_goal; auto.
* destruct_and!. rewrite -> IHφ1, -> IHφ2; auto.
* destruct_and!. rewrite -> IHφ1, -> IHφ2; auto.
* destruct_and!.
rewrite IHφ; auto.
rewrite no_neg_occ_db_bevar_subst; auto.
Qed.

Corollary wfp_evar_open : forall phi x n,
well_formed_positive phi = true ->
well_formed_positive (evar_open n x phi) = true.
Proof.
intros phi x n WF. apply bevar_subst_positive_2; auto.
Qed.

(* Additional lemmas: evar_open, svar_open, freshness, well_formedness, etc. *)

(* evar_open and evar_quantify are inverses *)
Lemma evar_open_evar_quantify x n phi:
well_formed_closed_ex_aux phi n ->
(evar_open n x (evar_quantify x n phi)) = phi.
Proof.
intros H.
(*apply wfc_wfc_ind in H.*)
move: n H.
induction phi; intros n' H; cbn; auto.
- destruct (decide (x = x0)); subst; simpl.
+ break_match_goal; auto; lia.
+ reflexivity.
- simpl in *. repeat case_match; simpl; auto; try lia; congruence.
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
(svar_open n X (svar_quantify X n phi)) = phi.
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
(evar_quantify x n (evar_open n x phi)) = phi.
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
(svar_quantify X n (svar_open n X phi)) = phi.
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
evar_quantify x n (evar_quantify x n φ) = evar_quantify x n φ.
Proof.
induction φ; intros x' n'; simpl; auto.
* unfold evar_quantify. repeat case_match; auto. contradiction.
* now rewrite -> IHφ1, -> IHφ2.
* now rewrite -> IHφ1, -> IHφ2.
* now rewrite IHφ.
* now rewrite IHφ.
Qed.

Lemma double_svar_quantify φ : forall X n,
svar_quantify X n (svar_quantify X n φ) = svar_quantify X n φ.
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
bevar_subst φ ψ m = φ.
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
bsvar_subst φ ψ m = φ.
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
bevar_subst ϕ ψ n = ϕ.
Proof.
intro H. eapply well_formed_bevar_subst; eauto.
Qed.

(* evar_open is identity if n does not occur in phi *)
Corollary evar_open_not_occur n x ϕ :
well_formed_closed_ex_aux ϕ n ->
evar_open n x ϕ = ϕ.
Proof.
apply bevar_subst_not_occur.
Qed.

(* bsvar_subst is identity if n does not occur in phi *)
Corollary bsvar_subst_not_occur n ψ ϕ :
well_formed_closed_mu_aux ϕ n ->
bsvar_subst ϕ ψ n = ϕ.
Proof.
intro H. eapply well_formed_bsvar_subst; eauto.
Qed.

(* evar_open is identity if n does not occur in phi *)
Corollary svar_open_not_occur n x ϕ :
well_formed_closed_mu_aux ϕ n ->
svar_open n x ϕ = ϕ.
Proof.
apply bsvar_subst_not_occur.
Qed.

(* opening on closed patterns is identity *)
Lemma evar_open_closed :
forall phi,
well_formed_closed_ex_aux phi 0 ->
forall n v,
  evar_open n v phi = phi.
Proof.
intros phi H n v. unfold evar_open. erewrite well_formed_bevar_subst. 3: exact H.
auto. lia.
Qed.

Lemma svar_open_closed :
forall phi,
well_formed_closed_mu_aux phi 0 ->
forall n v,
  svar_open n v phi = phi.
Proof. 
intros phi H n v. unfold svar_open. erewrite well_formed_bsvar_subst. 3: exact H.
auto. lia.
Qed.

Lemma bevar_subst_comm_higher :
forall phi psi1 psi2 n m, 
n > m -> well_formed_closed_ex_aux psi1 0 -> well_formed_closed_ex_aux psi2 0 ->
bevar_subst (bevar_subst phi psi1 n) psi2 m = 
bevar_subst (bevar_subst phi psi2 m) psi1 (pred n).
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
bevar_subst (bevar_subst phi psi1 n) psi2 m = 
bevar_subst (bevar_subst phi psi2 (S m)) psi1 n.
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
bsvar_subst (bsvar_subst phi psi1 n) psi2 m = 
bsvar_subst (bsvar_subst phi psi2 m) psi1 (pred n).
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
bsvar_subst (bsvar_subst phi psi1 n) psi2 m = 
bsvar_subst (bsvar_subst phi psi2 (S m)) psi1 n.
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
  evar_open n x (evar_open m y phi) = evar_open (pred m) y (evar_open n x phi).
Proof.
intros n m Hneqnm x y phi. apply bevar_subst_comm_higher; auto.
Qed.

Corollary evar_open_comm_lower:
forall n m,
n > m 
->
forall x y phi,
  evar_open n x (evar_open m y phi) = evar_open m y (evar_open (S n) x phi).
Proof.
intros n m Hneqnm x y phi. apply bevar_subst_comm_lower; auto.
Qed.

Corollary svar_open_comm_higher:
forall n m,
n < m 
->
forall X Y phi,
  svar_open n X (svar_open m Y phi) = svar_open (pred m) Y (svar_open n X phi).
Proof.
intros n m Hneqnm x y phi. apply bsvar_subst_comm_higher; auto.
Qed.

Corollary svar_open_comm_lower:
forall n m,
n > m
->
forall X Y phi,
  svar_open n X (svar_open m Y phi) = svar_open m Y (svar_open (S n) X phi).
Proof.
intros n m Hneqnm x y phi. apply bsvar_subst_comm_lower; auto.
Qed.

Lemma bevar_subst_bsvar_subst phi psi1 psi2 dbi1 dbi2
: well_formed_closed psi1 -> well_formed_closed psi2 ->
bevar_subst (bsvar_subst phi psi1 dbi1) psi2 dbi2
= bsvar_subst (bevar_subst phi psi2 dbi2) psi1 dbi1.
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
evar_open dbi1 x (svar_open dbi2 X phi) = svar_open dbi2 X (evar_open dbi1 x phi).
Proof.
intros phi dbi1 x dbi2 X. apply bevar_subst_bsvar_subst; auto.
Qed.


Lemma free_svars_evar_open : forall (ϕ : Pattern) (dbi :db_index) (x : evar),
free_svars (evar_open dbi x ϕ) = free_svars ϕ.
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
   svar_has_positive_occurrence X (svar_open dbi X phi) = false)
  /\ (no_negative_occurrence_db_b dbi phi ->
      svar_has_negative_occurrence X phi = false ->
      svar_has_negative_occurrence X (svar_open dbi X phi) = false).
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
  (svar_has_positive_occurrence X (evar_open dbi x ϕ) = false <-> svar_has_positive_occurrence X ϕ = false)
  /\ (svar_has_negative_occurrence X (evar_open dbi x ϕ) = false <-> svar_has_negative_occurrence X ϕ = false).
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
  svar_has_positive_occurrence X (evar_open dbi x ϕ) = false <-> svar_has_positive_occurrence X ϕ = false.
Proof.
apply positive_negative_occurrence_evar_open.
Qed.

Corollary negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
  svar_has_negative_occurrence X (evar_open dbi x ϕ) = false <-> svar_has_negative_occurrence X ϕ = false.
Proof.
apply positive_negative_occurrence_evar_open.
Qed.

Lemma positive_negative_occurrence_db_svar_open_le : forall (phi : Pattern) (dbi1 dbi2 : db_index) (X : svar),
  dbi1 < dbi2 ->
  (
    no_positive_occurrence_db_b dbi1 phi ->
    no_positive_occurrence_db_b dbi1 (svar_open dbi2 X phi)
  )
  /\ (no_negative_occurrence_db_b dbi1 phi -> no_negative_occurrence_db_b dbi1 (svar_open dbi2 X phi)).
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
  well_formed_positive (svar_open dbi X phi) = true.
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
    svar_has_negative_occurrence X (svar_open dbi Y phi) = false
  ) /\ (
    svar_has_positive_occurrence X phi = false ->
    svar_has_positive_occurrence X (svar_open dbi Y phi) = false
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
evar_open db2 X phi = phi.
Proof.
intros H H0. unfold evar_open. eapply well_formed_bevar_subst. 2: eassumption. auto.
Qed.

Corollary evar_open_wfc m X phi : well_formed_closed_ex_aux phi 0 -> evar_open m X phi = phi.
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
svar_open db2 X phi = phi.
Proof.
intros H H0. unfold evar_open. eapply well_formed_bsvar_subst. 2: eassumption. auto.
Qed.

Corollary svar_open_wfc m X phi : well_formed_closed_mu_aux phi 0 -> svar_open m X phi = phi.
Proof.
intros H.
unfold well_formed_closed in H.
apply svar_open_wfc_aux with (X := X)(db2 := m) in H.
2: lia.
auto.
Qed.

Corollary evar_open_bsvar_subst m phi1 phi2 dbi X
: well_formed_closed phi2 ->
  evar_open m X (bsvar_subst phi1 phi2 dbi)
  = bsvar_subst (evar_open m X phi1) phi2 dbi.
Proof.
intro H. apply bevar_subst_bsvar_subst; auto.
Qed.

Corollary svar_open_bevar_subst m phi1 phi2 dbi X
: well_formed_closed phi2 ->
  svar_open m X (bevar_subst phi1 phi2 dbi)
  = bevar_subst (svar_open m X phi1) phi2 dbi.
Proof.
intro H. apply eq_sym, bevar_subst_bsvar_subst; auto.
Qed.

Corollary svar_open_bsvar_subst_higher m phi1 phi2 dbi X
: well_formed_closed phi2 ->
  m < dbi ->
  svar_open m X (bsvar_subst phi1 phi2 dbi)
  = bsvar_subst (svar_open m X phi1) phi2 (pred dbi).
Proof.
intros H H0. apply bsvar_subst_comm_higher; auto.
unfold well_formed_closed in *. destruct_and!. auto.
Qed.

Corollary svar_open_bsvar_subst_lower m phi1 phi2 dbi X
: well_formed_closed phi2 ->
  m > dbi ->
  svar_open m X (bsvar_subst phi1 phi2 dbi)
  = bsvar_subst (svar_open (S m) X phi1) phi2 dbi.
Proof.
intros H H0. apply bsvar_subst_comm_lower; auto.
unfold well_formed_closed in *. destruct_and!. auto.
Qed.

Corollary evar_open_bevar_subst_higher m phi1 phi2 dbi X
: well_formed_closed_ex_aux phi2 0 ->
  m < dbi ->
  evar_open m X (bevar_subst phi1 phi2 dbi)
  = bevar_subst (evar_open m X phi1) phi2 (pred dbi).
Proof.
intros H H0. apply bevar_subst_comm_higher; auto.
Qed.

Corollary evar_open_bevar_subst_lower m phi1 phi2 dbi X
: well_formed_closed phi2 ->
  m > dbi ->
  evar_open m X (bevar_subst phi1 phi2 dbi)
  = bevar_subst (evar_open (S m) X phi1) phi2 dbi.
Proof.
intros H H0. apply bevar_subst_comm_lower; auto.
unfold well_formed_closed in *. destruct_and!. auto.
Qed.



Lemma free_svars_bsvar_subst' :
forall φ ψ dbi X,
  (X ∈ free_svars (bsvar_subst φ ψ dbi)) <->
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
- case_match; split; intros H.
  + simpl in H. set_solver.
  + destruct H.
    * destruct H; auto. case_match; auto; subst. lia. congruence.
    * set_solver.
  + left. split; auto. case_match; auto.
  + simpl in H. set_solver.
  + simpl in H. set_solver.
  + destruct H.
    * destruct H. case_match; try lia; congruence.
    * set_solver.
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
  (X ∈ free_evars (bevar_subst φ ψ dbi)) <->
  ((X ∈ (free_evars ψ) /\ bevar_occur φ dbi) \/ (X ∈ (free_evars φ))).
Proof.
induction φ; intros ψ dbi X; simpl.
- split; intros H; auto.
  destruct H.
  destruct H. congruence. assumption.
- split; intros H; auto.
  destruct H; auto.
  destruct H; congruence.
- case_match; split; intros H.
  + simpl in H. set_solver.
  + destruct H.
    * destruct H; auto. case_match; auto; subst. lia. congruence.
    * set_solver.
  + left. split; auto. case_match; auto.
  + simpl in H. set_solver.
  + simpl in H. set_solver.
  + destruct H.
    * destruct H. case_match; try lia; congruence.
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
free_svars (bsvar_subst φ ψ dbi) ⊆ union (free_svars ψ) (free_svars φ).
Proof.
induction φ; intros ψ dbi; simpl; try set_solver.
case_match; simpl; set_solver.
Qed.

Lemma free_evars_bevar_subst :
forall φ ψ dbi,
free_evars (bevar_subst φ ψ dbi) ⊆ union (free_evars ψ) (free_evars φ).
Proof.
induction φ; intros ψ dbi Hwf; simpl; try set_solver.
case_match; simpl; set_solver.
Qed.

Lemma free_svars_svar_open'' :
forall φ dbi X Y,
  (X ∈ free_svars (svar_open dbi Y φ)) <->
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
free_svars (svar_open dbi X ϕ) ⊆ union (singleton X) (free_svars ϕ).
Proof.
apply free_svars_bsvar_subst; auto.
Qed.

Lemma free_evars_evar_open'' :
forall φ dbi x y,
  (x ∈ free_evars (evar_open dbi y φ)) <->
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
free_evars (evar_open dbi x ϕ) ⊆ union (singleton x) (free_evars ϕ).
Proof.
apply free_evars_bevar_subst; auto.
Qed.

Lemma free_evars_evar_open' ϕ x dbi:
free_evars ϕ ⊆ free_evars (evar_open dbi x ϕ).
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
count_evar_occurrences x p = 0 ->
free_evar_subst p q x = p.
Proof.
intros H.
remember (size' p) as sz.
assert (Hsz: size' p <= sz) by lia.
clear Heqsz.

move: p Hsz H.
induction sz; intros p Hsz H; destruct p; simpl in *; try lia; auto.
- simpl in H. simpl.
  destruct (decide (x = x0)).
  + subst x0. destruct (decide (x = x)). simpl in H. inversion H. contradiction.
  + reflexivity.
- rewrite IHsz. lia. lia. rewrite IHsz. lia. lia. reflexivity.
- rewrite IHsz. lia. lia. rewrite IHsz. lia. lia. reflexivity.
- f_equal. rewrite IHsz. lia. exact H. reflexivity.
- rewrite IHsz; auto. lia.
Qed.


Lemma Private_bsvar_occur_evar_open sz dbi1 dbi2 X phi:
size phi <= sz ->
bsvar_occur phi dbi1 = false ->
bsvar_occur (evar_open dbi2 X phi) dbi1 = false.
Proof.
move: phi dbi1 dbi2.
induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H; firstorder.
2: { simpl. lia. }
cbn. case_match; reflexivity.
Qed.

Corollary bsvar_occur_evar_open dbi1 dbi2 X phi:
bsvar_occur phi dbi1 = false ->
bsvar_occur (evar_open dbi2 X phi) dbi1 = false.
Proof.
apply Private_bsvar_occur_evar_open with (sz := size phi). lia.
Qed.

Lemma Private_bevar_occur_svar_open sz dbi1 dbi2 X phi:
size phi <= sz ->
bevar_occur phi dbi1 = false ->
bevar_occur (svar_open dbi2 X phi) dbi1 = false.
Proof.
move: phi dbi1 dbi2.
induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H; firstorder.
{ cbn. case_match; reflexivity. }
simpl. lia.
Qed.

Corollary bevar_occur_svar_open dbi1 dbi2 X phi:
bevar_occur phi dbi1 = false ->
bevar_occur (svar_open dbi2 X phi) dbi1 = false.
Proof.
apply Private_bevar_occur_svar_open with (sz := size phi). lia.
Qed.

Lemma Private_bevar_occur_evar_open sz dbi1 dbi2 X phi:
size phi <= sz -> dbi1 < dbi2 ->
bevar_occur phi dbi1 = false ->
bevar_occur (evar_open dbi2 X phi) dbi1 = false.
Proof.
move: phi dbi1 dbi2.
induction sz; move=> phi; destruct phi; simpl; move=> dbi1 dbi2 Hsz H H1; try rewrite !IHsz; auto; try lia; try apply orb_false_elim in H1; firstorder.
{ cbn. repeat case_match; simpl; auto; try lia. rewrite Heqs. reflexivity.
  case_match; try lia. }
simpl. lia.
Qed.

Corollary bevar_occur_evar_open dbi1 dbi2 X phi:
bevar_occur phi dbi1 = false -> dbi1 < dbi2 ->
bevar_occur (evar_open dbi2 X phi) dbi1 = false.
Proof.
intros H H0. apply Private_bevar_occur_evar_open with (sz := size phi); auto.
Qed.

Lemma well_formed_positive_bevar_subst φ : forall n ψ,
mu_free φ ->
well_formed_positive φ = true -> well_formed_positive ψ = true
->
well_formed_positive (bevar_subst φ ψ n) = true.
Proof.
induction φ; intros n' ψ H H0 H1; simpl; auto.
2-3: apply andb_true_iff in H as [E1 E2];
     simpl in H0; apply eq_sym, andb_true_eq in H0; destruct H0; 
     rewrite -> IHφ1, -> IHφ2; auto.
* break_match_goal; auto.
Qed.

Lemma mu_free_bevar_subst :
forall φ ψ, mu_free φ -> mu_free ψ -> forall n, mu_free (bevar_subst φ ψ n).
Proof.
induction φ; intros ψ H H0 n'; simpl; try now constructor.
* break_match_goal; auto.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
* simpl in H. apply andb_true_iff in H as [E1 E2]. now rewrite -> IHφ1, -> IHφ2.
* simpl in H. now apply IHφ.
* inversion H.
Qed.

Corollary mu_free_evar_open :
forall φ, mu_free φ -> forall x n, mu_free (evar_open n x φ).
Proof.
intros φ H x n. apply mu_free_bevar_subst; auto.
Qed.

Theorem evar_open_free_evar_subst_swap :
forall φ x n ψ y, x <> y -> well_formed ψ ->
  evar_open n x (free_evar_subst φ ψ y) = free_evar_subst (evar_open n x φ) ψ y.
Proof.
induction φ; intros x' n' ψ y H H0; simpl; auto.
* destruct (decide (y = x)); simpl.
  ** rewrite evar_open_wfc; auto. unfold well_formed,well_formed_closed in H0. destruct_and!.
     assumption.
  ** reflexivity.
* cbn. break_match_goal; simpl; auto. destruct (decide (y = x')); auto.
  congruence.
* unfold evar_open in *. now rewrite -> bevar_subst_app, -> IHφ1, -> IHφ2.
* unfold evar_open in *. now rewrite -> bevar_subst_imp, -> IHφ1, -> IHφ2.
* unfold evar_open in *. now rewrite -> bevar_subst_exists, -> IHφ.
* unfold evar_open in *. now rewrite -> bevar_subst_mu, -> IHφ.
Qed.

Lemma free_evars_free_evar_subst : forall φ ψ x,
free_evars (free_evar_subst φ ψ x) ⊆ free_evars φ ∪ free_evars ψ.
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
  bevar_subst φ ψ n = free_evar_subst (evar_open n x φ) ψ x.
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
  bsvar_subst φ ψ n = free_svar_subst (svar_open n X φ) ψ X.
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
  (no_negative_occurrence_db_b db1 (evar_open db2 x φ) ->
  no_negative_occurrence_db_b db1 φ) /\
  (no_positive_occurrence_db_b db1 (evar_open db2 x φ) ->
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
well_formed_positive (evar_open n x φ) = true ->
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
well_formed_closed_mu_aux (bevar_subst φ ψ n) m = true.
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
well_formed_closed_ex_aux (bevar_subst φ ψ n) n = true.
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
well_formed_positive (bevar_subst φ ψ n) = true.
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
well_formed_closed_ex_aux (evar_quantify x n φ) (S n) = true.
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
well_formed_closed_mu_aux (svar_quantify X n φ) (S n) = true.
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
well_formed_closed_mu_aux (evar_quantify x n φ) m = true.
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
well_formed_closed_ex_aux (svar_quantify X n φ) m = true.
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
 → no_negative_occurrence_db_b db1 (evar_quantify x db2 φ))
∧ (no_positive_occurrence_db_b db1 φ
   → no_positive_occurrence_db_b db1 (evar_quantify x db2 φ)).
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
well_formed_positive (evar_quantify x n φ) = true.
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
  well_formed (patt_exists (evar_quantify x 0 φ)) = true.
Proof.
intros φ x H.
unfold well_formed, well_formed_closed in *.
destruct_and!.
split_and!; simpl.
- apply evar_quantify_positive. assumption.
- apply evar_quantify_closed_mu. assumption.
- apply evar_quantify_closed_ex. assumption.
Qed.

Theorem evar_quantify_not_free :
forall φ x n, x ∉ (free_evars (evar_quantify x n φ)).
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
forall φ X n, X ∉ (free_svars (svar_quantify X n φ)).
Proof.
induction φ; intros x' n'; simpl; try set_solver.
case_match; simpl; set_solver.
Qed.

(* FIXME: rename! *)
Lemma evar_quantify_noop :
forall φ x n, count_evar_occurrences x φ = 0 ->
evar_quantify x n φ = φ.
Proof.
induction φ; intros x' n' H; simpl; auto.
- simpl in H.
  destruct (decide (x = x')).
  + subst x'. destruct (decide (x = x)). simpl in H. inversion H. contradiction.
  + simpl in H. destruct (decide (x' = x)); cbn; auto. congruence.
- simpl in H. rewrite IHφ1. lia. rewrite IHφ2. lia. reflexivity.
- simpl in H. rewrite IHφ1. lia. rewrite IHφ2. lia. reflexivity.
- simpl in H. rewrite IHφ. lia. reflexivity.
- simpl in H. rewrite IHφ. lia. reflexivity.
Qed.


Lemma wf_ex_evar_quantify x p:
well_formed p = true ->
well_formed (patt_exists (evar_quantify x 0 p)) = true.
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

End subst.