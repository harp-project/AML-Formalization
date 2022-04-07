From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base sets propset.
From Coq Require Import Logic.Classical_Prop.
From MatchingLogic.Utils Require Import Lattice stdpp_ext extralibrary.
From MatchingLogic Require Import Syntax IndexManipulation.

Import MatchingLogic.Syntax.Notations.

  Section with_signature.
    Context {Σ : Signature}.

    
    Definition patt_not (phi : Pattern) := patt_imp phi patt_bott.

    Definition patt_or  (l r : Pattern) := patt_imp (patt_not l) r.

    Definition patt_and (l r : Pattern) :=
      patt_not (patt_or (patt_not l) (patt_not r)).

    Definition patt_top := (patt_not patt_bott).

    Definition patt_iff (l r : Pattern) :=
      patt_and (patt_imp l r) (patt_imp r l).

    Definition patt_forall (phi : Pattern) :=
      patt_not (patt_exists (patt_not phi)).

    Definition patt_nu (phi : Pattern) :=
      patt_not (patt_mu (patt_not (bsvar_subst phi (patt_not (patt_bound_svar 0)) 0))).

    Lemma size_not (phi : Pattern) :
      size (patt_not phi) = 1 + size phi.
    Proof.
      simpl. lia.
    Qed.

    Lemma size_or (l r : Pattern) :
      size (patt_or l r) = 2 + size l + size r.
    Proof.
      simpl. lia.
    Qed.

    Lemma size_and (l r : Pattern) :
      size (patt_and l r) = 5 + size l + size r.
    Proof.
      simpl. lia.
    Qed.
    
    Lemma well_formed_not (phi : Pattern) :
      well_formed phi = true ->
      well_formed (patt_not phi) = true.
    Proof.
      unfold well_formed, well_formed_closed. simpl.
      intros H.
      destruct_and!. split_and!; auto.
    Qed.

    Lemma well_formed_top : well_formed patt_top.
    Proof. reflexivity. Qed.

    Lemma well_formed_or (phi1 phi2 : Pattern) :
      well_formed phi1 = true ->
      well_formed phi2 = true ->
      well_formed (patt_or phi1 phi2) = true.
    Proof.
      unfold patt_or.
      unfold well_formed, well_formed_closed. simpl.
      intros H1 H2.
      destruct_and!. split_and!; auto.
    Qed.
    
    Lemma well_formed_iff (phi1 phi2 : Pattern) :
      well_formed phi1 = true ->
      well_formed phi2 = true ->
      well_formed (patt_iff phi1 phi2) = true.
    Proof.
      unfold patt_iff, patt_and, patt_or, patt_not. intros.
      unfold well_formed in *. simpl.
      unfold well_formed_closed in *. simpl.
      destruct_and!. split_and!; auto.
    Qed.

    Lemma well_formed_and (phi1 phi2 : Pattern) :
      well_formed phi1 = true ->
      well_formed phi2 = true ->
      well_formed (patt_and phi1 phi2) = true.
    Proof.
      unfold patt_or.
      unfold well_formed. simpl.
      unfold well_formed_closed. simpl.
      intros H1 H2.
      destruct_and!. split_and!; auto.
    Qed.

    Lemma well_formed_closed_ex_all φ : forall n,
      well_formed_closed_ex_aux (patt_forall φ) n
    <->
      well_formed_closed_ex_aux φ (S n).
    Proof.
      intros. simpl. do 2 rewrite andb_true_r. auto.
    Qed.

    Lemma well_formed_closed_mu_all φ : forall m,
      well_formed_closed_mu_aux (patt_forall φ) m
    <->
      well_formed_closed_mu_aux φ m.
    Proof.
      intros. simpl. do 2 rewrite andb_true_r. auto.
    Qed.
    
    Lemma well_formed_positive_all φ : 
      well_formed_positive (patt_forall φ)
    <->
      well_formed_positive φ.
    Proof.
      intros. simpl. do 2 rewrite andb_true_r. auto.
    Qed.
    
    Lemma bevar_subst_not ψ (wfψ : well_formed_closed ψ) x ϕ :
      bevar_subst (patt_not ϕ) ψ x = patt_not (bevar_subst ϕ ψ x).
    Proof. simpl. unfold patt_not. reflexivity. Qed.

    Lemma bevar_subst_or ψ (wfψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
      bevar_subst (patt_or ϕ₁ ϕ₂) ψ x = patt_or (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
    Proof. simpl. unfold patt_or. unfold patt_not. reflexivity. Qed.

    Lemma bevar_subst_and ψ (wfψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
      bevar_subst (patt_and ϕ₁ ϕ₂) ψ x = patt_and (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
    Proof. simpl. unfold patt_and. unfold patt_not. reflexivity. Qed.

    Lemma bevar_subst_iff ψ (wfψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
      bevar_subst (patt_iff ϕ₁ ϕ₂) ψ x = patt_iff (bevar_subst ϕ₁ ψ x) (bevar_subst ϕ₂ ψ x).
    Proof. simpl. unfold patt_iff. unfold patt_and. unfold patt_not. reflexivity. Qed.

    Lemma bevar_subst_top ψ (wfψ : well_formed_closed ψ) x : bevar_subst patt_top ψ x = patt_top.
    Proof. simpl. unfold patt_top. unfold patt_not. reflexivity. Qed.

    Lemma bevar_subst_forall ψ (wfψ : well_formed_closed ψ) x ϕ :
      bevar_subst (patt_forall ϕ) ψ x = patt_forall (bevar_subst ϕ ψ (S x)).
    Proof. simpl. unfold patt_forall. unfold patt_not. reflexivity. Qed.

    (* TODO: bevar_subst_nu *)

    Lemma bsvar_subst_not ψ (wfψ : well_formed_closed ψ) x ϕ :
      bsvar_subst (patt_not ϕ) ψ x = patt_not (bsvar_subst ϕ ψ x).
    Proof. simpl. unfold patt_not. reflexivity. Qed.

    Lemma bsvar_subst_or ψ (wfψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
      bsvar_subst (patt_or ϕ₁ ϕ₂) ψ x = patt_or (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
    Proof. simpl. unfold patt_or. unfold patt_not. reflexivity. Qed.

    Lemma bsvar_subst_and ψ (wfψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
      bsvar_subst (patt_and ϕ₁ ϕ₂) ψ x = patt_and (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
    Proof. simpl. unfold patt_and. unfold patt_not. reflexivity. Qed.

    Lemma bsvar_subst_iff ψ (wfψ : well_formed_closed ψ) x ϕ₁ ϕ₂ :
      bsvar_subst (patt_iff ϕ₁ ϕ₂) ψ x = patt_iff (bsvar_subst ϕ₁ ψ x) (bsvar_subst ϕ₂ ψ x).
    Proof. simpl. unfold patt_iff. unfold patt_and. unfold patt_not. reflexivity. Qed.

    Lemma bsvar_subst_top ψ (wfψ : well_formed_closed ψ) x : bsvar_subst patt_top ψ x = patt_top.
    Proof. simpl. unfold patt_top. unfold patt_not. reflexivity. Qed.

    Lemma bsvar_subst_forall ψ (wfψ : well_formed_closed ψ) x ϕ :
      bsvar_subst (patt_forall ϕ) ψ x = patt_forall (bsvar_subst ϕ ψ x).
    Proof. simpl. unfold patt_forall. unfold patt_not. reflexivity. Qed.

    (* ******* *)

    Lemma evar_open_not k x ϕ : evar_open k x (patt_not ϕ) = patt_not (evar_open k x ϕ).
    Proof. simpl. unfold patt_not. reflexivity. Qed.

    Lemma evar_open_or k x ϕ₁ ϕ₂ : evar_open k x (patt_or ϕ₁ ϕ₂) = patt_or (evar_open k x ϕ₁) (evar_open k x ϕ₂).
    Proof. simpl. unfold patt_or. unfold patt_not. reflexivity. Qed.

    Lemma evar_open_and k x ϕ₁ ϕ₂ : evar_open k x (patt_and ϕ₁ ϕ₂) = patt_and (evar_open k x ϕ₁) (evar_open k x ϕ₂).
    Proof. simpl. unfold patt_and. unfold patt_not. reflexivity. Qed.

    Lemma evar_open_iff k x ϕ₁ ϕ₂ : evar_open k x (patt_iff ϕ₁ ϕ₂) = patt_iff (evar_open k x ϕ₁) (evar_open k x ϕ₂).
    Proof. simpl. unfold patt_iff. unfold patt_and. unfold patt_not. reflexivity. Qed.

    Lemma evar_open_top k x : evar_open k x patt_top = patt_top.
    Proof. simpl. unfold patt_top. unfold patt_not. reflexivity. Qed.

    Lemma evar_open_forall k x ϕ : evar_open k x (patt_forall ϕ) = patt_forall (evar_open (S k) x ϕ).
    Proof. simpl. unfold patt_forall. unfold patt_not. reflexivity. Qed.

    Lemma evar_open_nu k x ϕ : evar_open k x (patt_nu ϕ) = patt_nu (evar_open k x ϕ).
    Proof. simpl. unfold patt_nu. unfold patt_not. unfold evar_open. simpl.
      rewrite -> bevar_subst_bsvar_subst; auto.
    Abort.

    Lemma svar_open_not k x ϕ : svar_open k x (patt_not ϕ) = patt_not (svar_open k x ϕ).
    Proof. simpl. unfold patt_not. reflexivity. Qed.

    Lemma svar_open_or k x ϕ₁ ϕ₂ : svar_open k x (patt_or ϕ₁ ϕ₂) = patt_or (svar_open k x ϕ₁) (svar_open k x ϕ₂).
    Proof. simpl. unfold patt_or. unfold patt_not. reflexivity. Qed.

    Lemma svar_open_and k x ϕ₁ ϕ₂ : svar_open k x (patt_and ϕ₁ ϕ₂) = patt_and (svar_open k x ϕ₁) (svar_open k x ϕ₂).
    Proof. simpl. unfold patt_and. unfold patt_not. reflexivity. Qed.

    Lemma svar_open_iff k x ϕ₁ ϕ₂ : svar_open k x (patt_iff ϕ₁ ϕ₂) = patt_iff (svar_open k x ϕ₁) (svar_open k x ϕ₂).
    Proof. simpl. unfold patt_iff. unfold patt_and. unfold patt_not. reflexivity. Qed.

    Lemma svar_open_top k x : svar_open k x patt_top = patt_top.
    Proof. simpl. unfold patt_top. unfold patt_not. reflexivity. Qed.

    Lemma svar_open_forall k x ϕ : svar_open k x (patt_forall ϕ) = patt_forall (svar_open k x ϕ).
    Proof. simpl. unfold patt_forall. unfold patt_not. reflexivity. Qed.

    #[global]
     Instance Unary_not : Unary patt_not :=
      {|
      unary_bevar_subst := bevar_subst_not ;
      unary_bsvar_subst := bsvar_subst_not ;
      unary_wf := well_formed_not ;
      |}.

    #[global]
     Instance NVNullary_top : NVNullary patt_top :=
      {|
      nvnullary_bevar_subst := bevar_subst_top ;
      nvnullary_bsvar_subst := bsvar_subst_top ;
      nvnullary_wf := well_formed_top ;
      |}.

    #[global]
     Instance Binary_or : Binary patt_or :=
      {|
      binary_bevar_subst := bevar_subst_or ;
      binary_bsvar_subst := bsvar_subst_or ;
      binary_wf := well_formed_or ;
      |}.

    #[global]
     Instance Binary_and : Binary patt_and :=
      {|
      binary_bevar_subst := bevar_subst_and ;
      binary_bsvar_subst := bsvar_subst_and ;
      binary_wf := well_formed_and ;
      |}.

    #[global]
     Instance Binary_iff : Binary patt_iff :=
      {|
      binary_bevar_subst := bevar_subst_iff ;
      binary_bsvar_subst := bsvar_subst_iff ;
      binary_wf := well_formed_iff ;
      |}.

    #[global]
     Instance EBinder_forall : EBinder patt_forall _ _ :=
      {|
      ebinder_bevar_subst := bevar_subst_forall ;
      ebinder_bsvar_subst := bsvar_subst_forall ;
      |}.
  
  
  End with_signature.


Module Notations.
  Import Syntax.

  Notation "! a"     := (patt_not   a  ) (at level 71, right associativity) : ml_scope.
  Notation "a 'or' b" := (patt_or    a b) (at level 73, right associativity) : ml_scope.
  Notation "a 'and' b" := (patt_and   a b) (at level 72, right associativity) : ml_scope.
  Notation "a <---> b" := (patt_iff a b) (at level 74, no associativity) : ml_scope.
  Notation "'Top'" := patt_top : ml_scope.
  Notation "'all' , phi" := (patt_forall phi) (at level 70) : ml_scope.
  Notation "'nu' , phi" := (patt_nu phi) (at level 70) : ml_scope.
End Notations.

Module Semantics.

End Semantics.

Export Syntax Semantics.

(*Module Hints.*)
#[export]
 Hint Resolve well_formed_not : core.

#[export]
 Hint Resolve well_formed_or : core.

#[export]
 Hint Resolve well_formed_and : core.

#[export]
 Hint Resolve well_formed_iff : core.

 (*End Hints.*)
