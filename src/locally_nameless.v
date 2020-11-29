Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import extralibrary.

Require Import Coq.micromega.Lia.

(*From Equations Require Import Equations.*)
Require Export String.
Require Export Coq.Lists.ListSet.
Require Export Ensembles_Ext.

Require Export Coq.Program.Wf.
From Coq Require Import ssreflect ssrfun ssrbool.
From stdpp Require Import pmap gmap mapset fin_sets.

Require Import Lattice.
Require Import Signature.

(** ** Matching Logic Syntax *)
Section ml_syntax_semantics.
Definition db_index := nat.

(* Variable signature : Signature. *)
Context {signature : Signature}.
Existing Instance mlvariables.


Definition evar_eqb (v1 v2 : evar) : bool :=
  match evar_eq v1 v2 with
  | left _ => true
  | right _ => false
  end.
Definition svar_eqb (v1 v2 : svar) : bool :=
  match svar_eq v1 v2 with
  | left _ => true
  | right _ => false
  end.  

Inductive Pattern : Type :=
| patt_free_evar (x : evar)
| patt_free_svar (x : svar)
| patt_bound_evar (n : db_index)
| patt_bound_svar (n : db_index)
| patt_sym (sigma : symbols) :  Pattern
| patt_app (phi1 phi2 : Pattern)
| patt_bott
| patt_imp (phi1 phi2 : Pattern)
| patt_exists (phi : Pattern)
| patt_mu (phi : Pattern)
.

(*
Definition sp_eq_dec : forall (signature : Signature)
                              (x y : Pattern), { x = y } + { x <> y }.
Proof.
decide equality.
- exact (eq_name x0 x1).
- decide equality.
- decide equality.
- exact (sigma_eq_dec sigma sigma0).
Defined.
*)


(** There are two substitution operations over types, written
  [vsubst] and [psubst] in Pollack's talk.  
  [vsubst] substitutes a pattern for a bound variable (a de Bruijn index).
  [psubst] substitutes a pattern for a free variable (a name).

  The crucial observation is that variable capture cannot occur
  during either substitution:
  - Types never contain free de Bruijn indices, since these
    indices are used only for representing bound variables.
    Therefore, [vsubst] does not need to
    perform lifting of de Bruijn indices in the substituted type.
  - Types never bind names, only de Bruijn indices.
    Therefore, [psubst] never needs to perform renaming of
    names in the substituted term when descending below a
    binder.
 *)

(* substitute bound variable x for psi in phi *)
Fixpoint bvar_subst (phi psi : Pattern) (x : db_index) :=
match phi with
| patt_free_evar x' => patt_free_evar x'
| patt_free_svar x' => patt_free_svar x'
| patt_bound_evar n => match compare_nat n x with
              | Nat_less _ _ _ => patt_bound_evar n
              | Nat_equal _ _ _ => psi
              | Nat_greater _ _ _ => patt_bound_evar (pred n)
              end
| patt_bound_svar n => match compare_nat n x with
              | Nat_less _ _ _ => patt_bound_svar n
              | Nat_equal _ _ _ => psi
              | Nat_greater _ _ _ => patt_bound_svar (pred n)
              end
| patt_sym sigma => patt_sym sigma
| patt_app phi1 phi2 => patt_app (bvar_subst phi1 psi x)
                                 (bvar_subst phi2 psi x)
| patt_bott => patt_bott
| patt_imp phi1 phi2 => patt_imp (bvar_subst phi1 psi x) (bvar_subst phi2 psi x)
| patt_exists phi' => patt_exists (bvar_subst phi' psi (S x))
| patt_mu phi' => patt_mu (bvar_subst phi' psi (S x))
end.

(* substitute free element variable x for psi in phi *)
Fixpoint free_evar_subst (phi psi : Pattern) (x : evar) :=
match phi with
| patt_free_evar x' => if evar_eq x x' then psi else patt_free_evar x'
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

Fixpoint free_svar_subst (phi psi : Pattern) (X : svar) :=
match phi with
| patt_free_evar x => patt_free_evar x
| patt_free_svar X' => if svar_eq X X' then psi else patt_free_svar X'
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
| patt_exists phi' => bvar_subst phi' psi 0
| patt_mu phi' => bvar_subst phi' psi 0
| _ => phi
end.

(** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)


(*Notation EVarSet := (mapset (@gmap evar evar_eqdec evar_countable)).*)

Notation EVarSet := (@gset evar evar_eqdec evar_countable).

Definition set_singleton {T : Type}
  (eq : forall (x y : T), { x = y } + { x <> y })
  := fun x : T => set_add eq x List.nil.

Fixpoint free_evars (phi : Pattern)
  : EVarSet :=
match phi with
| patt_free_evar x => singleton x
| patt_free_svar X => empty
| patt_bound_evar x => empty
| patt_bound_svar X => empty
| patt_sym sigma => empty
| patt_app phi1 phi2 => union (free_evars phi1) (free_evars phi2)
| patt_bott => empty
| patt_imp phi1 phi2 => union (free_evars phi1) (free_evars phi2)
| patt_exists phi => free_evars phi
| patt_mu phi => free_evars phi
end.

Fixpoint free_svars (phi : Pattern)
  : (ListSet.set svar) :=
match phi with
| patt_free_evar x => List.nil
| patt_free_svar X => set_singleton svar_eq X
| patt_bound_evar x => List.nil
| patt_bound_svar X => List.nil
| patt_sym sigma => List.nil
| patt_app phi1 phi2 => set_union svar_eq (free_svars phi1) (free_svars phi2)
| patt_bott => List.nil
| patt_imp phi1 phi2 => set_union svar_eq (free_svars phi1) (free_svars phi2)
| patt_exists phi => free_svars phi
| patt_mu phi => free_svars phi
end.

(* Section Derived_operators. *)

(* Model of AML ref. snapshot: Definition 2 *)

Record Model := {
  Domain : Type;
  nonempty_witness : Domain;
  Domain_eq_dec : forall (a b : Domain), {a = b} + {a <> b};
  app_interp : Domain -> Domain -> Power Domain;
  sym_interp (sigma : symbols) : Power Domain;
}.

Lemma empty_impl_not_full : forall {M : Model} (S : Power (Domain M)),
    Same_set (Domain M) S (Empty_set (Domain M)) ->
    ~ Same_set (Domain M) S (Full_set (Domain M)).
Proof.
  unfold Same_set. unfold Included. unfold not. intros.
  assert (Hexin : Ensembles.In (Domain M) (Full_set (Domain M)) (nonempty_witness M)).
  { unfold In. constructor. }
  firstorder.
Qed.

Lemma full_impl_not_empty : forall {M : Model} (S : Power (Domain M)),
    Same_set (Domain M) S (Full_set (Domain M)) ->
    ~ Same_set (Domain M) S (Empty_set (Domain M)).
Proof.
  unfold Same_set. unfold Included. unfold not. intros.
  assert (Hexin : Ensembles.In (Domain M) (Full_set (Domain M)) (nonempty_witness M)).
  { unfold In. constructor. }
  firstorder.
Qed.

Definition EVarVal {m : Model} : Type := evar -> Domain m.
Definition SVarVal {m : Model} : Type := svar -> Power (Domain m).

Definition update_evar_val {m : Model} 
           (v : evar) (x : Domain m) (evar_val : @EVarVal m) : EVarVal :=
  fun v' : evar => if evar_eq v v' then x else evar_val v'.

Definition update_svar_val {m : Model}
           (v : svar) (X : Power (Domain m)) (svar_val : @SVarVal m)  : SVarVal :=
  fun v' : svar => if svar_eq v v' then X else svar_val v'.

Definition app_ext {m : Model}
           (l r : Power (Domain m)) :
  Power (Domain m) :=
fun e:Domain m => exists le re:Domain m, l le /\ r re /\ (app_interp m) le re e.

(* TODO move to examples in a different module *)
(*
Compute @app_ext {| Domain := Pattern |}
        (Singleton _ (evar "a")) (Singleton _ (evar "b")).
*)
(* S . empty = empty *)

Lemma app_ext_bot_r : forall (m : Model),
    forall S : Power (Domain m),
  Same_set (Domain m) (app_ext S (Empty_set (Domain m))) (Empty_set (Domain m)).
Proof.
  intros. unfold app_ext. unfold Same_set. unfold Included. unfold In. split; intros.
  * inversion H. inversion H0. inversion H1. inversion H3. contradiction.
  * contradiction.
Qed.

Lemma app_ext_bot_l : forall (m : Model),
    forall S : Power (Domain m),
  Same_set (Domain m) (app_ext (Empty_set (Domain m)) S) (Empty_set (Domain m)).
Proof.
  intros. unfold app_ext. unfold Same_set. unfold Included. unfold In. split; intros.
  * inversion H. inversion H0. inversion H1. contradiction.
  * contradiction.
Qed.

Lemma app_ext_monotonic_l : forall (m : Model),
    forall (S1 S2 S : Power (Domain m)),
      Included (Domain m) S1 S2 ->
      Included (Domain m) (app_ext S1 S) (app_ext S2 S).
Proof.
  intros. unfold app_ext. unfold Included. unfold Included in H.
  intros. unfold In in *. destruct H0 as [le [re [H1 [H2 H3]]]].
  apply H in H1. exists le. exists re. firstorder.
Qed.

Lemma app_ext_monotonic_r : forall (m : Model),
    forall (S S1 S2 : Power (Domain m)),
      Included (Domain m) S1 S2 ->
      Included (Domain m) (app_ext S S1) (app_ext S S2).
Proof.
  intros. unfold app_ext. unfold Included. unfold Included in H.
  intros. unfold In in *. destruct H0 as [le [re [H1 [H2 H3]]]].
  apply H in H2. exists le. exists re. firstorder.
Qed.

(* Semantics of AML ref. snapshot: Definition 3 *)

Fixpoint evar_quantify (x : evar) (level : db_index)
         (p : Pattern) : Pattern :=
match p with
| patt_free_evar x' => if evar_eq x x' then patt_bound_evar level else patt_free_evar x'
| patt_free_svar x' => patt_free_svar x'
| patt_bound_evar x' => patt_bound_evar x'
| patt_bound_svar X => patt_bound_svar X
| patt_sym s => patt_sym s
| patt_app ls rs => patt_app (evar_quantify x level ls) (evar_quantify x level rs)
| patt_bott => patt_bott
| patt_imp ls rs => patt_imp (evar_quantify x level ls) (evar_quantify x level rs)
| patt_exists p' => patt_exists (evar_quantify x (level + 1) p')
| patt_mu p' => patt_mu (evar_quantify x (level + 1) p')
end.

Definition exists_quantify (x : evar)
           (p : Pattern) : Pattern :=
  patt_exists (evar_quantify x 0 p).

Fixpoint size (p : Pattern) : nat :=
match p with
| patt_app ls rs => 1 + (size ls) + (size rs)
| patt_imp ls rs => 1 + (size ls) + (size rs)
| patt_exists p' => 1 + size p'
| patt_mu p' => 1 + size p'
| _ => 0
end.

Fixpoint evar_open (k : db_index) (n : evar)
         (p : Pattern) : Pattern :=
match p with
| patt_free_evar x => patt_free_evar x
| patt_free_svar x => patt_free_svar x
| patt_bound_evar x => if beq_nat x k then patt_free_evar n else patt_bound_evar x
| patt_bound_svar X => patt_bound_svar X
| patt_sym s => patt_sym s
| patt_app ls rs => patt_app (evar_open k n ls) (evar_open k n rs)
| patt_bott => patt_bott
| patt_imp ls rs => patt_imp (evar_open k n ls) (evar_open k n rs)
| patt_exists p' => patt_exists (evar_open (k + 1) n p')
| patt_mu p' => patt_mu (evar_open k n p')
end.

Fixpoint svar_open (k : db_index) (n : svar)
         (p : Pattern) : Pattern :=
match p with
| patt_free_evar x => patt_free_evar x
| patt_free_svar x => patt_free_svar x
| patt_bound_evar x => patt_bound_evar x
| patt_bound_svar X => if beq_nat X k then patt_free_svar n else patt_bound_svar X
| patt_sym s => patt_sym s
| patt_app ls rs => patt_app (svar_open k n ls) (svar_open k n rs)
| patt_bott => patt_bott
| patt_imp ls rs => patt_imp (svar_open k n ls) (svar_open k n rs)
| patt_exists p' => patt_exists (svar_open k n p')
| patt_mu p' => patt_mu (svar_open (k + 1) n p')
end.

Lemma evar_open_size :
  forall (signature : Signature) (k : db_index) (n : evar) (p : Pattern),
    size p = size (evar_open k n p).
Proof.
  intros. generalize dependent k.
  induction p; intros; simpl; try reflexivity.
  destruct (n0 =? k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp (k + 1)); reflexivity.
  rewrite (IHp k); reflexivity.
Qed.

Lemma svar_open_size :
  forall (signature : Signature) (k : db_index) (n : svar) (p : Pattern),
    size p = size (svar_open k n p).
Proof.
  intros. generalize dependent k.
  induction p; intros; simpl; try reflexivity.
  destruct (n0 =? k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp1 k); rewrite (IHp2 k); reflexivity.
  rewrite (IHp k); reflexivity.
  rewrite (IHp (k + 1)); reflexivity.
Qed.

Inductive positive_occurrence_named : svar -> Pattern -> Prop :=
| po_free_evar (x : evar) (sv : svar) : positive_occurrence_named sv (patt_free_evar x)
| po_free_svar (x : svar) (sv : svar) : positive_occurrence_named sv (patt_free_svar x)
| po_bound_evar (m : db_index) (sv : svar) : positive_occurrence_named sv (patt_bound_evar m)
| po_bound_svar (m : db_index) (sv : svar) : positive_occurrence_named sv (patt_bound_svar m)
| po_const (sigma : symbols) (sv : svar) :
    positive_occurrence_named sv (patt_sym sigma)
| po_app (phi1 phi2 : Pattern) (sv : svar) :
  positive_occurrence_named sv phi1 -> positive_occurrence_named sv phi2 ->
  positive_occurrence_named sv (patt_app phi1 phi2)
| po_bott (sv : svar) : positive_occurrence_named sv patt_bott
| po_impl (phi1 phi2 : Pattern) (sv : svar) :
  negative_occurrence_named sv phi1 -> positive_occurrence_named sv phi2 ->
  positive_occurrence_named sv (patt_imp phi1 phi2)
| po_exists (phi : Pattern) (sv : svar) :
  positive_occurrence_named sv phi ->
  positive_occurrence_named sv (patt_exists phi)
| po_mu (phi : Pattern) (sv : svar) :
  positive_occurrence_named sv phi ->
  positive_occurrence_named sv (patt_mu phi)
with negative_occurrence_named : svar -> Pattern -> Prop :=
| no_free_evar (x : evar) (sv : svar) : negative_occurrence_named sv (patt_free_evar x)
| no_free_svar (x : svar) (sv : svar) : x <> sv -> negative_occurrence_named sv (patt_free_svar x)
| no_bound_evar (m : db_index) (sv : svar) :  negative_occurrence_named sv (patt_bound_evar m)
| no_bound_svar (m : db_index) (sv : svar) :  negative_occurrence_named sv (patt_bound_svar m)
| no_const (sigma : symbols) (sv : svar) :
    negative_occurrence_named sv (patt_sym sigma)
| no_app (phi1 phi2 : Pattern) (sv : svar) :
   negative_occurrence_named sv phi1 -> negative_occurrence_named sv phi2 ->
   negative_occurrence_named sv (patt_app phi1 phi2)
| no_bott (sv : svar) :  negative_occurrence_named sv patt_bott
| no_impl (phi1 phi2 : Pattern) (sv : svar) :
  positive_occurrence_named sv phi1 ->  negative_occurrence_named sv phi2 ->
   negative_occurrence_named sv (patt_imp phi1 phi2)
| no_exists (phi : Pattern) (sv : svar) :
   negative_occurrence_named sv phi ->
   negative_occurrence_named sv (patt_exists phi)
| no_mu (phi : Pattern) (sv : svar) :
   negative_occurrence_named sv phi ->
   negative_occurrence_named sv (patt_mu phi)
.
(* Cares only about set variables *)
Inductive positive_occurrence_db : db_index -> Pattern -> Prop :=
| podb_free_evar (x : evar) (n : db_index) : positive_occurrence_db n (patt_free_evar x)
| podb_free_svar (x : svar) (n : db_index) : positive_occurrence_db n (patt_free_svar x)
| podb_bound_evar (m : db_index) (n : db_index) : positive_occurrence_db n (patt_bound_evar m)
| podb_bound_svar (m : db_index) (n : db_index) : positive_occurrence_db n (patt_bound_svar m)
| podb_const (sigma : symbols) (n : db_index) :
    positive_occurrence_db n (patt_sym sigma)
| podb_app (phi1 phi2 : Pattern) (n : db_index) :
  positive_occurrence_db n phi1 -> positive_occurrence_db n phi2 ->
  positive_occurrence_db n (patt_app phi1 phi2)
| podb_bott (n : db_index) : positive_occurrence_db n patt_bott
| podb_impl (phi1 phi2 : Pattern) (n : db_index) :
  negative_occurrence_db n phi1 -> positive_occurrence_db n phi2 ->
  positive_occurrence_db n (patt_imp phi1 phi2)
| podb_exists (phi : Pattern) (n : db_index) :
  positive_occurrence_db n phi ->
  positive_occurrence_db n (patt_exists phi)
| podb_mu (phi : Pattern) (n : db_index) :
  positive_occurrence_db (n+1) phi ->
  positive_occurrence_db n (patt_mu phi)
with negative_occurrence_db : db_index -> Pattern -> Prop :=
| nodb_free_evar (x : evar) (n : db_index) : negative_occurrence_db n (patt_free_evar x)
| nodb_free_svar (x : svar) (n : db_index) : negative_occurrence_db n (patt_free_svar x)
| nodb_bound_evar (m : db_index) (n : db_index) : negative_occurrence_db n (patt_bound_evar m)
| nodb_bound_svar (m : db_index) (n : db_index) : n <> m -> negative_occurrence_db n (patt_bound_svar m)
| nodb_const (sigma : symbols) (n : db_index) :
    negative_occurrence_db n (patt_sym sigma)
| nodb_app (phi1 phi2 : Pattern) (n : db_index) :
   negative_occurrence_db n phi1 -> negative_occurrence_db n phi2 ->
   negative_occurrence_db n (patt_app phi1 phi2)
| nodb_bott (n : db_index) :  negative_occurrence_db n patt_bott
| nodb_impl (phi1 phi2 : Pattern) (n : db_index) :
  positive_occurrence_db n phi1 ->  negative_occurrence_db n phi2 ->
   negative_occurrence_db n (patt_imp phi1 phi2)
| nodb_exists (phi : Pattern) (n : db_index) :
   negative_occurrence_db n phi ->
   negative_occurrence_db n (patt_exists phi)
| nodb_mu (phi : Pattern) (n : db_index) :
   negative_occurrence_db (n+1) phi ->
   negative_occurrence_db n (patt_mu phi)
.

(* Lemmas about opening and positive occurrence *)
Lemma positive_negative_occurrence_db_evar_open : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
    (*le db1 db2 ->*)
    (positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi))
    /\ (negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi)).
Proof.
  induction phi; intros; simpl; split; intros; try constructor; try inversion H; subst; try firstorder.
  * destruct (n =? db2); intros. constructor. assumption.
  * destruct (n =? db2); intros. constructor. assumption.
Qed.

Lemma positive_occurrence_db_evar_open : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
    positive_occurrence_db db1 phi -> positive_occurrence_db db1 (evar_open db2 x phi).
Proof.
  intros.
  pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x).
  firstorder.
Qed.

Lemma negative_occurrence_db_evar_open : forall (phi : Pattern) (db1 db2 : db_index) (x : evar),
    negative_occurrence_db db1 phi -> negative_occurrence_db db1 (evar_open db2 x phi).
Proof.
  intros.
  pose proof (H' := positive_negative_occurrence_db_evar_open phi db1 db2 x).
  firstorder.
Qed.

Fixpoint well_formed_positive (phi : Pattern) : Prop :=
  match phi with
  | patt_free_evar _ => True
  | patt_free_svar _ => True
  | patt_bound_evar _ => True
  | patt_bound_svar _ => True
  | patt_sym _ => True
  | patt_app psi1 psi2 => well_formed_positive psi1 /\ well_formed_positive psi2
  | patt_bott => True
  | patt_imp psi1 psi2 => well_formed_positive psi1 /\ well_formed_positive psi2
  | patt_exists psi => well_formed_positive psi
  | patt_mu psi => positive_occurrence_db 0 psi /\ well_formed_positive psi
  end.

Fixpoint well_formed_closed_aux (phi : Pattern) (max_ind_evar : db_index) (max_ind_svar : db_index) : Prop :=
  match phi with
  | patt_free_evar _ => True
  | patt_free_svar _ => True
  | patt_bound_evar n => n < max_ind_evar
  | patt_bound_svar n => n < max_ind_svar
  | patt_sym _ => True
  | patt_app psi1 psi2 => well_formed_closed_aux psi1 max_ind_evar max_ind_svar /\
                          well_formed_closed_aux psi2 max_ind_evar max_ind_svar
  | patt_bott => True
  | patt_imp psi1 psi2 => well_formed_closed_aux psi1 max_ind_evar max_ind_svar /\
                          well_formed_closed_aux psi2 max_ind_evar max_ind_svar
  | patt_exists psi => well_formed_closed_aux psi (max_ind_evar + 1) max_ind_svar
  | patt_mu psi => well_formed_closed_aux psi max_ind_evar (max_ind_svar + 1)
  end.
Definition well_formed_closed (phi : Pattern) := well_formed_closed_aux phi 0 0.

Lemma well_formed_closed_aux_ind (phi : Pattern) (ind_evar1 ind_evar2 ind_svar1 ind_svar2: db_index) :
  ind_evar1 < ind_evar2 -> ind_svar1 < ind_svar2  
  -> well_formed_closed_aux phi ind_evar1 ind_svar1 
  -> well_formed_closed_aux phi ind_evar2 ind_svar2.
Proof.
  intros. 
  generalize dependent ind_evar1. generalize dependent ind_evar2.
  generalize dependent ind_svar1. generalize dependent ind_svar2.
  induction phi; intros; simpl in *; try lia.
  inversion H1. split. eapply IHphi1; eassumption. eapply IHphi2; eassumption.
  inversion H1. split. eapply IHphi1; eassumption. eapply IHphi2; eassumption.
  - eapply (IHphi ind_svar2 ind_svar1 H0  (ind_evar2 + 1) (ind_evar1 + 1)).
    + lia.
    + assumption.
  - eapply (IHphi (ind_svar2 + 1) (ind_svar1 + 1) _  ind_evar2 ind_evar1).
    + lia.
    + assumption.
    Unshelve.
    lia.
Qed.  

Definition well_formed (phi : Pattern) := well_formed_positive phi /\ well_formed_closed phi.

(* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.3 (body def.) *)
Definition wfc_body_ex phi  := forall x, 
  ~ elem_of x (free_evars phi) -> well_formed_closed (evar_open 0 x phi).

(*Helper lemma for wf_ex_to_wf_body *)
Lemma wfc_aux_body_ex_imp1:
forall phi n n' x,
well_formed_closed_aux phi (S n) n'
->
well_formed_closed_aux (evar_open n x phi) n n'.
Proof.
  - induction phi; intros; try lia; auto.
  * simpl. inversion H.
    -- simpl. rewrite -> Nat.eqb_refl. simpl. trivial.
    -- subst. rewrite -> Nat.le_succ_l in H1. destruct (n =? n0) eqn:D1.
      + apply Nat.eqb_eq in D1. rewrite D1 in H1. lia.
      + simpl. auto.
  * simpl in H. destruct H. firstorder.
  * firstorder.
  * firstorder.
  * firstorder.
Qed.

(*Helper lemma for wf_body_to_wf_ex*)
Lemma wfc_aux_body_ex_imp2:
forall phi n n' x,
  well_formed_closed_aux (evar_open n x phi) n n'
  ->
  well_formed_closed_aux phi (S n) n'.
Proof.
  induction phi; firstorder.
  - simpl. simpl in H. destruct (n =? n0) eqn:P.
    + apply beq_nat_true in P. rewrite P. lia.
    + simpl in H. lia.
Qed.

Lemma wfc_aux_body_iff: 
forall phi n n' x,
well_formed_closed_aux phi (S n) n'
<->
well_formed_closed_aux (evar_open n x phi) n n'.
Proof.
  split.
  apply wfc_aux_body_ex_imp1.
  apply wfc_aux_body_ex_imp2.
Qed.

(*If (ex, phi) is closed, then its body is closed too*)
Lemma wfc_ex_to_wfc_body:
forall phi, well_formed_closed (patt_exists phi) -> wfc_body_ex phi.
Proof.
  intros.
  unfold wfc_body_ex. intros.
  unfold well_formed_closed in *. simpl in H.
  apply wfc_aux_body_ex_imp1. auto.
Qed.

Lemma pmap_to_list_lookup {A} (M : Pmap A) (i : positive) (x : A)
  : (i,x) ∈ (map_to_list M) <-> lookup i M = Some x.
Proof.
  intros. unfold map_to_list. unfold Pto_list. unfold lookup. unfold Plookup.
  destruct M eqn:HM. simpl.
  split; intros.
  + apply Pelem_of_to_list in H. simpl in H.
    destruct H.
    * destruct H as [i' [Hi' Hsome]]. subst. apply Hsome.
    * inversion H.
  + apply Pelem_of_to_list.
    left. simpl. exists i. firstorder.
Qed.
    

  
Lemma gmap_to_list_lookup `{Countable K} {A} (M : gmap K A) (k : K) (a : A): (elem_of_list (k,a) (gmap_to_list M)) <-> (gmap_lookup k M = Some a).
Proof.
  destruct M as [PM PMwf] eqn: HM. simpl.
  unfold gmap_wf in PMwf.
  split; intros H'.
  + apply pmap_to_list_lookup.
    apply elem_of_list_omap in H'.
    destruct H' as [[k' a'] [HxinPM H']].
    apply fmap_Some_1 in H'.
    destruct H' as [k'' [H1 H2]]. inversion H2. subst. clear H2.
    assert (Hk': k' = encode k'').
    { apply bool_decide_unpack in PMwf.
      unfold map_Forall in PMwf.
      apply pmap_to_list_lookup in HxinPM.
      specialize (PMwf k' a' HxinPM).
      apply (inj Some). rewrite <- PMwf.
      apply fmap_Some_2. apply H1. }
    subst. apply HxinPM.
    
  + apply pmap_to_list_lookup in H'.
    apply elem_of_list_omap.
    exists (encode k, a). firstorder.
    rewrite -> decode_encode. simpl. reflexivity.
Qed.


(*
Existing Instance evar_eqdec.
Existing Instance evar_countable.
Existing Instance svar_eqdec.
Existing Instance svar_countable.*)
  Existing Instance gmap_finmap.
Lemma mapset_elements_to_set (X : EVarSet) : list_to_set (mapset_elements X) = X.
Proof.

  Set Printing Implicit.
  (*apply (iff_sym (@mapset_eq evar (gmap evar) gmap_fmap _ _ _ _ _ _ _ _ _ _)).*)
  apply (iff_sym (@mapset_eq evar (gmap evar) gmap_fmap (@gmap_lookup evar _ _) _ _ _ _ _ _ gmap_finmap _ _)).
  unfold gset in X.
  intros.
  pose proof (H' := @elem_of_list_to_set evar EVarSet _ _ _ _ _ x (mapset_elements X)).
  destruct H' as [H1 H2].
  split; intros.
  + specialize (H1 H). clear H2 H.
    unfold mapset_elements in H1.
    Search map_to_list elem_of.
    (*Set Printing Implicit.*)
    destruct X.
    unfold elem_of in H1.
    unfold elem_of.
    rename mapset_car into M.
    unfold map_to_list in H1.
    unfold mapset_elem_of.
    Print mapset_elem_of.
    simpl.
    Search elem_of_list.
    (*unfold elem_of_list in H1.*)
    Unset Printing Notations.
    unfold lookup.
    Print FinMapToList.
    gmap_to_list.
    Set Printing Implicit.
    unfold gmap_to_list in H1.
    
    Locate map_to_list.
    Check map_to_list.
    Search fmap fst.
    unfold mapset_elem_of.
    specialize (H0 H).
      in H.  apply elem_of_list_to_set in H. admit.
  +  unfold elem_of.
  Search mapset_elem_of.
  
  apply gmap_eq.
  Check @list_to_set.
  Search list_to_set.
  Check elem_of_list_to_set.
  Search elem_of.
  Check symmetry_iff.
  (*pose proof (H := mapset_eq (list_to_set (mapset_elements X)) X).*)
  Check mapset_eq. (*apply mapset_eq.*)
  (*apply (@mapset_eq evar _ _ _ _ _ _ _ _ _ _).*)
  Check ( mapset_eq (list_to_set (mapset_elements X)) X).
  Unset Printing Notations.
  Check mapset_eq.
  Check (mapset_elements X).
  
  apply @mapset_eq with (K := evar).
  pose proof ( H := ( mapset_eq (list_to_set (mapset_elements X)) X)).
  rewrite -> mapset_eq.

Lemma set_evar_fresh_is_fresh ϕ : evar_fresh (elements (free_evars ϕ)) ∉ free_evars ϕ.
Proof.
  pose proof (Hf := evar_fresh_is_fresh (elements (free_evars ϕ))).
  Check @list_to_set evar EVarSet _ _ _.
  Search list_to_set.
  assert (Hf': evar_fresh (elements (free_evars ϕ)) ∉ @list_to_set evar EVarSet _ _ _ (elements (free_evars ϕ))).
  { Search list_to_set. unfold not.  intros. apply elem_of_list_to_set in H. unfold elem_of in H.
    Print elem_of_list. Search elem_of_list List.In. apply elem_of_list_In in H. contradiction.}
    clear Hf. Search list_to_set elements. unfold elements in Hf'.
    Search mapset_elements.
Admitted.

(*If phi is a closed body, then (ex, phi) is closed too*)
Lemma wfc_body_to_wfc_ex:
forall phi, wfc_body_ex phi -> well_formed_closed (patt_exists phi).
Proof.
  intros. unfold wfc_body_ex in H. unfold well_formed_closed. simpl.
  unfold well_formed_closed in H.
  apply (wfc_aux_body_ex_imp2 phi 0 0 (evar_fresh (elements (free_evars phi)))) in H. exact H.
  clear H.
  pose proof (Hf := evar_fresh_is_fresh (elements (free_evars phi))).
  Check elements.
  Search elements.
  Search elements elem_of.
  Unset Printing Notations. unfold elem_of
  unfold not. intros.
  Search elements.
  Check elem_of_elements.
  Check evar_fresh_is_fresh.
  pose proof (Hf := evar_fresh_is_fresh (elements (free_evars phi))).
  unfold not in Hf. apply Hf. clear Hf.
  Search elements.
  Check (elem_of_elements (free_evars phi)).
  apply elem_of_elements.
Qed.

(* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.4 (lc_abs_iff_body) *)
(*Conclusion*)
Lemma wfc_body_wfc_ex_iff: 
  forall phi,
  well_formed_closed (patt_exists phi) <-> wfc_body_ex phi.
Proof.
  split.
  - apply wfc_ex_to_wfc_body.
  - apply (wfc_body_to_wfc_ex phi).
Qed.

(*Similarly to the section above but with mu*)
Definition wfc_body_mu phi := forall X, 
  ~List.In X (free_svars phi) -> well_formed_closed (svar_open 0 X phi).

(*Helper for wfc_mu_to_wfc_body*)
Lemma wfc_aux_body_mu_imp1:
forall phi n n' X,
well_formed_closed_aux phi n (S n')
->
well_formed_closed_aux (svar_open n' X phi) n n'.
Proof.
  - induction phi; intros; try lia; auto.
    * simpl. inversion H.
    -- simpl. rewrite Nat.eqb_refl. simpl. trivial.
    -- subst. rewrite Nat.le_succ_l in H1. destruct (n =? n') eqn:D1.
      + apply Nat.eqb_eq in D1. rewrite D1 in H1. lia.
      + simpl. auto. 
    * simpl in H. destruct H. firstorder.
    * firstorder.
    * firstorder.
    * firstorder.
Qed.

(*Helper for *)
Lemma wfc_aux_body_mu_imp2:
forall phi n n' X,
well_formed_closed_aux (svar_open n' X phi) n n'
->
well_formed_closed_aux phi n (S n').
Proof.
  induction phi; firstorder.
  - simpl. simpl in H. destruct (n =? n') eqn:P.
    + apply beq_nat_true in P. rewrite P. lia.
    + simpl in H. lia.
Qed.

(*If (mu, phi) is closed, then its body is closed too*)
Lemma wfc_mu_to_wfc_body:
forall phi, well_formed_closed (patt_mu phi) -> wfc_body_mu phi.
Proof.
  intros. 
  unfold wfc_body_mu. intros.
  unfold well_formed_closed in *. simpl in H.
  apply wfc_aux_body_mu_imp1. auto.
Qed.

(*If phi is a closed body, then (mu, phi) is closed too*)
Lemma wfc_body_to_wfc_mu:
forall phi, wfc_body_mu phi -> well_formed_closed (patt_mu phi).
Proof.
  intros. unfold wfc_body_mu in H. unfold well_formed_closed. simpl.
  unfold well_formed_closed in H.
  apply (wfc_aux_body_mu_imp2 phi 0 0 (svar_fresh (free_svars phi))) in H. exact H.
  apply svar_fresh_is_fresh.
Qed.

(* From https://www.chargueraud.org/research/2009/ln/main.pdf in 3.4 (lc_abs_iff_body) *)
(*Conclusion*)
Lemma wfc_body_wfc_mu_iff: 
  forall phi (X : svar),
  well_formed_closed (patt_mu phi) <-> wfc_body_mu phi.
Proof.
  split.
  - apply wfc_mu_to_wfc_body.
  - apply (wfc_body_to_wfc_mu phi).
Qed.

(* Similarly with positiveness *)
Definition wfp_body_ex phi := forall x,
  ~List.In x (free_evars phi) -> well_formed_positive (evar_open 0 x phi).

Lemma wfp_evar_open : forall phi x n,
  well_formed_positive phi ->
  well_formed_positive (evar_open n x phi).
Proof.
  induction phi; firstorder.
  - intros. simpl. destruct (n =? n0) eqn:P.
    + simpl. trivial.
    + simpl. trivial.
  - simpl in *. firstorder. apply positive_occurrence_db_evar_open. assumption.
Qed.

Lemma wfp_ex_to_wfp_body: forall phi,
  well_formed_positive (patt_exists phi) ->
  wfp_body_ex phi.
Proof.
  unfold wfp_body_ex. intros. apply wfp_evar_open. simpl in H. assumption.
Qed.

(* Connection between bodies and well-formedness *)
Definition wf_body_ex phi := forall x, 
  ~List.In x (free_evars phi) -> well_formed (evar_open 0 x phi).

(* This might be useful in soundness cases prop_ex_left/right *)
Lemma wf_ex_to_wf_body: forall phi,
  well_formed (patt_exists phi) ->
  wf_body_ex phi.
Proof.
  unfold wf_body_ex. intros. unfold well_formed in *. destruct H. split.
  - apply (wfp_ex_to_wfp_body phi H). assumption.
  - apply (wfc_ex_to_wfc_body phi H1). assumption.
Qed.

(*
Definition pattern_lt (p1 p2 : Pattern) :=
  size p1 < size p2.
Lemma pattern_lt_well_founded : well_founded (@pattern_lt).
Proof.
  apply well_founded_lt_compat with size; auto.
Qed.

Instance wf_pattern_lt : WellFounded (@pattern_lt).
apply pattern_lt_well_founded.
Defined.

Equations pattern_interpretation_aux {m : Model}
          (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
          (p : Pattern) : Power (Domain m)
  by wf (size p) :=
  pattern_interpretation_aux evar_val svar_val (patt_free_evar x) := Singleton _ (evar_val x);
  pattern_interpretation_aux evar_val svar_val (patt_free_svar X) := svar_val X;
  pattern_interpretation_aux evar_val svar_val (patt_bound_evar x) := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_bound_svar x) := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_sym s) := (sym_interp m) s;
  pattern_interpretation_aux evar_val svar_val (patt_app ls rs) :=
    app_ext (pattern_interpretation_aux evar_val svar_val ls)
                  (pattern_interpretation_aux evar_val svar_val rs);
  pattern_interpretation_aux evar_val svar_val patt_bott := Empty_set _;
  pattern_interpretation_aux evar_val svar_val (patt_imp ls rs) :=
    Union _ (Complement _ (pattern_interpretation_aux evar_val svar_val ls))
            (pattern_interpretation_aux evar_val svar_val rs);
  pattern_interpretation_aux evar_val svar_val (patt_exists p') :=
    let x := evar_fresh variables (free_evars p') in
    FA_Union
      (fun e => pattern_interpretation_aux (update_evar_val x e evar_val) svar_val
                                  (evar_open 0 x p'));
  pattern_interpretation_aux evar_val svar_val (patt_mu p') :=
    let X := svar_fresh variables (free_svars p') in
    Ensembles_Ext.mu
      (fun S => pattern_interpretation_aux evar_val (update_svar_val X S svar_val)
                                  (svar_open 0 X p')).
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. lia. Defined.
Next Obligation. unfold pattern_lt. simpl. rewrite <- evar_open_size. lia. apply signature. Defined.
Next Obligation. unfold pattern_lt. simpl. rewrite <- svar_open_size. lia. apply signature. Defined.
*)

Section semantics.

  Context {m : Model}.
  Let OS := EnsembleOrderedSet (@Domain m).
  Let  L := PowersetLattice (@Domain m).

Program Fixpoint pattern_interpretation
        (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
        (p : Pattern) {measure (size p)} :=
match p with
| patt_free_evar x => Ensembles.Singleton _ (evar_val x)
| patt_free_svar X => svar_val X
| patt_bound_evar x => Empty_set _
| patt_bound_svar X => Empty_set _
| patt_sym s => (sym_interp m) s
| patt_app ls rs => app_ext (pattern_interpretation evar_val svar_val ls)
                                  (pattern_interpretation evar_val svar_val rs)
| patt_bott => Empty_set _
| patt_imp ls rs => Ensembles.Union _ (Complement _ (pattern_interpretation evar_val svar_val ls))
                            (pattern_interpretation evar_val svar_val rs)
| patt_exists p' =>
  let x := evar_fresh (free_evars p') in
  FA_Union
    (fun e => pattern_interpretation (update_evar_val x e evar_val)
                            svar_val
                            (evar_open 0 x p'))
| patt_mu p' =>
  let X := svar_fresh (free_svars p') in
  @LeastFixpointOf (Ensemble (@Domain m)) OS L
    (fun S => pattern_interpretation evar_val
                            (update_svar_val X S svar_val)
                            (svar_open 0 X p'))
end.
Next Obligation. intros. subst. simpl; lia. Defined.
Next Obligation. intros. subst. simpl; lia. Defined.
Next Obligation. intros. subst. simpl; lia. Defined.
Next Obligation. intros. subst. simpl; lia. Defined.
Next Obligation. intros. subst. simpl; rewrite <- evar_open_size. lia. apply signature. Defined.
Next Obligation. intros. subst. simpl; rewrite <- svar_open_size. lia. apply signature. Defined.
Next Obligation. Tactics.program_simpl. Defined.

Lemma pattern_interpretation_free_evar_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (x : evar) :
  pattern_interpretation evar_val svar_val (patt_free_evar x) = Ensembles.Singleton _ (evar_val x).
Admitted.

Lemma pattern_interpretation_free_svar_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (X : svar) :
  pattern_interpretation evar_val svar_val (patt_free_svar X) = svar_val X.
Admitted.

Lemma pattern_interpretation_bound_evar_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (x : db_index) :
  pattern_interpretation evar_val svar_val (patt_bound_evar x) = Empty_set _ .
Admitted.

Lemma pattern_interpretation_bound_svar_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (X : db_index) :
  pattern_interpretation evar_val svar_val (patt_bound_svar X) = Empty_set _ .
Admitted.

Lemma pattern_interpretation_sym_simpl
      (evar_val : @EVarVal m) (svar_val : @SVarVal m)
      (s : symbols) :
  pattern_interpretation evar_val svar_val (patt_sym s) = sym_interp m s.
Proof.

Admitted.


Lemma pattern_interpretation_app_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (ls rs : Pattern) :
  pattern_interpretation evar_val svar_val (patt_app ls rs) =
  app_ext (pattern_interpretation evar_val svar_val ls)
                (pattern_interpretation evar_val svar_val rs).
Admitted.

Lemma pattern_interpretation_bott_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)) :
  pattern_interpretation evar_val svar_val patt_bott = Empty_set _ .
Admitted.

Lemma pattern_interpretation_imp_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (ls rs : Pattern) :
  pattern_interpretation evar_val svar_val (patt_imp ls rs) =
  Ensembles.Union _ (Complement _ (pattern_interpretation evar_val svar_val ls))
          (pattern_interpretation evar_val svar_val rs).
Admitted.

Lemma pattern_interpretation_ex_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (p : Pattern) :
  pattern_interpretation evar_val svar_val (patt_exists p) =
  let x := evar_fresh (free_evars p) in
  FA_Union 
    (fun e => pattern_interpretation (update_evar_val x e evar_val)
                            svar_val
                            (evar_open 0 x p)).
Admitted.

Lemma pattern_interpretation_mu_simpl
      (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m))
      (p : Pattern) :
  pattern_interpretation evar_val svar_val (patt_mu p) =
  let X := svar_fresh (free_svars p) in
  @LeastFixpointOf (Ensemble (@Domain m)) OS L
    (fun S => pattern_interpretation evar_val
                            (update_svar_val X S svar_val)
                            (svar_open 0 X p)).
Admitted.

(*
Ltac proof_ext_val :=
simpl;intros;
repeat
  (* Normalize *)
   rewrite (Same_set_to_eq (Union_Empty_l _))
|| rewrite (Same_set_to_eq (Compl_Compl_Powers _ _))
|| rewrite
   (Same_set_to_eq (Compl_Union_Compl_Intes_Powers_alt _ _ _))
|| rewrite (Same_set_to_eq (FA_rel _ _ _))
  (* Apply *)
|| (eapply (proj1 Same_set_Compl) ; intros)
|| (eapply FA_Inters_same ; intros)
  (* Final step *)
|| exact Complement_Empty_is_Full
|| exact (Symdiff_val _ _)
|| exact (Same_set_refl _).
 *)

End semantics.

Section Semantics_of_derived_operators.

  (* TODO: Need to be able to simplify Program Fixpoint definitions *)
  
End Semantics_of_derived_operators.

(**
   Proof of correct semantics for the derived operators
   ref. snapshot: Proposition 4
*)

(* Theory,axiom ref. snapshot: Definition 5 *)

Definition Theory := Power Pattern.

Definition satisfies_model (m : Model) (phi : Pattern) : Prop :=
forall (evar_val : evar -> Domain m) (svar_val : svar -> Power (Domain m)),
  Same_set _ (pattern_interpretation (m := m) evar_val svar_val phi) (Full_set _).

Definition satisfies_theory (m : Model) (theory : Theory)
: Prop := forall axiom : Pattern, Ensembles.In _ theory axiom -> (satisfies_model m axiom).

Definition satisfies (theory : Theory) (p: Pattern)
: Prop := forall m : Model, (satisfies_theory m theory) -> (satisfies_model m p).

(* End of definition 5. *)

Inductive Application_context : Type :=
| box
| ctx_app_l (cc : Application_context) (p : Pattern) (Prf : well_formed p)
| ctx_app_r (p : Pattern) (cc : Application_context) (Prf : well_formed p)
.

Fixpoint subst_ctx (C : Application_context) (p : Pattern)
  : Pattern :=
match C with
| box => p
| ctx_app_l C' p' prf => patt_app (subst_ctx C' p) p'
| ctx_app_r p' C' prf => patt_app p' (subst_ctx C' p)
end.

Fixpoint free_evars_ctx (C : Application_context)
  : (ListSet.set evar) :=
match C with
| box => List.nil
| ctx_app_l cc p prf => set_union evar_eq (free_evars_ctx cc) (free_evars p)
| ctx_app_r p cc prf => set_union evar_eq (free_evars p) (free_evars_ctx cc)
end.

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
  patt_not (patt_mu (patt_not (bvar_subst phi (patt_not (patt_bound_svar 0)) 0))).


Lemma pattern_interpretation_not_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)(phi : Pattern),
    pattern_interpretation evar_val svar_val (patt_not phi) = Complement (Domain m) (pattern_interpretation evar_val svar_val phi).
Proof.
  intros. unfold patt_not.
  rewrite -> pattern_interpretation_imp_simpl.
  rewrite -> pattern_interpretation_bott_simpl.
  apply Extensionality_Ensembles.
  apply Union_Empty_l.
Qed.

Lemma pattern_interpretation_or_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                      (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_or phi1 phi2)
    = Ensembles.Union (Domain m) (pattern_interpretation evar_val svar_val phi1) (pattern_interpretation evar_val svar_val phi2).
Proof.
  intros. unfold patt_or.
  rewrite -> pattern_interpretation_imp_simpl.
  rewrite -> pattern_interpretation_not_simpl.
  assert (H: Complement (Domain m) (Complement (Domain m) (pattern_interpretation evar_val svar_val phi1)) = pattern_interpretation evar_val svar_val phi1).
  { apply Extensionality_Ensembles. apply Compl_Compl_Ensembles. }
  rewrite -> H. reflexivity.
Qed.

Lemma pattern_interpretation_or_comm : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                     (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_or phi1 phi2)
    = pattern_interpretation evar_val svar_val (patt_or phi2 phi1).
Proof.
  intros.
  repeat rewrite -> pattern_interpretation_or_simpl.
  apply Extensionality_Ensembles.
  apply Union_Symmetric.
Qed.

Lemma pattern_interpretation_and_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                       (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_and phi1 phi2)
    = Ensembles.Intersection (Domain m) (pattern_interpretation evar_val svar_val phi1) (pattern_interpretation evar_val svar_val phi2).
Proof.
  intros. unfold patt_and.
  rewrite -> pattern_interpretation_not_simpl.
  rewrite -> pattern_interpretation_or_simpl.
  repeat rewrite -> pattern_interpretation_not_simpl.
  apply Extensionality_Ensembles.
  apply Compl_Union_Compl_Intes_Ensembles_alt.
Qed.

Lemma pattern_interpretation_and_comm : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                     (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_and phi1 phi2)
    = pattern_interpretation evar_val svar_val (patt_and phi2 phi1).
Proof.
  intros.
  repeat rewrite -> pattern_interpretation_and_simpl.
  apply Extensionality_Ensembles.
  apply Intersection_Symmetric.
Qed.

Lemma pattern_interpretation_top_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m),
    pattern_interpretation evar_val svar_val patt_top = Full_set (Domain m).
Proof.
  intros. unfold patt_top.
  rewrite -> pattern_interpretation_not_simpl.
  rewrite -> pattern_interpretation_bott_simpl.
  apply Extensionality_Ensembles.
  apply Complement_Empty_is_Full.
Qed.

(* TODO prove. Maybe some de-morgan laws could be helpful in proving this? *)
Lemma pattern_interpretation_iff_or : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                     (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_iff phi1 phi2)
    = pattern_interpretation evar_val svar_val (patt_or (patt_and phi1 phi2) (patt_and (patt_not phi1) (patt_not phi2))).
Proof.

Admitted.

Lemma pattern_interpretation_iff_comm : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m)
                                      (phi1 phi2 : Pattern),
    pattern_interpretation evar_val svar_val (patt_iff phi1 phi2)
    = pattern_interpretation evar_val svar_val (patt_iff phi2 phi1).
Proof.
  intros.
  unfold patt_iff.
  rewrite -> pattern_interpretation_and_comm.
  reflexivity.
Qed.

(* TODO: forall, nu *)

(* TODO prove *)
Lemma pattern_interpretation_fa_simpl : forall {m : Model} (evar_val : @EVarVal m) (svar_val : @SVarVal m) (phi : Pattern),
    pattern_interpretation evar_val svar_val (patt_forall phi) =
    let x := evar_fresh (free_evars phi) in
    FA_Intersection (fun e : @Domain m => pattern_interpretation (update_evar_val x e evar_val) svar_val (evar_open 0 x phi) ).
Proof.
  intros.
  unfold patt_forall.
  rewrite -> pattern_interpretation_not_simpl.
  rewrite -> pattern_interpretation_ex_simpl.
  simpl.
  apply Extensionality_Ensembles.
  unfold Same_set. unfold Complement. unfold Included. unfold In.
  split; intros.
Admitted.

Lemma evar_open_not k x ϕ : evar_open k x (patt_not ϕ) = patt_not (evar_open k x ϕ).
Proof.
  simpl. unfold patt_not. reflexivity.
Qed.

Lemma evar_open_or k x ϕ₁ ϕ₂ : evar_open k x (patt_or ϕ₁ ϕ₂) = patt_or (evar_open k x ϕ₁) (evar_open k x ϕ₂).
Proof.
  simpl. unfold patt_or. unfold patt_not. reflexivity.
Qed.

Lemma evar_open_and k x ϕ₁ ϕ₂ : evar_open k x (patt_and ϕ₁ ϕ₂) = patt_and (evar_open k x ϕ₁) (evar_open k x ϕ₂).
Proof.
  simpl. unfold patt_and. unfold patt_not. reflexivity.
Qed.

Definition M_predicate (M : Model) (ϕ : Pattern) : Prop := forall ρₑ ρₛ,
    Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Full_set (Domain M))
    \/ Same_set (Domain M) (pattern_interpretation ρₑ ρₛ ϕ) (Empty_set (Domain M)).


Lemma M_predicate_impl M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_imp ϕ₁ ϕ₂).
Proof.
  unfold M_predicate. intros Hp1 Hp2 ρₑ ρₛ.
  specialize (Hp1 ρₑ ρₛ). specialize (Hp2 ρₑ ρₛ).
  rewrite -> pattern_interpretation_imp_simpl.
  destruct Hp1, Hp2; apply Same_set_to_eq in H; apply Same_set_to_eq in H0; rewrite -> H; rewrite -> H0.
  + left. apply Union_Compl_Fullset.
  + right.
    rewrite -> (Same_set_to_eq (Complement_Full_is_Empty)).
    apply Union_Empty_r.
  + left.
    rewrite -> (Same_set_to_eq (Complement_Empty_is_Full)).
    unfold Same_set. unfold Included. unfold In. split; intros; constructor; constructor.
  + left. apply Union_Compl_Fullset.
Qed.

Lemma M_predicate_bott M : M_predicate M patt_bott.
Proof.
  unfold M_predicate. intros. right.
  rewrite -> pattern_interpretation_bott_simpl.
  apply Same_set_refl.
Qed.

Lemma M_predicate_not M ϕ : M_predicate M ϕ -> M_predicate M (patt_not ϕ).
Proof.
  intros. unfold patt_not. auto using M_predicate_impl, M_predicate_bott.
Qed.

Lemma M_predicate_or M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_or ϕ₁ ϕ₂).
Proof.
  intros. unfold patt_or. auto using M_predicate_not, M_predicate_impl.
Qed.

Lemma M_predicate_and M ϕ₁ ϕ₂ : M_predicate M ϕ₁ -> M_predicate M ϕ₂ -> M_predicate M (patt_and ϕ₁ ϕ₂).
Proof.
  intros. unfold patt_and. auto using M_predicate_or, M_predicate_not.
Qed.

(* TODO something like this, but with binding a free variable *)
Lemma M_predicate_exists M ϕ :
  let x := evar_fresh (free_evars ϕ) in
  M_predicate M (evar_open 0 x ϕ) -> M_predicate M (patt_exists ϕ).
Proof.
  simpl. unfold M_predicate. intros.
  rewrite -> pattern_interpretation_ex_simpl.
  simpl.
  pose proof (H' := classic (exists e : Domain M, Same_set (Domain M) (pattern_interpretation (update_evar_val (evar_fresh (free_evars ϕ)) e ρₑ) ρₛ (evar_open 0 (evar_fresh (free_evars ϕ)) ϕ)) (Full_set (Domain M)))).
  destruct H'.
  - (* For some member, the subformula evaluates to full set. *)
    left. apply Same_set_symmetric. apply Same_set_Full_set.
    unfold Included. intros. constructor.
    destruct H0. unfold Same_set in H0. destruct H0. clear H0.
    unfold Included in H2. specialize (H2 x H1).
    exists x0. unfold In in H2. apply H2.
  - (* The subformula does not evaluate to full set for any member. *)
    right.
    unfold Same_set.
    split.
    + unfold Included. intros.
      unfold In in H1. inversion H1. subst. clear H1. destruct H2.
      specialize (H (update_evar_val (evar_fresh (free_evars ϕ)) x0 ρₑ) ρₛ).
      destruct H.
      * exfalso. apply H0. exists x0. apply H.
      * unfold Same_set in H. destruct H. clear H2.
        unfold Included in H. specialize (H x).
        auto.
    + unfold Included. intros. inversion H1.
Qed.

(* TODO top forall iff *)
    
(* TODO this pattern evar_open of zero to fresh variable occurs quite often; we should have a name for it *)
(* ϕ is expected to have dangling evar indices *)
Lemma pattern_interpretation_set_builder M ϕ ρₑ ρₛ :
  let x := evar_fresh (free_evars ϕ) in
  M_predicate M (evar_open 0 x ϕ) ->
  Same_set (Domain M)
           (pattern_interpretation ρₑ ρₛ (patt_exists (patt_and (patt_bound_evar 0) ϕ)))
           (fun m : (Domain M) => Same_set (Domain M)
                                           (pattern_interpretation (update_evar_val x m ρₑ) ρₛ (evar_open 0 x ϕ))
                                           (Full_set _)).
Proof.
  simpl. intros Hmp.
  rewrite -> pattern_interpretation_ex_simpl.
  red. simpl free_evars.
  rewrite -> evar_open_and.
  remember (evar_fresh (set_union evar_eq (@nil evar) (free_evars ϕ))) as x'.
Admitted.

End ml_syntax_semantics.

Module MLNotations.
  Declare Scope ml_scope.
  Delimit Scope ml_scope with ml.
  (* TODO: change Bot and Top to unicode symbols *)
  Notation "a $ b" := (patt_app a b) (at level 65, right associativity) : ml_scope.
  Notation "'Bot'" := patt_bott : ml_scope.
  Notation "a ---> b"  := (patt_imp a b) (at level 90, right associativity,
                                         b at level 200) : ml_scope.
  Notation "'ex' , phi" := (patt_exists phi) (at level 70) : ml_scope.
  Notation "'mu' , phi" := (patt_mu phi) (at level 70) : ml_scope.

  Notation "¬ a"     := (patt_not   a  ) (at level 75, right associativity) : ml_scope.
  Notation "a 'or' b" := (patt_or    a b) (at level 85, right associativity) : ml_scope.
  Notation "a 'and' b" := (patt_and   a b) (at level 80, right associativity) : ml_scope.
  Notation "a <---> b" := (patt_iff a b) (at level 95, no associativity) : ml_scope.
  Notation "'Top'" := patt_top : ml_scope.
  Notation "'all' , phi" := (patt_forall phi) (at level 70) : ml_scope.
  Notation "'nu' , phi" := (patt_nu phi) (at level 70) : ml_scope.

  Notation "M ⊨ᴹ phi" := (satisfies_model M phi) (left associativity, at level 50) : ml_scope.
  (* FIXME this should not be called `satisfies` *)
Notation "G ⊨ phi" := (satisfies G phi) (left associativity, at level 50) : ml_scope.
Notation "M ⊨ᵀ Gamma" := (satisfies_theory M Gamma)
    (left associativity, at level 50) : ml_scope.
End MLNotations.

Section ml_proof_system.
  Import MLNotations.
  Open Scope ml_scope.

  Context {signature : Signature}.
(* Proof system for AML ref. snapshot: Section 3 *)
(* TODO: all propagation rules, framing, use left and right rules (no contexts) like in bott *)
(* TODO: add well-formedness of theory *)
(* TODO: use well-formedness as parameter in proof system *)

Reserved Notation "theory ⊢ pattern" (at level 1).
Inductive ML_proof_system (theory : Theory) :
  Pattern -> Prop :=

(* Hypothesis *)
  | hypothesis (axiom : Pattern) :
      well_formed axiom ->
      (Ensembles.In _ theory axiom) -> theory ⊢ axiom
  
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
      well_formed phi1 -> well_formed (phi1 ---> phi2) ->
      theory ⊢ phi1 ->
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ phi2

  (* Existential quantifier *)
  | Ex_quan (phi : Pattern) (y : evar) :
      well_formed phi ->
      theory ⊢ (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi))

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Pattern) (x : evar) :
      well_formed phi1 -> well_formed phi2 ->
      theory ⊢ (phi1 ---> phi2) ->
      set_mem evar_eq x (free_evars phi2) = false ->
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
      well_formed phi -> well_formed psi ->
      theory ⊢ (((ex , phi) $ psi) ---> (ex , phi $ psi))

  | Prop_ex_right (phi psi : Pattern) :
      well_formed phi -> well_formed psi ->
      theory ⊢ ((psi $ (ex , phi)) ---> (ex , psi $ phi))

  (* Framing *)
  | Framing_left (phi1 phi2 psi : Pattern) :
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((phi1 $ psi) ---> (phi2 $ psi))

  | Framing_right (phi1 phi2 psi : Pattern) :
      theory ⊢ (phi1 ---> phi2) ->
      theory ⊢ ((psi $ phi1) ---> (psi $ phi2))

(* Fixpoint reasoning *)
  (* Set Variable Substitution *)
  | Svar_subst (phi psi : Pattern) (X : svar) :
      theory ⊢ phi -> theory ⊢ (free_svar_subst phi psi X)

  (* Pre-Fixpoint *)
  (* TODO: is this correct? *)
  | Pre_fixp (phi : Pattern) :
      theory ⊢ (instantiate (patt_mu phi) (patt_mu phi) ---> (patt_mu phi))

  (* Knaster-Tarski *)
  | Knaster_tarski (phi psi : Pattern) :
      theory ⊢ ((instantiate (patt_mu phi) psi) ---> psi) ->
      theory ⊢ ((@patt_mu signature phi) ---> psi)

(* Technical rules *)
  (* Existence *)
  | Existence : theory ⊢ (ex , patt_bound_evar 0)

  (* Singleton *)
  | Singleton_ctx (C1 C2 : Application_context) (phi : Pattern) (x : evar) : 
      theory ⊢ (¬ ((subst_ctx C1 (patt_free_evar x and phi)) and
                    (subst_ctx C2 (patt_free_evar x and (¬ phi)))))

where "theory ⊢ pattern" := (ML_proof_system theory pattern).

Definition T_predicate Γ ϕ := forall M, (M ⊨ᵀ Γ) -> @M_predicate signature M ϕ.

Lemma T_predicate_impl Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_imp ϕ₁ ϕ₂).
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_impl.
Qed.

Lemma T_predicate_bot Γ : T_predicate Γ patt_bott.
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_bott.
Qed.

Lemma T_predicate_not Γ ϕ : T_predicate Γ ϕ -> T_predicate Γ (patt_not ϕ).
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_not.
Qed.

Lemma T_predicate_or Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_or ϕ₁ ϕ₂).
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_or.
Qed.

Lemma T_predicate_and Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_and ϕ₁ ϕ₂).
Proof.
  unfold T_predicate.
  intros.
  auto using M_predicate_and.
Qed.

(* TODO: top iff exists forall *)


End ml_proof_system.


