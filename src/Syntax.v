Require Import List.
Require Import Ensembles.
Require Import Coq.Strings.String.
Require Import extralibrary.
From stdpp Require Import countable.
From stdpp Require Import pmap gmap mapset fin_sets.
Require Import stdpp_ext.
  
Class MLVariables := {
  evar : Type;
  svar : Type;
  (* TODO remove _eq, use _eqdec instead *)
  evar_eq : forall (v1 v2 : evar), {v1 = v2} + {v1 <> v2};
  svar_eq : forall (v1 v2 : svar), {v1 = v2} + {v1 <> v2};
  evar_eqdec : EqDecision evar;
  evar_countable : Countable evar;
  svar_eqdec : EqDecision svar;
  svar_countable : Countable svar;
  (* TODO fresh generator *)
  evar_fresh : list evar -> evar;
  svar_fresh : list svar -> svar;
  evar_fresh_is_fresh : forall l,
      ~List.In (evar_fresh l) l;
  svar_fresh_is_fresh : forall l,
      ~List.In (svar_fresh l) l;
  (* We need a way to build named variables from strings *)
  nevar : string -> evar;
  nsvar : string -> svar;
  nevar_inj : forall (s1 s2 : string), nevar s1 = nevar s2 -> s1 = s2;
  nsvar_inj : forall (s1 s2 : string), nsvar s1 = nsvar s2 -> s1 = s2;
}.

Class Signature := {
  variables : MLVariables;
  symbols : Type;
  sym_eq : forall (s1 s2 : symbols), {s1 = s2} + {s1 <> s2};
}.

(* TODO move to some other file *)
Definition Power (Sigma : Type) := Ensemble Sigma.

(* TODO have different type for element variable and for set variable index *)
Definition db_index := nat.


Section syntax.

  Context {signature : Signature}.
  Existing Instance variables.

  (* TODO remove *)
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
  Fixpoint bevar_subst (phi psi : Pattern) (x : db_index) :=
    match phi with
    | patt_free_evar x' => patt_free_evar x'
    | patt_free_svar x' => patt_free_svar x'
    | patt_bound_evar n => match compare_nat n x with
                           | Nat_less _ _ _ => patt_bound_evar n
                           | Nat_equal _ _ _ => psi
                           | Nat_greater _ _ _ => patt_bound_evar (pred n)
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
                           | Nat_greater _ _ _ => patt_bound_svar (pred n)
                           end
    | patt_sym sigma => patt_sym sigma
    | patt_app phi1 phi2 => patt_app (bsvar_subst phi1 psi x)
                                     (bsvar_subst phi2 psi x)
    | patt_bott => patt_bott
    | patt_imp phi1 phi2 => patt_imp (bsvar_subst phi1 psi x) (bsvar_subst phi2 psi x)
    | patt_exists phi' => patt_exists (bsvar_subst phi' psi x)
    | patt_mu phi' => patt_mu (bsvar_subst phi' psi (S x))
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
    | patt_exists phi' => bevar_subst phi' psi 0
    | patt_mu phi' => bsvar_subst phi' psi 0
    | _ => phi
    end.

  (** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)

  Definition EVarSet := (@gset evar evar_eqdec evar_countable).
  Definition SVarSet := (@gset svar svar_eqdec svar_countable).

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
    : SVarSet :=
    match phi with
    | patt_free_evar x => empty
    | patt_free_svar X => singleton X
    | patt_bound_evar x => empty
    | patt_bound_svar X => empty
    | patt_sym sigma => empty
    | patt_app phi1 phi2 => union (free_svars phi1) (free_svars phi2)
    | patt_bott => empty
    | patt_imp phi1 phi2 => union (free_svars phi1) (free_svars phi2)
    | patt_exists phi => free_svars phi
    | patt_mu phi => free_svars phi
    end.


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

  Definition fresh_evar ϕ := evar_fresh (elements (free_evars ϕ)).
  Definition fresh_svar ϕ := svar_fresh (elements (free_svars ϕ)).

  Lemma set_evar_fresh_is_fresh ϕ : fresh_evar ϕ ∉ free_evars ϕ.
  Proof.
    unfold fresh_evar.
    intros H.
    pose proof (Hf := evar_fresh_is_fresh (elements (free_evars ϕ))).
    unfold elements in H. unfold gset_elements in H.
    apply gset_to_list_elem_of in H.
    unfold elements in Hf. unfold gset_elements in Hf.
    apply elem_of_list_In in H. contradiction.
  Qed.

  Lemma set_svar_fresh_is_fresh ϕ : fresh_svar ϕ ∉ free_svars ϕ.
  Proof.
    unfold fresh_svar.
    intros H.
    pose proof (Hf := svar_fresh_is_fresh (elements (free_svars ϕ))).
    unfold elements in H. unfold gset_elements in H.
    apply gset_to_list_elem_of in H.
    unfold elements in Hf. unfold gset_elements in Hf.
    apply elem_of_list_In in H. contradiction.
  Qed.

  (*If phi is a closed body, then (ex, phi) is closed too*)
  Lemma wfc_body_to_wfc_ex:
    forall phi, wfc_body_ex phi -> well_formed_closed (patt_exists phi).
  Proof.
    intros. unfold wfc_body_ex in H. unfold well_formed_closed. simpl.
    unfold well_formed_closed in H.
    apply (wfc_aux_body_ex_imp2 phi 0 0 (fresh_evar phi)) in H. exact H.
    clear H.
    apply set_evar_fresh_is_fresh.
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
      X ∉ (free_svars phi) -> well_formed_closed (svar_open 0 X phi).

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
        -- subst. rewrite -> Nat.le_succ_l in H1. destruct (n =? n') eqn:D1.
      + apply Nat.eqb_eq in D1. rewrite -> D1 in H1. lia.
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
    apply (wfc_aux_body_mu_imp2 phi 0 0 (fresh_svar phi)) in H. exact H.
    apply set_svar_fresh_is_fresh.
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
      x ∉ (free_evars phi) -> well_formed_positive (evar_open 0 x phi).

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
      x ∉ (free_evars phi) -> well_formed (evar_open 0 x phi).

  (* This might be useful in soundness cases prop_ex_left/right *)
  Lemma wf_ex_to_wf_body: forall phi,
      well_formed (patt_exists phi) ->
      wf_body_ex phi.
  Proof.
    unfold wf_body_ex. intros. unfold well_formed in *. destruct H. split.
    - apply (wfp_ex_to_wfp_body phi H). assumption.
    - apply (wfc_ex_to_wfc_body phi H1). assumption.
  Qed.


  
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


End syntax.
