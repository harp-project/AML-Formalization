Require Import List.
Require Import Ensembles.
Require Import Coq.Strings.String.
Require Import extralibrary.
From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Logic.Classical_Prop.
From stdpp Require Import countable.
From stdpp Require Import pmap gmap mapset fin_sets.
Require Import stdpp_ext.

Class MLVariables := {
  evar : Type;
  svar : Type;
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

  Instance Pattern_eqdec : EqDecision Pattern.
  Proof.
    unfold EqDecision. intros. unfold Decision. decide equality.
    - apply evar_eqdec.
    - apply svar_eqdec.
    - apply nat_eq_dec.
    - apply nat_eq_dec.
    - apply sym_eq.
  Qed.
      

  Definition Theory := Ensemble Pattern.
  
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

  Fixpoint bevar_occur (phi : Pattern) (x : db_index) : bool :=
    match phi with
    | patt_free_evar x' => false
    | patt_free_svar x' => false
    | patt_bound_evar n => (bool_decide (n = x))
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
    | patt_bound_svar n => (bool_decide (n = x))
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
    | patt_free_evar x' => if evar_eqdec x x' then psi else patt_free_evar x'
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
    | patt_free_svar X' => if svar_eqdec X X' then psi else patt_free_svar X'
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
    | patt_free_evar x' => if evar_eqdec x x' then patt_bound_evar level else patt_free_evar x'
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

  Definition evar_is_fresh_in x ϕ := x ∉ free_evars ϕ.
  Definition svar_is_fresh_in x ϕ := x ∉ free_svars ϕ.

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


  Inductive well_formed_closed_induc : Pattern -> Prop :=
  | wfc_free_evar : forall (x : evar), well_formed_closed_induc (patt_free_evar x)
  | wfc_free_svar : forall (X : svar), well_formed_closed_induc (patt_free_svar X)
  | wfc_sym       : forall (sym : symbols), well_formed_closed_induc (patt_sym sym)
  | wfc_app       : forall (phi psi : Pattern), well_formed_closed_induc phi 
                                                -> well_formed_closed_induc psi -> well_formed_closed_induc (patt_app phi psi)
  | wfc_bott      : well_formed_closed_induc patt_bott
  | wfc_imp       : forall (phi psi : Pattern), well_formed_closed_induc phi 
                                                -> well_formed_closed_induc psi -> well_formed_closed_induc (patt_imp phi psi)
  | wfc_ex        : forall phi : Pattern, 
      (forall (x : evar), 
          x ∉ (free_evars phi) ->
          well_formed_closed_induc (evar_open 0 x phi))
      -> 
      well_formed_closed_induc (patt_exists phi)
  | wfc_mu        : forall phi : Pattern, 
      (forall (X : svar),
          X ∉ (free_svars phi) ->
          well_formed_closed_induc (svar_open 0 X phi)) 
      -> well_formed_closed_induc (patt_mu phi).

  Lemma wfc_wfc_ind_helper : forall sz phi, 
      well_formed_closed phi ->
      le (size phi) sz
      ->
      well_formed_closed_induc phi.
  Proof.
    induction sz; destruct phi; intros Hwf Hsz ; simpl in *; try inversion Hsz; auto. 1, 2, 5, 6 : constructor.
    - inversion Hwf.
    - inversion Hwf.
    - constructor. apply IHsz. firstorder. lia. apply IHsz. firstorder. lia.
    - constructor. apply IHsz. firstorder. lia. apply IHsz. firstorder. lia.
    - constructor. apply wfc_ex_to_wfc_body in Hwf. unfold wfc_body_ex in Hwf. intros. 
      apply (IHsz (evar_open 0 x phi)). apply Hwf. assumption. erewrite evar_open_size in Hsz.  apply Peano.le_S_n in Hsz. exact Hsz. exact signature.
    - constructor. apply wfc_mu_to_wfc_body in Hwf. unfold wfc_body_mu in Hwf. intros. 
      apply (IHsz (svar_open 0 X phi)). apply Hwf. assumption. erewrite svar_open_size in Hsz. apply Peano.le_S_n in Hsz. exact Hsz. exact signature.
  Qed.

  Lemma wfc_wfc_ind phi: well_formed_closed phi -> well_formed_closed_induc phi.
  Proof.
    intros H.
    apply wfc_wfc_ind_helper with (sz := size phi).
    auto. lia.
  Qed.

  Lemma wfc_ind_wfc: forall phi, 
      well_formed_closed_induc phi 
      ->
      well_formed_closed phi.
  Proof.
    intros. induction H; firstorder.
    - apply wfc_body_to_wfc_ex. unfold wfc_body_ex. assumption.
    - apply wfc_body_to_wfc_mu. unfold wfc_body_mu. assumption.
  Qed.

  Lemma evar_open_last: forall phi i u j v,
      (i <> j) -> evar_open i u (evar_open j v phi) = evar_open j v phi
      ->
      (evar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - simpl in H. destruct (n=?j) eqn:D.
      + simpl. destruct (n =? i) eqn:D1.
        * apply Nat.eqb_eq in D1. subst. apply Nat.eqb_eq in D. lia.
        * auto.
      + simpl. destruct (n =? i) eqn:D1.
        * apply Nat.eqb_eq in D1. subst. simpl in H0. rewrite D in H0. simpl in H0. rewrite Nat.eqb_refl in H0. congruence.
        * auto.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. exact H. inversion H0. exact H3. exact H.  inversion H0. exact H2.
    - simpl in H0. inversion H0. simpl. erewrite (IHphi (i+1) _ (j+1)). reflexivity. lia. exact H2.
    - simpl in H0. inversion H0. simpl. erewrite (IHphi (i) _ (j)). reflexivity. lia. exact H2.
  Qed.

  Lemma svar_open_last: forall phi i u j v,
      evar_open i u (svar_open j v phi) = svar_open j v phi
      ->
      (evar_open i u phi) = phi.
  Proof.
    induction phi; firstorder.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - simpl. erewrite IHphi1, IHphi2. reflexivity. inversion H. exact H2. inversion H. exact H1.
    - simpl in H. inversion H. simpl. erewrite (IHphi (i+1) _ (j)). reflexivity. exact H1.
    - simpl in H. inversion H. simpl. erewrite (IHphi (i) _ (j+1)). reflexivity.  exact H1.
  Qed.

  (* evar_open of fresh name does not change in a well-formed pattern*)
  Lemma evar_open_fresh :
    forall phi,
      well_formed_closed phi ->
      forall n v,
        evar_open n v phi = phi.
  Proof.
    intros phi IHwf. apply (wfc_wfc_ind) in IHwf.
    induction IHwf; firstorder.
    - simpl. rewrite IHIHwf1. rewrite IHIHwf2. reflexivity.
    - simpl. rewrite IHIHwf1. rewrite IHIHwf2. reflexivity.
    - simpl. eapply (evar_open_last _ _ _ _ (fresh_evar phi))in H0. erewrite H0. reflexivity. lia.
      apply set_evar_fresh_is_fresh.
    - simpl. eapply svar_open_last in H0. erewrite H0. reflexivity. 
      instantiate (1 := fresh_svar phi). apply set_svar_fresh_is_fresh.
  Qed.

  Lemma evar_open_comm:
    forall n m,
      n <> m 
      ->
      forall x y phi,
        evar_open n x (evar_open m y phi) = evar_open m y (evar_open n x phi).
  Proof.
  Admitted.

  
  (* TODO make a wrapper that does not have the 'sz' variable *)
  Lemma fresh_notin: 
    forall sz phi v w,
      le (size phi) sz ->
      v ∉ (free_evars phi) ->
      w ∉ (free_evars phi) ->
      (v <> w) ->
      forall n,
        v ∉ (free_evars (evar_open n w phi)).
  Proof.
    induction sz; destruct phi; intros v w Hsz Hlsv Hlsw Hneq n0; simpl in *; try inversion Hsz; auto.
    - destruct (n =? n0) eqn:P.
      + simpl. apply not_elem_of_singleton_2. assumption.
      + simpl. trivial.
    - destruct (n =? n0) eqn:P.
      + simpl. apply not_elem_of_singleton_2. assumption.
      + simpl. trivial.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite -> elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - rewrite elem_of_union.
      apply and_not_or. 
      rewrite -> elem_of_union in Hlsv.
      rewrite -> elem_of_union in Hlsw.
      apply not_or_and in Hlsv.
      apply not_or_and in Hlsw.
      destruct Hlsv, Hlsw.
      split.
      + apply IHsz. lia. assumption. assumption. assumption.
      + apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
    - apply IHsz. lia. assumption. assumption. assumption.
  Qed.

  Lemma free_evars_svar_open : forall (psi : Pattern) (dbi :db_index) (X : svar),
      free_evars (svar_open dbi X psi) = free_evars psi.
  Proof.
    induction psi; intros; simpl; try reflexivity.
    * destruct (n =? dbi); reflexivity.
    * rewrite -> IHpsi1. rewrite -> IHpsi2. reflexivity.
    * rewrite -> IHpsi1. rewrite -> IHpsi2. reflexivity.
    * rewrite -> IHpsi. reflexivity.
    * rewrite -> IHpsi. reflexivity.
  Qed.

  Lemma not_free_implies_positive_negative_occurrence :
    forall (phi : Pattern) (X : svar),
      X ∉ (free_svars phi) ->
      positive_occurrence_named X phi /\ negative_occurrence_named X phi.
  Proof.
    induction phi; simpl; intros Y H; split; try constructor. (* try firstorder.*)
    * unfold not. intros. apply H. apply elem_of_singleton_2. symmetry. assumption.
    * apply IHphi1. unfold not. intros H0.
      assert (H': Y ∈ (union (free_svars phi1) (free_svars phi2))).
      { apply elem_of_union_l. assumption. }
      auto.
    * apply IHphi2. unfold not. intros H0.
      assert (H': Y ∈ (union (free_svars phi1) (free_svars phi2))).
      { apply elem_of_union_r. assumption. }
      auto.
    * apply IHphi1. unfold not. intros H0. apply H. apply elem_of_union_l. auto.
    * apply IHphi2. unfold not. intros H0. apply H. apply elem_of_union_r. auto.
    * apply IHphi1. unfold not. intros H0. apply H. apply elem_of_union_l. auto.
    * apply IHphi2. unfold not. intros H0. apply H. apply elem_of_union_r. auto.
    * apply IHphi1. unfold not. intros H0. apply H. apply elem_of_union_l. auto.
    * apply IHphi2. unfold not. intros H0. apply H. apply elem_of_union_r. auto.
    * apply IHphi. auto.
    * apply IHphi. auto.
    * apply IHphi. auto.
    * apply IHphi. auto.
  Qed.

  Lemma positive_negative_occurrence_db_named :
    forall (phi : Pattern) (dbi : db_index) (X : svar),
      (positive_occurrence_db dbi phi ->
       positive_occurrence_named X phi ->
       positive_occurrence_named X (svar_open dbi X phi))
      /\ (negative_occurrence_db dbi phi ->
          negative_occurrence_named X phi ->
          negative_occurrence_named X (svar_open dbi X phi)).
  Proof.
    induction phi; intros; split; simpl; try firstorder.
    + destruct ( n =? dbi). constructor. constructor.
    + destruct (eqb_reflect n dbi).
      { inversion H. subst. lia. }
      { constructor. }
    + inversion H; subst. inversion H0; subst.
      constructor. firstorder. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder. firstorder.
    + inversion H. inversion H0. subst.
      constructor. apply IHphi. firstorder. assumption.
    + inversion H. inversion H0. subst.
      constructor. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder.
    + inversion H. inversion H0. subst.
      constructor. firstorder.
  Qed.


  Lemma well_formed_app_1 : forall (phi1 phi2 : Pattern),
      well_formed (patt_app phi1 phi2) -> well_formed phi1.
  Proof.
    unfold well_formed. intros.
    destruct H as [Hpos Hclos].
    inversion Hpos. inversion Hclos.
    split. assumption. unfold well_formed_closed. assumption.
  Qed.

  Lemma well_formed_app_2 : forall (phi1 phi2 : Pattern),
      well_formed (patt_app phi1 phi2) -> well_formed phi2.
  Proof.
    unfold well_formed. intros.
    destruct H as [Hpos Hclos].
    inversion Hpos. inversion Hclos.
    split. assumption. unfold well_formed_closed. assumption.
  Qed.

  Lemma free_svars_evar_open : forall (ϕ : Pattern) (dbi :db_index) (x : evar),
      free_svars (evar_open dbi x ϕ) = free_svars ϕ.
  Proof.
    induction ϕ; intros; simpl; try reflexivity.
    * destruct (n =? dbi); reflexivity.
    * rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
    * rewrite -> IHϕ1. rewrite -> IHϕ2. reflexivity.
    * rewrite -> IHϕ. reflexivity.
    * rewrite -> IHϕ. reflexivity.
  Qed.

  Lemma svar_open_evar_open_comm
    : forall (phi : Pattern) (dbi1 : db_index)(x : evar)(dbi2 : db_index)(X : svar),
      evar_open dbi1 x (svar_open dbi2 X phi) = svar_open dbi2 X (evar_open dbi1 x phi).
  Proof.
    induction phi; intros; simpl; try reflexivity.
    * destruct (n =? dbi1); reflexivity.
    * destruct (n =? dbi2); reflexivity.
    * rewrite -> IHphi1. rewrite -> IHphi2. reflexivity.
    * rewrite -> IHphi1. rewrite -> IHphi2. reflexivity.
    * rewrite -> IHphi. reflexivity.
    * rewrite -> IHphi. reflexivity.
  Qed.

  Lemma positive_negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      (positive_occurrence_named X (evar_open dbi x ϕ) <-> positive_occurrence_named X ϕ)
      /\ (negative_occurrence_named X (evar_open dbi x ϕ) <-> negative_occurrence_named X ϕ).
  Proof.
    induction ϕ; intros; simpl; split; try reflexivity.
    + destruct (n =? dbi).
      split; intros H; inversion H; constructor. reflexivity.
    + destruct (n =? dbi).
      split; intros H; inversion H; constructor. reflexivity.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
    + split; intros H; inversion H; subst; constructor; firstorder.
  Qed.

  Lemma positive_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      positive_occurrence_named X (evar_open dbi x ϕ) <-> positive_occurrence_named X ϕ.
  Proof.
    intros.
    pose proof (P := positive_negative_occurrence_evar_open ϕ X dbi x).
    destruct P as [P _]. exact P.
  Qed.

  Lemma negative_occurrence_evar_open : forall (ϕ : Pattern) (X : svar) (dbi : db_index) (x : evar),
      negative_occurrence_named X (evar_open dbi x ϕ) <-> negative_occurrence_named X ϕ.
  Proof.
    intros.
    pose proof (P := positive_negative_occurrence_evar_open ϕ X dbi x).
    destruct P as [_ P]. exact P.
  Qed.

  Lemma evar_open_wfp : forall (sz : nat) (phi : Pattern),
      le (size phi) sz ->
      forall(n : db_index) (x : evar),
        well_formed_positive phi -> well_formed_positive (evar_open n x phi).
  Proof.
    induction sz; destruct phi; intros Hsz dbi e Hwfp; simpl in *; auto; try inversion Hsz; subst.
    + destruct (n =? dbi). constructor. assumption.
    + destruct (n =? dbi). constructor. assumption.
    + destruct Hwfp as [Hwfp1 Hwfp2].
      split; apply IHsz. lia. assumption. lia. assumption.
    + destruct Hwfp as [Hwfp1 Hwfp2].
      split; apply IHsz. lia. assumption. lia. assumption.
    + destruct Hwfp as [Hwfp1 Hwfp2].
      split; apply IHsz. lia. assumption. lia. assumption.
    + destruct Hwfp as [Hwfp1 Hwfp2].
      split; apply IHsz. lia. assumption. lia. assumption.
    + apply IHsz. lia. assumption.
    + apply IHsz. lia. assumption.
    + split.
      * apply positive_occurrence_db_evar_open. firstorder.
      * apply IHsz. lia. firstorder.
    + split.
      * apply positive_occurrence_db_evar_open. firstorder.
      * apply IHsz. lia. firstorder.
  Qed.

  Lemma positive_occurrence_db_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar),
      (positive_occurrence_db dbi phi ->
       positive_occurrence_db dbi (svar_open dbi X phi))
      /\ (negative_occurrence_db dbi phi -> negative_occurrence_db dbi (svar_open dbi X phi)).
  Proof.
    induction phi; intros; simpl; split; intros; try constructor; try inversion H; try firstorder.
    + destruct (n =? dbi); constructor.
    + destruct (n =? dbi).
      * constructor.
      * subst. constructor. assumption.
  Qed.

  
  Lemma positive_negative_occurrence_db_svar_open_le : forall (phi : Pattern) (dbi1 dbi2 : db_index) (X : svar),
      dbi1 < dbi2 ->
      (
        positive_occurrence_db dbi1 phi ->
        positive_occurrence_db dbi1 (svar_open dbi2 X phi)
      )
      /\ (negative_occurrence_db dbi1 phi -> negative_occurrence_db dbi1 (svar_open dbi2 X phi)).
  Proof.
    induction phi; intros dbi1 dbi2 X Hneq; split; intros H; inversion H; subst; intros; simpl in *; auto.
    + destruct (n =? dbi2); constructor.
    + destruct (n =? dbi2); constructor. auto.
    + constructor; firstorder.
    + constructor; firstorder.
    + constructor; firstorder.
    + constructor; firstorder.
    + constructor. apply IHphi. lia. assumption.
    + constructor. apply IHphi. lia. assumption.
    + constructor. apply IHphi. lia. assumption.
    + constructor. apply IHphi. lia. assumption.
  Qed.

  Lemma wfp_svar_open : forall (phi : Pattern) (dbi : db_index) (X : svar),
      well_formed_positive phi ->
      well_formed_positive (svar_open dbi X phi).
  Proof.
    induction phi; intros.
    + constructor.
    + constructor.
    + constructor.
    + simpl. destruct (n =? dbi); constructor.
    + constructor.
    + inversion H. firstorder.
    + constructor.
    + inversion H. firstorder.
    + simpl in H. simpl. auto.
    + simpl in H. simpl.
      split.
      * apply positive_negative_occurrence_db_svar_open_le.
        lia. firstorder.
      * firstorder.
  Qed.


  Lemma positive_negative_occurrence_named_svar_open :
    forall (phi : Pattern) (X Y : svar) (dbi : db_index),
      X <> Y ->
      (
        negative_occurrence_named X phi ->
        negative_occurrence_named X (svar_open dbi Y phi)
      ) /\ (
        positive_occurrence_named X phi ->
        positive_occurrence_named X (svar_open dbi Y phi)
      ).
  Proof.
    induction phi; intros X Y dbi XneY; split; intros Hneg; inversion Hneg; subst;
      simpl in *; try constructor; try firstorder.
    - destruct (n =? dbi); constructor. 
      unfold not. intros. assert (X = Y). symmetry. assumption.
      unfold not in XneY. destruct (XneY H0).
    - destruct (n =? dbi); constructor.
  Qed.

  Lemma evar_open_wfc_aux db1 db2 dbs X phi :
    db1 <= db2 ->
    well_formed_closed_aux phi db1 dbs ->
    evar_open db2 X phi = phi.
  Proof.
    generalize dependent dbs. generalize dependent db2. generalize dependent db1.
    induction phi; intros db1 db2 dbs Hle Hwfca; simpl; simpl in Hwfca; auto.
    * destruct (eqb_reflect n db2). lia. auto.
    * rewrite -> IHphi1 with (dbs := dbs)(db1 := db1). 3: firstorder. 2: auto. 
      rewrite -> IHphi2 with (dbs := dbs)(db1 := db1). 3: firstorder. 2: auto.
      auto.
    * rewrite -> IHphi1 with (dbs := dbs)(db1 := db1). 3: firstorder. 2: auto.
      rewrite -> IHphi2 with (dbs := dbs)(db1 := db1). 3: firstorder. 2: auto.
      auto.
    * apply f_equal.
      rewrite -> IHphi with (dbs := dbs)(db1 := db1 + 1). 3: auto. 2: lia. auto.
    * apply f_equal. rewrite -> IHphi with (dbs := dbs + 1)(db1 := db1). auto. auto. auto.
  Qed.

  Lemma evar_open_wfc m X phi : well_formed_closed phi -> evar_open m X phi = phi.
  Proof.
    intros.
    unfold well_formed_closed in H.
    apply evar_open_wfc_aux with (X := X)(db2 := m) in H.
    2: lia.
    auto.
  Qed.

  Lemma evar_open_bsvar_subst m phi1 phi2 dbi X
    : well_formed_closed phi2 ->
      evar_open m X (bsvar_subst phi1 phi2 dbi)
      = bsvar_subst (evar_open m X phi1) phi2 dbi.
  Proof.
    generalize dependent dbi. generalize dependent m. induction phi1; intros m dbi Hwfc; auto.
    - simpl. destruct (n =? m) eqn:Heq, (compare_nat n (S dbi)) eqn:Hdbi; simpl; auto.
    - simpl. destruct (compare_nat n dbi); simpl; auto. auto using evar_open_wfc.
    - simpl. rewrite -> IHphi1_1. rewrite -> IHphi1_2. auto. auto. auto.
    - simpl. rewrite -> IHphi1_1. rewrite -> IHphi1_2. auto. auto. auto.
    - simpl. apply f_equal. rewrite -> IHphi1. auto. auto.
    - simpl. rewrite -> IHphi1. auto. auto.
  Qed.

  Lemma fresh_evar_svar_open dbi X phi :
    fresh_evar (svar_open dbi X phi) = fresh_evar phi.
  Proof.
    unfold fresh_evar.
    apply f_equal.
    apply f_equal.
    apply free_evars_svar_open.
  Qed.

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
    : (EVarSet) :=
    match C with
    | box => empty
    | ctx_app_l cc p prf => union (free_evars_ctx cc) (free_evars p)
    | ctx_app_r p cc prf => union (free_evars p) (free_evars_ctx cc)
    end.


  Inductive is_subformula_of_ind : Pattern -> Pattern -> Prop :=
  | sub_eq ϕ₁ ϕ₂ : ϕ₁ = ϕ₂ -> is_subformula_of_ind ϕ₁ ϕ₂
  | sub_app_l ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_app ϕ₂ ϕ₃)
  | sub_app_r ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₃ -> is_subformula_of_ind ϕ₁ (patt_app ϕ₂ ϕ₃)
  | sub_imp_l ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_imp ϕ₂ ϕ₃)
  | sub_imp_r ϕ₁ ϕ₂ ϕ₃ : is_subformula_of_ind ϕ₁ ϕ₃ -> is_subformula_of_ind ϕ₁ (patt_imp ϕ₂ ϕ₃)
  | sub_exists ϕ₁ ϕ₂ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_exists ϕ₂)
  | sub_mu ϕ₁ ϕ₂ : is_subformula_of_ind ϕ₁ ϕ₂ -> is_subformula_of_ind ϕ₁ (patt_mu ϕ₂)
  .

  (*
  Fixpoint is_subformula_of (phi1 : Pattern) (phi2 : Pattern) : bool :=
    orb (if (Pattern_eqdec phi1 phi2) then true else false)
        match phi2 with
        | patt_app p q => orb (is_subformula_of phi1 p) (is_subformula_of phi1 q)
        | patt_imp p q => orb (is_subformula_of phi1 p) (is_subformula_of phi1 q)
        | patt_exists p => is_subformula_of phi1 p
        | patt_mu p => is_subformula_of phi1 p
        | _ => false
        end.
  *)

  Lemma bsvar_subst_contains_subformula ϕ₁ ϕ₂ dbi :
    bsvar_occur ϕ₁ dbi ->
    is_subformula_of_ind ϕ₂ (bsvar_subst ϕ₁ ϕ₂ dbi).
  Proof.
    intros H. induction ϕ₁; simpl; simpl in H; try inversion H.
    - case_bool_decide; destruct (compare_nat n dbi); try inversion H1.
      + lia.
      + constructor. reflexivity.
      + lia.
    - move: H H1 IHϕ₁1 IHϕ₁2.
      case: (bsvar_occur ϕ₁1 dbi); case: (bsvar_occur ϕ₁2 dbi); move=> H H1 IHϕ₁₁ IHϕ₁₂.
      + apply sub_app_l. auto.
      + apply sub_app_l. auto.
      + apply sub_app_r. auto.
      + done.
    - Abort. (* TO BE FINISHED *)
    
  
  Lemma free_evars_subformula ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ -> free_evars ϕ₁ ⊆ free_evars ϕ₂.
  Proof.
    intros H. induction H.
    * subst. apply PreOrder_Reflexive.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. auto.
    * simpl. auto.
  Qed.
  

  Lemma evar_fresh_in_subformula x ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ ->
    evar_is_fresh_in x ϕ₂ ->
    evar_is_fresh_in x ϕ₁.
  Proof.
    unfold evar_is_fresh_in.
    intros Hsub Hfresh.
    apply free_evars_subformula in Hsub.
    auto.
  Qed.

  Lemma free_svars_subformula ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ -> free_svars ϕ₁ ⊆ free_svars ϕ₂.
  Proof.
    intros H. induction H.
    * subst. apply PreOrder_Reflexive.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_l.
    * simpl. eapply PreOrder_Transitive.
      apply IHis_subformula_of_ind.
      apply union_subseteq_r.
    * simpl. auto.
    * simpl. auto.
  Qed.
  
  Lemma svar_fresh_in_subformula x ϕ₁ ϕ₂ :
    is_subformula_of_ind ϕ₁ ϕ₂ ->
    svar_is_fresh_in x ϕ₂ ->
    svar_is_fresh_in x ϕ₁.
  Proof.
    unfold svar_is_fresh_in.
    intros Hsub Hfresh.
    apply free_svars_subformula in Hsub.
    auto.
  Qed.
  
End syntax.

Module Notations.
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
End Notations.
