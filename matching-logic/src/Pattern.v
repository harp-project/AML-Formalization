From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import countable infinite.
From stdpp Require Import pmap gmap mapset fin_sets propset.
Require Import stdpp_ext.

Require Import extralibrary.

From MatchingLogic Require Export
    Signature.


(* TODO have different type for element variable and for set variable index *)
Definition db_index := nat.

Inductive Pattern {Σ : Signature} : Set :=
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

Global
Instance Pattern_eqdec {Σ : Signature} : EqDecision Pattern.
Proof. solve_decision. Defined.

Global Instance Pattern_countable {Σ : Signature} (sc : Countable symbols) : Countable Pattern.
Proof.
  set (enc :=
         fix go p : gen_tree (unit
                              + ((@symbols Σ)
                                 + (((@evar variables) + db_index)
                                    + ((@svar variables) + db_index))))%type :=
           match p with
           | patt_bott => GenLeaf (inl ())
           | patt_sym s => GenLeaf (inr (inl s))
           | patt_free_evar x => GenLeaf (inr (inr (inl (inl x))))
           | patt_free_svar X => GenLeaf (inr (inr (inr (inl X))))
           | patt_bound_evar n => GenLeaf (inr (inr (inl (inr n))))
           | patt_bound_svar n => GenLeaf (inr (inr (inr (inr n))))
           | patt_app p1 p2 => GenNode 0 [go p1; go p2]
           | patt_imp p1 p2 => GenNode 1 [go p1; go p2]
           | patt_exists p' => GenNode 2 [go p']
           | patt_mu p' => GenNode 3 [go p']
           end
      ).

  set (dec :=
         fix go (p : gen_tree (unit
                              + ((@symbols Σ)
                                 + (((@evar variables) + db_index)
                                    + ((@svar variables) + db_index))))%type) : Pattern :=
           match p with
           | GenLeaf (inl ()) => patt_bott
           | GenLeaf (inr (inl s)) => patt_sym s
           | GenLeaf (inr (inr (inl (inl x)))) => patt_free_evar x
           | GenLeaf (inr (inr (inr (inl X)))) => patt_free_svar X
           | GenLeaf (inr (inr (inl (inr n)))) => patt_bound_evar n
           | GenLeaf (inr (inr (inr (inr n)))) => patt_bound_svar n
           | GenNode 0 [p1; p2] => patt_app (go p1) (go p2)
           | GenNode 1 [p1; p2] => patt_imp (go p1) (go p2)
           | GenNode 2 [p'] => patt_exists (go p')
           | GenNode 3 [p'] => patt_mu (go p')
           | _ => patt_bott (* dummy *)
           end
      ).

  refine (inj_countable' enc dec _).
  intros x.
  induction x; simpl; congruence.
Defined.

Section syntax.
    Context {Σ : Signature}.

Fixpoint size (p : Pattern) : nat :=
    match p with
    | patt_app ls rs => 1 + (size ls) + (size rs)
    | patt_imp ls rs => 1 + (size ls) + (size rs)
    | patt_exists p' => 1 + size p'
    | patt_mu p' => 1 + size p'
    | _ => 0
    end.


Fixpoint size' (p : Pattern) : nat :=
    match p with
    | patt_app ls rs => 1 + (size' ls) + (size' rs)
    | patt_imp ls rs => 1 + (size' ls) + (size' rs)
    | patt_exists p' => 1 + size' p'
    | patt_mu p' => 1 + size' p'
    | _ => 1
    end.

  (** The free names of a type are defined as follow.  Notice the
  [exists] and [mu] cases: they do not bind any name. *)

  Definition EVarSet := gset evar.
  Definition SVarSet := gset svar.

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




  (* for bound set variables *)
  Fixpoint no_negative_occurrence_db_b (dbi : db_index) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_sym _ | patt_bott => true
    | patt_bound_svar n => true
    | patt_app ϕ₁ ϕ₂ => no_negative_occurrence_db_b dbi ϕ₁ && no_negative_occurrence_db_b dbi ϕ₂
    | patt_imp ϕ₁ ϕ₂ => no_positive_occurrence_db_b dbi ϕ₁ && no_negative_occurrence_db_b dbi ϕ₂
    | patt_exists ϕ' => no_negative_occurrence_db_b dbi ϕ'
    | patt_mu ϕ' => no_negative_occurrence_db_b (S dbi) ϕ'
    end
  with
  no_positive_occurrence_db_b (dbi : db_index) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_sym _ | patt_bott => true
    | patt_bound_svar n => if decide (n = dbi) is left _ then false else true
    | patt_app ϕ₁ ϕ₂ => no_positive_occurrence_db_b dbi ϕ₁ && no_positive_occurrence_db_b dbi ϕ₂
    | patt_imp ϕ₁ ϕ₂ => no_negative_occurrence_db_b dbi ϕ₁ && no_positive_occurrence_db_b dbi ϕ₂
    | patt_exists ϕ' => no_positive_occurrence_db_b dbi ϕ'
    | patt_mu ϕ' => no_positive_occurrence_db_b (S dbi) ϕ'                                  
    end.

  (* for free element variables *)
  Fixpoint evar_has_positive_occurrence (x : evar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar x' => if decide (x = x') is left _ then true else false
    | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => evar_has_positive_occurrence x ϕ₁ || evar_has_positive_occurrence x ϕ₂
    | patt_imp ϕ₁ ϕ₂ => evar_has_negative_occurrence x ϕ₁ || evar_has_positive_occurrence x ϕ₂
    | patt_exists ϕ' => evar_has_positive_occurrence x ϕ'
    | patt_mu ϕ' => evar_has_positive_occurrence x ϕ'
    end
  with
  evar_has_negative_occurrence (x : evar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => evar_has_negative_occurrence x ϕ₁ || evar_has_negative_occurrence x ϕ₂
    | patt_imp ϕ₁ ϕ₂ => evar_has_positive_occurrence x ϕ₁ || evar_has_negative_occurrence x ϕ₂
    | patt_exists ϕ' => evar_has_negative_occurrence x ϕ'
    | patt_mu ϕ' => evar_has_negative_occurrence x ϕ'
    end.

  (* for free set variables *)
  Fixpoint svar_has_positive_occurrence (X : svar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_svar X' => if decide (X = X') is left _ then true else false
    | patt_free_evar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => svar_has_positive_occurrence X ϕ₁ || svar_has_positive_occurrence X ϕ₂
    | patt_imp ϕ₁ ϕ₂ => svar_has_negative_occurrence X ϕ₁ || svar_has_positive_occurrence X ϕ₂
    | patt_exists ϕ' => svar_has_positive_occurrence X ϕ'
    | patt_mu ϕ' => svar_has_positive_occurrence X ϕ'
    end
  with
  svar_has_negative_occurrence (X : svar) (ϕ : Pattern) : bool :=
    match ϕ with
    | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ | patt_sym _ | patt_bott => false
    | patt_app ϕ₁ ϕ₂ => svar_has_negative_occurrence X ϕ₁ || svar_has_negative_occurrence X ϕ₂
    | patt_imp ϕ₁ ϕ₂ => svar_has_positive_occurrence X ϕ₁ || svar_has_negative_occurrence X ϕ₂
    | patt_exists ϕ' => svar_has_negative_occurrence X ϕ'
    | patt_mu ϕ' => svar_has_negative_occurrence X ϕ'
    end.

  Fixpoint well_formed_positive (phi : Pattern) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar _ => true
    | patt_bound_svar _ => true
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_positive psi1 && well_formed_positive psi2
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_positive psi1 && well_formed_positive psi2
    | patt_exists psi => well_formed_positive psi
    | patt_mu psi => no_negative_occurrence_db_b 0 psi && well_formed_positive psi
    end.
  
  Fixpoint well_formed_closed_mu_aux (phi : Pattern) (max_ind_svar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => true
    | patt_bound_svar n => if decide (n < max_ind_svar) is left _ then true else false
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_closed_mu_aux psi1 max_ind_svar &&
                            well_formed_closed_mu_aux psi2 max_ind_svar
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_closed_mu_aux psi1 max_ind_svar &&
                            well_formed_closed_mu_aux psi2 max_ind_svar
    | patt_exists psi => well_formed_closed_mu_aux psi max_ind_svar
    | patt_mu psi => well_formed_closed_mu_aux psi (S max_ind_svar)
    end.

  Fixpoint well_formed_closed_ex_aux (phi : Pattern) (max_ind_evar : db_index) : bool :=
    match phi with
    | patt_free_evar _ => true
    | patt_free_svar _ => true
    | patt_bound_evar n => if decide (n < max_ind_evar) is left _ then true else false
    | patt_bound_svar n => true
    | patt_sym _ => true
    | patt_app psi1 psi2 => well_formed_closed_ex_aux psi1 max_ind_evar &&
                            well_formed_closed_ex_aux psi2 max_ind_evar
    | patt_bott => true
    | patt_imp psi1 psi2 => well_formed_closed_ex_aux psi1 max_ind_evar &&
                            well_formed_closed_ex_aux psi2 max_ind_evar
    | patt_exists psi => well_formed_closed_ex_aux psi (S max_ind_evar)
    | patt_mu psi => well_formed_closed_ex_aux psi max_ind_evar
    end.
  
  Definition well_formed_closed (phi : Pattern) : bool
    := well_formed_closed_mu_aux phi 0 && well_formed_closed_ex_aux phi 0.

  Lemma well_formed_closed_ex_aux_ind (phi : Pattern) (ind_evar1 ind_evar2 : db_index) :
    ind_evar1 <= ind_evar2 ->
    well_formed_closed_ex_aux phi ind_evar1 = true->
    well_formed_closed_ex_aux phi ind_evar2 = true.
  Proof.
    intros H H0.
    generalize dependent ind_evar1. generalize dependent ind_evar2.
    induction phi; intros ind_evar_2 ind_evar_1 Heqevar H;
      simpl in *; repeat case_match; try (naive_bsolver lia); auto.
    eapply IHphi. 2: eassumption. lia.
  Qed.

  Lemma well_formed_closed_mu_aux_ind (phi : Pattern) (ind_svar1 ind_svar2 : db_index) :
    ind_svar1 <= ind_svar2  ->
    well_formed_closed_mu_aux phi ind_svar1 = true ->
    well_formed_closed_mu_aux phi ind_svar2 = true.
  Proof.
    intros H H1.
    generalize dependent ind_svar1. generalize dependent ind_svar2.
    induction phi; intros ind_svar_2 ind_svar_1 Hleqsvar;
      simpl in *; repeat case_match; try (naive_bsolver lia); auto.
    eapply IHphi. lia.
  Qed.
  
  Definition well_formed (phi : Pattern) := well_formed_positive phi && well_formed_closed phi.



End syntax.