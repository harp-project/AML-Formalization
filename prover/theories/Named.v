From Coq Require Import ssreflect ssrfun ssrbool.

From Equations Require Import Equations.

From stdpp Require Import base pmap gmap fin_maps finite.
From MatchingLogic Require Import Syntax Utils.stdpp_ext StringSignature.

  (* stdpp_ext.v *)
  Lemma drop_notin :
    forall {T : Set} (l : list T) n x, x ∉ l -> x ∉ drop n l.
  Proof.
    induction l; intros; destruct n; simpl; auto.
    apply IHl. set_solver.
  Qed.     
  
  (* stdpp_ext.v *)
  Lemma take_notin :
    forall {T : Set} (l : list T) n x, x ∉ l -> x ∉ take n l.
  Proof.
    induction l; intros; destruct n; simpl; auto. set_solver.
    set_solver.
  Qed.

  (* stdpp_ext.v *)
  Lemma drop_subseteq :
    forall {T : Set} (l : list T) n, drop n l ⊆ l.
  Proof.
    induction l; intros; destruct n; simpl; auto.
    set_solver.
  Qed.     
  
  (* stdpp_ext.v *)
  Lemma take_subseteq :
    forall {T : Set} (l : list T) n, take n l ⊆ l.
  Proof.
    induction l; intros; destruct n; simpl; auto. set_solver.
    set_solver.
  Qed.    

Section named.
  Context
    {Σ : Signature}
  .

  Inductive NamedPattern : Set :=
  | npatt_evar (x : evar)
  | npatt_svar (X : svar)
  | npatt_sym (sigma : symbols)
  | npatt_app (phi1 phi2 : NamedPattern)
  | npatt_bott
  | npatt_imp (phi1 phi2 : NamedPattern)
  | npatt_exists (x : evar) (phi : NamedPattern)
  | npatt_mu (X : svar) (phi : NamedPattern)
  .

Fixpoint nsize' (p : NamedPattern) : nat :=
  match p with
  | npatt_app ls rs => 1 + (nsize' ls) + (nsize' rs)
  | npatt_imp ls rs => 1 + (nsize' ls) + (nsize' rs)
  | npatt_exists _ p' => 1 + nsize' p'
  | npatt_mu _ p' => 1 + nsize' p'
  | _ => 1
  end.

  #[global]
  Instance NamedPattern_eqdec : EqDecision NamedPattern.
  Proof. solve_decision. Defined.

  #[global]
  Instance NamedPattern_countable (sc : Countable symbols) : Countable NamedPattern.
Proof.
  set (enc :=
         fix go p : gen_tree (unit
                              + ((@symbols (@ml_symbols Σ))
                                 + (((@evar variables))
                                    + ((@svar variables)))))%type :=
           match p with
           | npatt_bott => GenLeaf (inl ())
           | npatt_sym s => GenLeaf (inr (inl s))
           | npatt_evar x => GenLeaf (inr (inr (inl x)))
           | npatt_svar X => GenLeaf (inr (inr (inr X)))
           | npatt_app p1 p2 => GenNode 0 [go p1; go p2]
           | npatt_imp p1 p2 => GenNode 1 [go p1; go p2]
           | npatt_exists x p' => GenNode 2 [GenLeaf (inr (inr (inl x))); go p']
           | npatt_mu X p' => GenNode 3 [GenLeaf (inr (inr (inr X))); go p']
           end
      ).

  set (dec :=
         fix go (p : gen_tree (unit
                              + ((@symbols (@ml_symbols Σ))
                                 + (((@evar variables) )
                                    + ((@svar variables)))))%type) : NamedPattern :=
           match p with
           | GenLeaf (inl ()) => npatt_bott
           | GenLeaf (inr (inl s)) => npatt_sym s
           | GenLeaf (inr (inr (inl x))) => npatt_evar x
           | GenLeaf (inr (inr (inr X))) => npatt_svar X
           | GenNode 0 [p1; p2] => npatt_app (go p1) (go p2)
           | GenNode 1 [p1; p2] => npatt_imp (go p1) (go p2)
           | GenNode 2 [nx; p'] =>
            match (go nx) with
            | npatt_evar x => npatt_exists x (go p')
            | _ => npatt_bott (* dummy *)
            end
           | GenNode 3 [nX; p']  =>
            match (go nX) with
            | npatt_svar X => npatt_mu X (go p')
            | _ => npatt_bott (* dummy *)
            end
           | _ => npatt_bott (* dummy *)
           end
      ).

  refine (inj_countable' enc dec _).
  intros x.
  induction x; simpl; congruence.
Defined.

  Fixpoint named_no_negative_occurrence (X : svar) (ϕ : NamedPattern) : bool :=
    match ϕ with
    | npatt_evar _ | npatt_sym _ | npatt_bott => true
    | npatt_svar Y => true
    | npatt_app ϕ₁ ϕ₂ => named_no_negative_occurrence X ϕ₁ && named_no_negative_occurrence X ϕ₂
    | npatt_imp ϕ₁ ϕ₂ => named_no_positive_occurrence X ϕ₁ && named_no_negative_occurrence X ϕ₂
    | npatt_exists _ ϕ' => named_no_negative_occurrence X ϕ'
    | npatt_mu Y ϕ' => 
      match decide (X = Y) with
      | right _ => named_no_negative_occurrence X ϕ'
      | left _ => true
      end
    end
  with
  named_no_positive_occurrence (X : svar) (ϕ : NamedPattern) : bool :=
    match ϕ with
    | npatt_evar _ | npatt_sym _ | npatt_bott => true
    | npatt_svar Y => negb (if decide (X = Y) is left _ then true else false)
    | npatt_app ϕ₁ ϕ₂ => named_no_positive_occurrence X ϕ₁ && named_no_positive_occurrence X ϕ₂
    | npatt_imp ϕ₁ ϕ₂ => named_no_negative_occurrence X ϕ₁ && named_no_positive_occurrence X ϕ₂
    | npatt_exists _ ϕ' => named_no_positive_occurrence X ϕ'
    | npatt_mu Y ϕ' =>
      match decide (X = Y) with
      | right _ => named_no_positive_occurrence X ϕ'
      | left _ => true
      end
    end.

  Fixpoint named_well_formed_positive (phi : NamedPattern) : bool :=
    match phi with
    | npatt_evar _ => true
    | npatt_svar _ => true
    | npatt_sym _ => true
    | npatt_app psi1 psi2 => named_well_formed_positive psi1 && named_well_formed_positive psi2
    | npatt_bott => true
    | npatt_imp psi1 psi2 => named_well_formed_positive psi1 && named_well_formed_positive psi2
    | npatt_exists _ psi => named_well_formed_positive psi
    | npatt_mu X psi => named_no_negative_occurrence X psi && named_well_formed_positive psi
    end.

  Definition named_well_formed := named_well_formed_positive.

  Inductive Named_Application_context : Type :=
  | nbox
  | nctx_app_l (cc : Named_Application_context) (p : NamedPattern) (Prf : named_well_formed p)
  | nctx_app_r (p : NamedPattern) (cc : Named_Application_context) (Prf : named_well_formed p)
  .

  Fixpoint named_subst_ctx (C : Named_Application_context) (p : NamedPattern)
    : NamedPattern :=
    match C with
    | nbox => p
    | @nctx_app_l C' p' prf => npatt_app (named_subst_ctx C' p) p'
    | @nctx_app_r p' C' prf => npatt_app p' (named_subst_ctx C' p)
    end.

  Definition EVarMap := gmap db_index evar.
  Definition SVarMap := gmap db_index svar.

  Fixpoint named_free_evars (phi : NamedPattern) : EVarSet :=
    match phi with
    | npatt_evar x => singleton x
    | npatt_svar X => empty
    | npatt_sym sigma => empty
    | npatt_app phi1 phi2 => union (named_free_evars phi1) (named_free_evars phi2)
    | npatt_bott => empty
    | npatt_imp phi1 phi2 => union (named_free_evars phi1) (named_free_evars phi2)
    | npatt_exists x phi => difference (named_free_evars phi) (singleton x)
    | npatt_mu X phi => named_free_evars phi
    end.

  Fixpoint named_free_svars (phi : NamedPattern) : SVarSet :=
    match phi with
    | npatt_evar x => empty
    | npatt_svar X => singleton X
    | npatt_sym sigma => empty
    | npatt_app phi1 phi2 => union (named_free_svars phi1) (named_free_svars phi2)
    | npatt_bott => empty
    | npatt_imp phi1 phi2 => union (named_free_svars phi1) (named_free_svars phi2)
    | npatt_exists x phi => named_free_svars phi
    | npatt_mu X phi => difference (named_free_svars phi) (singleton X)
    end.


  Fixpoint named_bound_evars (phi : NamedPattern) : EVarSet :=
    match phi with
    | npatt_app phi1 phi2 => (named_bound_evars phi1) ∪ (named_bound_evars phi2)
    | npatt_imp phi1 phi2 => (named_bound_evars phi1) ∪ (named_bound_evars phi2)
    | npatt_exists x phi => (named_bound_evars phi) ∪ {[x]}
    | npatt_mu X phi => named_bound_evars phi
    | _ => empty
    end.

  Fixpoint named_bound_svars (phi : NamedPattern) : SVarSet :=
    match phi with
    | npatt_app phi1 phi2 => (named_bound_svars phi1) ∪ (named_bound_svars phi2)
    | npatt_imp phi1 phi2 => (named_bound_svars phi1) ∪ (named_bound_svars phi2)
    | npatt_exists x phi => named_bound_svars phi
    | npatt_mu X phi => (named_bound_svars phi) ∪ {[X]}
    | _ => empty
    end.

  Definition named_evars phi := named_free_evars phi ∪ named_bound_evars phi.
  Definition named_svars phi := named_free_svars phi ∪ named_bound_svars phi.
  Arguments named_evars / phi.
  Arguments named_svars / phi.

  Lemma named_free_evars_subseteq_named_evars ϕ:
    named_free_evars ϕ ⊆ named_evars ϕ.
  Proof.
    set_solver.
  Qed.

  Lemma named_free_svars_subseteq_named_svars ϕ:
    named_free_svars ϕ ⊆ named_svars ϕ.
  Proof.
    set_solver.
  Qed.

  CoInductive EVarGen := mkEvarGen {
    eg_get : gset evar -> evar ;
    eg_get_correct : forall evs, eg_get evs ∉ evs ;
    eg_next : gset evar -> EVarGen ;
  }.

  Program CoFixpoint default_EVarGen avoid : EVarGen := {|
    eg_get := fun evs => evar_fresh (elements (avoid ∪ evs)) ;
    eg_next := fun evs => default_EVarGen (avoid ∪ evs) ;
  |}.
  Next Obligation.
    intros avoid evs. simpl.
    assert (H: evar_fresh (elements (avoid ∪ evs)) ∉ (avoid ∪ evs)).
    {
      apply set_evar_fresh_is_fresh'.
    }
    set_solver.
  Qed.

  (* CoInductive SVarGen := mkSvarGen {
    sg_get : gset svar -> svar ;
    sg_get_correct : forall svs, sg_get svs ∉ svs ;
    sg_next : gset svar -> SVarGen ;
  }.
  Print SVarGen.

  Program CoFixpoint default_SVarGen avoid : SVarGen := {|
    sg_get := fun svs => svar_fresh (elements (avoid ∪ svs)) ;
    sg_next := fun svs => default_SVarGen (avoid ∪ svs) ;
  |}.
  Next Obligation.
    intros avoid svs. simpl.
    assert (H: svar_fresh (elements (avoid ∪ svs)) ∉ (avoid ∪ svs)).
    {
      apply set_svar_fresh_is_fresh'.
    }
    set_solver.
  Qed.

  Definition eg_fresh (eg : EVarGen) (ϕ : NamedPattern) : evar
    := eg_get eg (named_free_evars ϕ).

  Lemma eg_fresh_correct (eg : EVarGen) (ϕ : NamedPattern) :
    (eg_fresh eg ϕ) ∉ (named_free_evars ϕ)
  .
  Proof.
    apply eg_get_correct.
  Qed.

  Definition eg_update (eg : EVarGen) (ϕ : NamedPattern) : EVarGen
    := eg_next eg (named_free_evars ϕ)
  .

  Definition sg_fresh (sg : SVarGen) (ϕ : NamedPattern) : svar
    := sg_get sg (named_free_svars ϕ)
  .

  Lemma sg_getf_correct (sg : SVarGen) (ϕ : NamedPattern) :
    (sg_getf sg ϕ) ∉ (named_free_svars ϕ)
  .
  Proof.
    apply sg_get_correct.
  Qed.

  Definition sg_nextf (sg : SVarGen) (ϕ : NamedPattern) : SVarGen
    := sg_next sg (named_free_svars ϕ)
  . *)


  (* phi[y/x] *)
  Fixpoint rename_free_evar (phi : NamedPattern) (y x : evar) : NamedPattern :=
  match phi with
  | npatt_evar x' => if decide (x = x') is left _ then npatt_evar y else npatt_evar x'
  | npatt_svar X => npatt_svar X
  | npatt_sym sigma => npatt_sym sigma
  | npatt_app phi1 phi2 => npatt_app (rename_free_evar phi1 y x)
                                     (rename_free_evar phi2 y x)
  | npatt_bott => npatt_bott
  | npatt_imp phi1 phi2 => npatt_imp (rename_free_evar phi1 y x)
                                     (rename_free_evar phi2 y x)
  | npatt_exists x' phi'
    => match (decide (x = x')) with
       | left _ => npatt_exists x' phi' (* no-op *)
       | right _ => (
          npatt_exists x' (rename_free_evar phi' y x)
         )
       end
  | npatt_mu X phi'
    => npatt_mu X (rename_free_evar phi' y x)
  end.

  Lemma nsize'_rename_free_evar (ϕ : NamedPattern) (y x : evar) :
    nsize' (rename_free_evar ϕ y x) = nsize' ϕ
  .
  Proof.
    induction ϕ; cbn; repeat case_match; cbn; try reflexivity; lia.
  Qed.

  Lemma rename_free_evar_id (ϕ : NamedPattern) (y x : evar) :
    x ∉ named_free_evars ϕ ->
    rename_free_evar ϕ y x = ϕ
  .
  Proof.
    move: y x.
    induction ϕ; cbn; intros y x' H; try reflexivity.
    {
      destruct (decide (x' = x)).
      { subst. exfalso. set_solver. }
      { reflexivity. }
    }
    {
      rewrite IHϕ1. set_solver.
      rewrite IHϕ2. set_solver.
      reflexivity.
    }
    {
      rewrite IHϕ1. set_solver.
      rewrite IHϕ2. set_solver.
      reflexivity.
    }
    {
      destruct (decide (x' = x));[reflexivity|].
      rewrite IHϕ. set_solver. reflexivity.
    }
    {
      rewrite IHϕ. assumption. reflexivity.
    }
  Qed.


  Lemma rename_free_evar_chain (ϕ : NamedPattern) (z y x : evar) :
    y ∉ named_evars ϕ ->
    rename_free_evar (rename_free_evar ϕ y x) z y
    = rename_free_evar ϕ z x.
  Proof.
    move: z y x.
    remember (nsize' ϕ) as sz.
    assert (Hsz: nsize' ϕ <= sz) by lia.
    clear Heqsz.
    move: ϕ Hsz.
    induction sz; intros ϕ Hsz.
    { destruct ϕ; cbn in Hsz; lia. }
    destruct ϕ; intros z y x' Hfry; cbn in Hsz; cbn in Hfry; cbn; try reflexivity.
    {
      destruct (decide (x' = x)).
      { subst. cbn. rewrite decide_eq_same. reflexivity. }
      { cbn. destruct (decide (y = x));[|reflexivity].
        subst. cbn in Hfry. exfalso. clear -Hfry. set_solver.
      }
    }
    {
      rewrite IHsz.
      { lia. }
      { set_solver. }
      rewrite IHsz.
      { lia. }
      { set_solver. }
      reflexivity.
    }
    {
      rewrite IHsz.
      { lia. }
      { set_solver. }
      rewrite IHsz.
      { lia. }
      { set_solver. }
      reflexivity.
    }
    {
      destruct (decide (x' = x)).
      {
        subst. cbn.
        destruct (decide (y = x));[reflexivity|].
        cbn.
        rewrite rename_free_evar_id.
        { 
          pose proof (named_free_evars_subseteq_named_evars ϕ).  
          set_solver.
        }
        reflexivity.
      }
      {
        cbn.
        destruct (decide (y = x)).
        { subst. exfalso. clear -Hfry. set_solver. }
        {
          rewrite IHsz.
          { lia. }
          { set_solver. }
          reflexivity.
        }
      }
    }
    {
      rewrite IHsz.
      { lia. }
      { assumption. }
      reflexivity.
    }
  Qed.

  Lemma inclusion_evar_seq :
    forall (n n' : nat) (evs : EVarSet), n <= n' ->
      evar_fresh_seq evs n ⊆ evar_fresh_seq evs n'.
  Proof.
    induction n; intros n' evs H.
    * set_solver.
    * destruct n'.
      - lia.
      - simpl.
        specialize (IHn n' ({[evar_fresh_s evs]} ∪ evs) ltac:(lia)). set_solver.
  Defined.

(*   Lemma rename_cancel :
    forall φ x y,
    y ∉ named_evars φ ->
    rename_free_evar (rename_free_evar φ y x) x y = φ.
  Proof.
    intro φ.
    remember (nsize' φ) as sz.
    assert (Hsz: nsize' φ <= sz) by lia.
    clear Heqsz.
    move: φ Hsz.
    induction sz; intros φ Hsz x y Hin; destruct φ; simpl; auto; simpl in Hsz; try lia.
    * case_match; simpl.
      - case_match; congruence.
      - case_match; auto. subst. set_solver.
    * rewrite IHsz. 3: rewrite IHsz.
      1, 3: lia.
      1-2: set_solver.
      reflexivity.
    * rewrite IHsz. 3: rewrite IHsz.
      1, 3: lia.
      1-2: set_solver.
      reflexivity.
    * case_match; simpl; case_match; subst; auto.
      - 
  Qed. *)

  Lemma rename_free_evar_same :
    forall ϕ x, rename_free_evar ϕ x x = ϕ.
  Proof.
    induction ϕ; intros y; simpl; auto.
    * case_match; subst; auto.
    * now rewrite IHϕ1 IHϕ2.
    * now rewrite IHϕ1 IHϕ2.
    * case_match; auto. now rewrite IHϕ.
    * now rewrite IHϕ.
  Qed.

  (* phi[Y/X] *)
  Fixpoint rename_free_svar (phi : NamedPattern) (Y X : svar) : NamedPattern :=
  match phi with
  | npatt_svar X' => if decide (X = X') is left _ then npatt_svar Y else npatt_svar X'
  | npatt_evar x => npatt_evar x
  | npatt_sym sigma => npatt_sym sigma
  | npatt_app phi1 phi2 => npatt_app (rename_free_svar phi1 Y X)
                                     (rename_free_svar phi2 Y X)
  | npatt_bott => npatt_bott
  | npatt_imp phi1 phi2 => npatt_imp (rename_free_svar phi1 Y X)
                                     (rename_free_svar phi2 Y X)
  | npatt_mu X' phi'
    => match (decide (X = X')) with
       | left _ => npatt_mu X' phi' (* no-op *)
       | right _ => (
          npatt_mu X' (rename_free_svar phi' Y X)
         )
       end
  | npatt_exists x phi'
    => npatt_exists x (rename_free_svar phi' Y X)
  end.

  Lemma nsize'_rename_free_svar (ϕ : NamedPattern) (Y X : svar) :
    nsize' (rename_free_svar ϕ Y X) = nsize' ϕ
  .
  Proof.
    induction ϕ; cbn; repeat case_match; cbn; try reflexivity; lia.
  Qed.

  Lemma rename_free_svar_id (ϕ : NamedPattern) (Y X : svar) :
    X ∉ named_free_svars ϕ ->
    rename_free_svar ϕ Y X = ϕ
  .
  Proof.
    move: Y X.
    induction ϕ; cbn; intros Y X' H; try reflexivity.
    {
      destruct (decide (X' = X)).
      { subst. exfalso. set_solver. }
      { reflexivity. }
    }
    {
      rewrite IHϕ1. set_solver.
      rewrite IHϕ2. set_solver.
      reflexivity.
    }
    {
      rewrite IHϕ1. set_solver.
      rewrite IHϕ2. set_solver.
      reflexivity.
    }
    {
      rewrite IHϕ. assumption. reflexivity.
    }
    {
      destruct (decide (X' = X));[reflexivity|].
      rewrite IHϕ. set_solver. reflexivity.
    }
  Qed.

  Lemma rename_free_svar_chain (ϕ : NamedPattern) (Z Y X : svar) :
    Y ∉ named_svars ϕ ->
    rename_free_svar (rename_free_svar ϕ Y X) Z Y
    = rename_free_svar ϕ Z X.
  Proof.
    move: Z Y X.
    remember (nsize' ϕ) as sz.
    assert (Hsz: nsize' ϕ <= sz) by lia.
    clear Heqsz.
    move: ϕ Hsz.
    induction sz; intros ϕ Hsz.
    { destruct ϕ; cbn in Hsz; lia. }
    destruct ϕ; intros Z Y X' HfrY; cbn in Hsz; cbn in HfrY; cbn; try reflexivity.
    {
      destruct (decide (X' = X)).
      { subst. cbn. rewrite decide_eq_same. reflexivity. }
      { cbn. destruct (decide (Y = X));[|reflexivity].
        subst. cbn in HfrY. exfalso. clear -HfrY. set_solver.
      }
    }
    {
      rewrite IHsz.
      { lia. }
      { set_solver. }
      rewrite IHsz.
      { lia. }
      { set_solver. }
      reflexivity.
    }
    {
      rewrite IHsz.
      { lia. }
      { set_solver. }
      rewrite IHsz.
      { lia. }
      { set_solver. }
      reflexivity.
    }
    {
      rewrite IHsz.
      { lia. }
      { assumption. }
      reflexivity.
    }
    {
      destruct (decide (X' = X)).
      {
        subst. cbn.
        destruct (decide (Y = X));[reflexivity|].
        cbn.
        rewrite rename_free_svar_id.
        { 
          pose proof (named_free_svars_subseteq_named_svars ϕ).  
          set_solver.
        }
        reflexivity.
      }
      {
        cbn.
        destruct (decide (Y = X)).
        { subst. exfalso. clear -HfrY. set_solver. }
        {
          rewrite IHsz.
          { lia. }
          { set_solver. }
          reflexivity.
        }
      }
    }
  Qed.

  Lemma rename_free_svar_same :
    forall ϕ X, rename_free_svar ϕ X X = ϕ.
  Proof.
    induction ϕ; intros Y; simpl; auto.
    * case_match; subst; auto.
    * now rewrite IHϕ1 IHϕ2.
    * now rewrite IHϕ1 IHϕ2.
    * now rewrite IHϕ.
    * case_match; auto. now rewrite IHϕ.
  Qed.

  Section blacklist_translation.

  Definition EvarBlacklist := gset evar.
  Definition SvarBlacklist := gset svar.

  Fixpoint shift_evars (eg : EvarBlacklist) (ϕ : NamedPattern) : NamedPattern :=
  match ϕ with
  | npatt_imp ϕ1 ϕ2 =>  npatt_imp (shift_evars eg ϕ1) (shift_evars eg ϕ2)
  | npatt_app ϕ1 ϕ2 => npatt_app (shift_evars eg ϕ1) (shift_evars eg ϕ2)
  | npatt_exists x ϕ =>
      let freshx := evar_fresh (elements eg) in
        npatt_exists freshx (rename_free_evar (shift_evars ({[freshx]} ∪ eg) ϕ) x freshx)
  | npatt_mu X ϕ => npatt_mu X (shift_evars eg ϕ)
  | ψ => ψ
  end.

  Fixpoint shift_svars (sg : SvarBlacklist) (ϕ : NamedPattern) : NamedPattern :=
  match ϕ with
  | npatt_imp ϕ1 ϕ2 => npatt_imp (shift_svars sg ϕ1) (shift_svars sg ϕ2)
  | npatt_app ϕ1 ϕ2 => npatt_app (shift_svars sg ϕ1) (shift_svars sg ϕ2)
  | npatt_exists x ϕ => npatt_exists x (shift_svars sg ϕ)
  | npatt_mu X ϕ =>
      let freshX := svar_fresh (elements sg) in
        npatt_mu freshX (rename_free_svar (shift_svars ({[freshX]} ∪ sg) ϕ) X freshX)
  | ψ => ψ
  end.

  Equations? named_evar_subst (eg : EvarBlacklist)
    (ϕ : NamedPattern) (x : evar) (ψ : NamedPattern)  : NamedPattern 
    by wf (nsize' ϕ) lt :=
    named_evar_subst eg (npatt_evar y) x ψ with (decide (x = y)) => {
      | left _  := shift_evars eg ψ (* shifts the bound names in ψ *)
      | right _ := npatt_evar y
    };
    named_evar_subst eg (npatt_imp ϕ1 ϕ2) x ψ :=
      npatt_imp (named_evar_subst eg ϕ1 x ψ) (named_evar_subst eg ϕ2 x ψ);
    named_evar_subst eg (npatt_app ϕ1 ϕ2) x ψ :=
      npatt_app  (named_evar_subst eg ϕ1 x ψ) (named_evar_subst eg ϕ2 x ψ);
    named_evar_subst eg (npatt_exists y ϕ) x ψ :=
      let freshy := evar_fresh (elements eg) in
        npatt_exists freshy (named_evar_subst ({[freshy]} ∪ eg) (rename_free_evar ϕ y freshy) x ψ);
    named_evar_subst eg (npatt_mu Y ϕ) x ψ := npatt_mu Y (named_evar_subst eg ϕ x ψ);
    named_evar_subst _ ψ _ _ := ψ.
  Proof.
    all: simpl; try lia.
    rewrite nsize'_rename_free_evar. lia.
  Defined.

  Equations? named_svar_subst (sg : SvarBlacklist)
    (ϕ : NamedPattern) (X : svar) (ψ : NamedPattern)  : NamedPattern 
    by wf (nsize' ϕ) lt :=
    named_svar_subst sg (npatt_svar Y) X ψ with (decide (X = Y)) => {
      | left _  := shift_svars sg ψ (* shifts the bound names in ψ *)
      | right _ := npatt_svar Y
    };
    named_svar_subst sg (npatt_imp ϕ1 ϕ2) X ψ :=
      npatt_imp (named_svar_subst sg ϕ1 X ψ) (named_svar_subst sg ϕ2 X ψ);
    named_svar_subst sg (npatt_app ϕ1 ϕ2) X ψ :=
      npatt_app  (named_svar_subst sg ϕ1 X ψ) (named_svar_subst sg ϕ2 X ψ);
    named_svar_subst sg (npatt_exists y ϕ) X ψ := npatt_exists y (named_svar_subst sg ϕ X ψ);
    named_svar_subst sg (npatt_mu Y ϕ) X ψ := 
      let freshY := svar_fresh (elements sg) in
       npatt_mu freshY (named_svar_subst ({[freshY]} ∪ sg) (rename_free_svar ϕ Y freshY) X ψ);
    named_svar_subst _ ψ _ _ := ψ.
  Proof.
    all: simpl; try lia.
    rewrite nsize'_rename_free_svar. lia.
  Defined.

  Fixpoint iterate {A : Type} (f : A -> A) (n : nat) (a : A) :=
  match n with
    | 0 => a
    | S n' => f (iterate f n' a)
  end.

  Equations? translate (eg : EvarBlacklist) (sg : SvarBlacklist) (ϕ : Pattern) : NamedPattern
    by wf (size' ϕ) lt :=
    translate eg sg (patt_bound_evar n) :=
      npatt_evar (evar_fresh (elements (iterate (fun eg => {[evar_fresh (elements eg)]} ∪ eg) n eg)));
    translate eg sg (patt_bound_svar N) :=
      npatt_svar (svar_fresh (elements (iterate (fun sg => {[svar_fresh (elements sg)]} ∪ sg) N sg)));
    translate _  _ (patt_free_evar x)   := npatt_evar x;
    translate _  _ (patt_free_svar X)   := npatt_svar X;
    translate _  _ (patt_sym s)         := npatt_sym s;
    translate _  _ patt_bott            := npatt_bott;
    translate eg sg (patt_imp ϕ1 ϕ2)    := npatt_imp (translate eg sg ϕ1) (translate eg sg ϕ2);
    translate eg sg (patt_app ϕ1 ϕ2)    := npatt_app (translate eg sg ϕ1) (translate eg sg ϕ2);
    translate eg sg (patt_exists ϕ)     :=
      let freshx := evar_fresh (elements eg) in
        npatt_exists freshx (translate ({[freshx]} ∪ eg) sg (evar_open freshx 0 ϕ));
    translate eg sg (patt_mu ϕ)         :=
    let freshX := svar_fresh (elements sg) in
      npatt_mu freshX (translate eg ({[freshX]} ∪ sg) (svar_open freshX 0 ϕ)).
  Proof.
    all: simpl; try lia.
    1: rewrite evar_open_size'; lia.
    1: rewrite svar_open_size'; lia.
  Defined.

  Lemma shift_translate :
    forall ϕ eg sg,
    shift_evars eg (translate eg sg ϕ) = (translate eg sg ϕ).
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; intros ϕ Hs eg sg; destruct ϕ; simpl in Hs; try lia; simpl; simp translate; auto.
    * simpl. rewrite IHs. 2: rewrite IHs. 1-2: lia. reflexivity.
    * simpl. rewrite IHs. 2: rewrite IHs. 1-2: lia. reflexivity.
    * simpl. rewrite rename_free_evar_same. rewrite IHs.
      rewrite evar_open_size'. lia. reflexivity.
    * simpl. rewrite IHs. rewrite svar_open_size'. lia. reflexivity.
  Defined.

  Lemma rename_shift :
    forall ϕ x y eg,
      {[x; y]} ∪ named_free_evars ϕ ⊆ eg ->
      rename_free_evar (shift_evars eg ϕ) x y = shift_evars eg (rename_free_evar ϕ x y).
  Proof.
    intros ϕ. remember (nsize' ϕ) as s.
    assert (nsize' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; intros ϕ Hs x y eg; destruct ϕ; simpl in Hs; try lia; auto.
    * simpl. case_match; auto.
    (* * simpl. rewrite IHs. lia. 2: rewrite IHs; now try lia.
    * simpl. rewrite IHs. lia. rewrite IHs; now try lia.
    * simpl. case_match.
      - rewrite IHs. lia. *)
    Abort.

  Lemma shift_evars_irrelevant :
    forall ψ eg eg' eg'' sg,
      well_formed ψ ->
      shift_evars eg (translate eg'' sg ψ) =
      shift_evars eg (translate eg' sg ψ).
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; intros ϕ Hs eg eg' eg'' sg Hwf; destruct ϕ; simpl in Hs; try lia; auto.
    * wf_auto2.
    * simp translate. simpl. erewrite (IHs ϕ1), (IHs ϕ2). reflexivity. 1, 3: lia.
      all: wf_auto2.
    * simp translate. simpl. erewrite (IHs ϕ1), (IHs ϕ2). reflexivity. 1, 3: lia.
      all: wf_auto2.
    * simp translate. simpl.
      remember (evar_fresh _) as x.
      remember (evar_fresh (elements eg')) as x'.
      remember (evar_fresh (elements eg'')) as x''. f_equal.
    Abort.

  Lemma named_evar_subst_irrelevant :
    forall ϕ x ψ eg eg' eg'' sg,
      named_evar_subst eg ϕ x (translate eg'' sg ψ) =
      named_evar_subst eg ϕ x (translate eg' sg ψ).
  Proof.
    intros ϕ. remember (nsize' ϕ) as s.
    assert (nsize' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; intros ϕ Hs x ψ eg eg' eg'' sg; destruct ϕ; simpl in Hs; try lia; auto.
    * simp named_evar_subst. destruct decide; simpl; auto.
  Abort.

  Lemma named_svar_subst_irrelevant :
    forall x ϕ ψ eg sg sg' sg'',
      named_svar_subst sg ϕ x (translate eg sg' ψ) =
      named_svar_subst sg ϕ x (translate eg sg'' ψ).
  Proof.

  Abort.

  Theorem translate_free_evar_subst :
    forall x ϕ ψ eg sg,
      {[x]} ∪ free_evars ψ ∪ free_evars ϕ ⊆ eg ->
      well_formed ψ ->
      translate eg sg (free_evar_subst ψ x ϕ) =
      named_evar_subst eg (translate eg sg ϕ) x (translate eg sg ψ).
  Proof.
    intros x ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H x.
    induction s; intros ϕ Hsz x ψ eg sg Hfree Hwf; destruct ϕ; simpl in Hsz; try lia; simpl.
    * simp translate. simp named_evar_subst. case_match; simpl. by rewrite shift_translate. by simp translate.
    * simp translate. by simp named_evar_subst.
    * simp translate. remember (evar_fresh _) as y. simp named_evar_subst.
      assert (x <> y). {
        apply X_eq_evar_fresh_impl_X_notin_S in Heqy. clear -Heqy Hfree.
        induction n; simpl in Heqy. set_solver.
        apply IHn; set_solver.
      }
      destruct decide; simpl; auto. congruence.
    * simp translate. remember (svar_fresh _) as Y.
      by simp named_evar_subst.
    * by simp translate.
    * simp translate. simp named_evar_subst. rewrite IHs. 4: rewrite IHs.
      all: auto; try lia; set_solver.
    * by auto.
    * simp translate. simp named_evar_subst. rewrite IHs. 4: rewrite IHs.
    all: auto; try lia; set_solver.
    * simp translate. simpl. simp named_evar_subst. simpl.
      remember (evar_fresh _) as y. rewrite rename_free_evar_same.
      rewrite evar_open_free_evar_subst_swap; auto.
      apply X_eq_evar_fresh_impl_X_notin_S in Heqy. set_solver.
      rewrite IHs; auto.
      - rewrite evar_open_size'. lia.
      - pose proof (free_evars_evar_open ϕ y 0). set_solver.
      - f_equal. admit.
    * simp translate. simp named_evar_subst. simpl.
      remember (svar_fresh _) as Y.
      unfold svar_open. rewrite -free_evar_subst_bsvar_subst. wf_auto2.
      unfold evar_is_fresh_in. set_solver. rewrite IHs.
      - rewrite svar_open_size'. lia.
      - pose proof (free_evars_svar_open ϕ 0 Y). set_solver.
      - assumption.
      - admit.
    Abort.

  End blacklist_translation.

  Section whitelist_translation.

  Equations? standard_evar_subst 
    (ϕ : NamedPattern) (x : evar) (ψ : NamedPattern)  : NamedPattern 
    by wf (nsize' ϕ) lt :=
    standard_evar_subst (npatt_evar y) x ψ with (decide (x = y)) => {
      | left _  := ψ
      | right _ := npatt_evar y
    };
    standard_evar_subst (npatt_imp ϕ1 ϕ2) x ψ :=
      npatt_imp (standard_evar_subst ϕ1 x ψ) (standard_evar_subst ϕ2 x ψ);
    standard_evar_subst (npatt_app ϕ1 ϕ2) x ψ :=
      npatt_app  (standard_evar_subst ϕ1 x ψ) (standard_evar_subst ϕ2 x ψ);
    standard_evar_subst (npatt_exists y ϕ) x ψ with (decide (x = y)) => {
      | left _  := npatt_exists y ϕ
      | right _ with 
        (decide (y ∈ named_free_evars ψ /\ x ∈ named_free_evars ϕ)) => { 
        | left _  := let z := evar_fresh (elements ({[x]} ∪ named_free_evars ϕ ∪ named_free_evars ψ)) in
          npatt_exists z (standard_evar_subst (rename_free_evar ϕ y z) x ψ)
        | right _ := npatt_exists y (standard_evar_subst ϕ x ψ)
      }
    };
    standard_evar_subst (npatt_mu Y ϕ) x ψ := npatt_mu Y (standard_evar_subst ϕ x ψ);
    standard_evar_subst ϕ _ _ := ϕ.
  Proof.
    all: simpl; try lia.
    rewrite nsize'_rename_free_evar. lia.
  Defined.

  Equations? standard_svar_subst 
    (ϕ : NamedPattern) (C : svar) (ψ : NamedPattern)  : NamedPattern 
    by wf (nsize' ϕ) lt :=
    standard_svar_subst (npatt_svar Y) X ψ with (decide (X = Y)) => {
      | left _  := ψ
      | right _ := npatt_svar Y
    };
    standard_svar_subst (npatt_imp ϕ1 ϕ2) X ψ :=
      npatt_imp (standard_svar_subst ϕ1 X ψ) (standard_svar_subst ϕ2 X ψ);
    standard_svar_subst (npatt_app ϕ1 ϕ2) X ψ :=
      npatt_app  (standard_svar_subst ϕ1 X ψ) (standard_svar_subst ϕ2 X ψ);
    standard_svar_subst (npatt_mu Y ϕ) X ψ with (decide (X = Y)) => {
      | left _  := npatt_mu Y ϕ
      | right _ with
        (decide (Y ∈ named_free_svars ψ /\ X ∈ named_free_svars ϕ)) => { 
        | left _  := let Z := svar_fresh (elements ({[X]} ∪ named_free_svars ϕ ∪ named_free_svars ψ)) in
          npatt_mu Z (standard_svar_subst (rename_free_svar ϕ Y Z) X ψ)
        | right _ := npatt_mu Y (standard_svar_subst ϕ X ψ)
      }
    };
    standard_svar_subst (npatt_exists y ϕ) x ψ := npatt_exists y (standard_svar_subst ϕ x ψ);
    standard_svar_subst ϕ _ _ := ϕ.
  Proof.
    all: simpl; try lia.
    rewrite nsize'_rename_free_svar. lia.
  Defined.

  Fixpoint count_ebinders (ϕ : Pattern) : nat :=
    match ϕ with
    | patt_app ϕ1 ϕ2 => count_ebinders ϕ1 + count_ebinders ϕ2
    | patt_imp ϕ1 ϕ2 => count_ebinders ϕ1 + count_ebinders ϕ2
    | patt_exists ϕ => 1 + count_ebinders ϕ
    | patt_mu ϕ => count_ebinders ϕ
    | _ => 0
    end.
  Fixpoint count_sbinders (ϕ : Pattern) : nat :=
    match ϕ with
    | patt_app ϕ1 ϕ2 => count_sbinders ϕ1 + count_sbinders ϕ2
    | patt_imp ϕ1 ϕ2 => count_sbinders ϕ1 + count_sbinders ϕ2
    | patt_exists ϕ => count_sbinders ϕ
    | patt_mu ϕ => 1 + count_sbinders ϕ
    | _ => 0
    end.

  (* We use option type to check that a sufficient number of names were given.
    NOTE: use None for dangling indices too?
    NOTE: do not use option type, because then inversion would be needed in the proofs,
    which is disallowed on Set. *)
  Equations? namify (eg : EvarBlacklist) (sg : SvarBlacklist) (evars : list evar) (svars : list svar) (ϕ : Pattern) : NamedPattern
    by wf (size' ϕ) lt :=
    namify eg sg _ _ (patt_bound_evar n) :=
      npatt_evar (evar_fresh (elements (iterate (fun eg => {[evar_fresh (elements eg)]} ∪ eg) n eg)));
    namify eg sg _ _ (patt_bound_svar N) :=
      npatt_svar (svar_fresh (elements (iterate (fun sg => {[svar_fresh (elements sg)]} ∪ sg) N sg)));
    namify _  _ _ _ (patt_free_evar x)   := npatt_evar x;
    namify _  _ _ _ (patt_free_svar X)   := npatt_svar X;
    namify _  _ _ _ (patt_sym s)         := npatt_sym s;
    namify _  _ _ _ patt_bott            := npatt_bott;
    namify eg sg evars svars (patt_imp ϕ1 ϕ2) :=
      match namify eg sg (take (count_ebinders ϕ1) evars) (take (count_sbinders ϕ1) svars) ϕ1,
            namify eg sg (drop (count_ebinders ϕ1) evars) (drop (count_sbinders ϕ1) svars) ϕ2 with
      | ϕ1', ϕ2' => npatt_imp ϕ1' ϕ2'
      end;
    namify eg sg evars svars (patt_app ϕ1 ϕ2) :=
      match namify eg sg (take (count_ebinders ϕ1) evars) (take (count_sbinders ϕ1) svars) ϕ1,
            namify eg sg (drop (count_ebinders ϕ1) evars) (drop (count_sbinders ϕ1) svars) ϕ2 with
      | ϕ1', ϕ2' => npatt_app ϕ1' ϕ2'
      end;
    namify eg sg (y :: evars) svars (patt_exists ϕ) :=
      match namify eg sg evars svars (evar_open y 0 ϕ) with
      | ϕ' => npatt_exists y ϕ'
      end;
    namify eg sg evars (Y :: svars) (patt_mu ϕ) :=
      match namify eg sg evars svars (svar_open Y 0 ϕ) with
      | ϕ' => npatt_mu Y ϕ'
      end;
    namify eg sg [] svars (patt_exists ϕ) :=
      let y := evar_fresh (elements eg) in
      match namify ({[y]} ∪ eg) sg [] svars (evar_open y 0 ϕ) with
      | ϕ' => npatt_exists y ϕ'
      end;
    namify eg sg evars [] (patt_mu ϕ) :=
      let Y := svar_fresh (elements sg) in
      match namify eg ({[Y]} ∪ sg) evars [] (svar_open Y 0 ϕ) with
      | ϕ' => npatt_mu Y ϕ'
      end.
  Proof.
    all: simpl; try lia.
    1,2: rewrite evar_open_size'; lia.
    1,2: rewrite svar_open_size'; lia.
  Defined.

  (* Pattern.v *)
  Lemma negative_occ_svar_open :
    forall ϕ n x m,
      m <= n ->
      no_negative_occurrence_db_b (S n) ϕ ->
      no_negative_occurrence_db_b n (svar_open x m ϕ)
  with positive_occ_svar_open :
    forall ϕ n x m,
      m <= n ->
      no_positive_occurrence_db_b (S n) ϕ ->
      no_positive_occurrence_db_b n (svar_open x m ϕ).
  Proof.
    {
      induction ϕ; intros; trivial.
      * cbn. case_match; cbn; auto.
      * cbn in H0. move: H0 => /andP [H0_1 H0_2].
        cbn. rewrite IHϕ1; auto. rewrite IHϕ2; auto.
      * move: H0 => /andP [H0_1 H0_2].
        cbn. rewrite IHϕ2; auto. cbn in positive_occ_svar_open.
        apply (positive_occ_svar_open ϕ1 n x m) in H0_1; auto.
      * cbn. rewrite IHϕ; auto.
      * cbn. rewrite IHϕ; auto. lia.
    }
    {
      induction ϕ; intros; trivial.
      * cbn. case_match; cbn; auto; case_match; auto; try lia.
        cbn in H0. case_match; try lia. congruence.
      * cbn in H0. move: H0 => /andP [H0_1 H0_2].
        cbn. rewrite IHϕ1; auto. rewrite IHϕ2; auto.
      * move: H0 => /andP [H0_1 H0_2].
        cbn. rewrite IHϕ2; auto. cbn in negative_occ_svar_open.
        apply (negative_occ_svar_open ϕ1 n x m) in H0_1; auto.
      * cbn. rewrite IHϕ; auto.
      * cbn. rewrite IHϕ; auto. lia.
    }
  Qed.

  Theorem Private_no_negatives_namify :
    forall ϕ n,
    (no_negative_occurrence_db_b n ϕ ->
    (forall eg sg evars svars X, X ∉ free_svars ϕ ->
    X ∈ sg ->
    X ∉ svars ->
    named_no_negative_occurrence X (namify eg sg evars svars (svar_open X n ϕ))))
  /\
    (no_positive_occurrence_db_b n ϕ ->
    forall eg sg evars svars X,
    X ∉ free_svars ϕ ->
    X ∈ sg ->
    X ∉ svars ->
    named_no_positive_occurrence X (namify eg sg evars svars (svar_open X n ϕ))).
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; split; intros; cbn in *; simp namify; cbn; try lia; try reflexivity.
    * case_match; auto. set_solver.
    * cbn. case_match; simp namify.
    * cbn. case_match; simp namify; cbn; case_match; auto.
      - clear H5. simp namify. cbn.
        case_match.
        + clear H5. apply X_eq_svar_fresh_impl_X_notin_S in e.
          clear -e H2. induction n;set_solver.
        + auto.
      - simp namify. cbn. case_match; auto.
        clear -e H2. apply X_eq_svar_fresh_impl_X_notin_S in e.
        induction (pred n); set_solver.
    * move: H0 => /andP [H1_1 H1_2]. cbn. simp namify.
      simpl. rewrite (proj1 (IHs _ _ _)); auto. lia. set_solver.
      by apply take_notin.
      rewrite (proj1 (IHs _ _ _)); auto. lia. set_solver.
      by apply drop_notin.
    * move: H0 => /andP [H1_1 H1_2]. cbn. simp namify.
      simpl. rewrite (proj2 (IHs _ _ _)); auto. lia. set_solver.
      by apply take_notin.
      rewrite (proj2 (IHs _ _ _)); auto. lia. set_solver.
      by apply drop_notin.
    * move: H0 => /andP [H1_1 H1_2]. cbn. simp namify.
      simpl. rewrite (proj2 (IHs _ _ _)); auto. lia. set_solver.
      by apply take_notin.
      rewrite (proj1 (IHs _ _ _)); auto. lia. set_solver.
      by apply drop_notin.
    * move: H0 => /andP [H1_1 H1_2]. cbn.
      simpl. rewrite (proj1 (IHs _ _ _)); auto. lia. set_solver.
      by apply take_notin.
      rewrite (proj2 (IHs _ _ _)); auto. lia. set_solver.
      by apply drop_notin.
    * cbn. destruct evars; simp namify; simpl.
      - rewrite svar_open_evar_open_comm. rewrite (proj1 (IHs _ _ _)); auto.
        rewrite evar_open_size'. lia.
        cbn in H2. by apply no_negative_occurrence_evar_open.
        pose proof (free_svars_evar_open). set_solver.
      - rewrite svar_open_evar_open_comm. rewrite (proj1 (IHs _ _ _)); auto.
        rewrite evar_open_size'. lia.
        cbn in H2. by apply no_negative_occurrence_evar_open.
        pose proof (free_svars_evar_open). set_solver.
    * cbn. destruct evars; simp namify; simpl.
      - rewrite svar_open_evar_open_comm. rewrite (proj2 (IHs _ _ _)); auto.
        rewrite evar_open_size'. lia.
        cbn in H2. by apply no_positive_occurrence_evar_open.
        pose proof (free_svars_evar_open). set_solver.
      - rewrite svar_open_evar_open_comm. rewrite (proj2 (IHs _ _ _)); auto.
        rewrite evar_open_size'. lia.
        cbn in H2. by apply no_positive_occurrence_evar_open.
        pose proof (free_svars_evar_open). set_solver.
    * cbn. destruct svars; simp namify; simpl.
      - rewrite svar_open_bsvar_subst_higher; auto. lia. simpl.
        cbn in H2.
        rewrite (proj1 (IHs _ _ _)); auto.
        rewrite svar_open_size'. lia.
        apply negative_occ_svar_open; auto. lia.
        pose proof (free_svars_svar_open ϕ (svar_fresh (elements sg)) 0).
        pose proof (set_svar_fresh_is_fresh' sg). set_solver.
        set_solver. by case_match.
      - rewrite svar_open_bsvar_subst_higher; auto. lia. simpl.
        cbn in H2.
        rewrite (proj1 (IHs _ _ _)); auto.
        rewrite svar_open_size'. lia.
        apply negative_occ_svar_open; auto. lia.
        pose proof (free_svars_svar_open ϕ s0 0). set_solver.
        pose proof (set_svar_fresh_is_fresh' sg). set_solver.
        by case_match.
    * cbn. destruct svars; simp namify; simpl.
      - rewrite svar_open_bsvar_subst_higher; auto. lia. simpl.
        cbn in H2.
        rewrite (proj2 (IHs _ _ _)); auto.
        rewrite svar_open_size'. lia.
        apply positive_occ_svar_open; auto. lia.
        pose proof (free_svars_svar_open ϕ (svar_fresh (elements sg)) 0).
        pose proof (set_svar_fresh_is_fresh' sg). set_solver.
        set_solver. by case_match.
      - rewrite svar_open_bsvar_subst_higher; auto. lia. simpl.
        cbn in H2.
        rewrite (proj2 (IHs _ _ _)); auto.
        rewrite svar_open_size'. lia.
        apply positive_occ_svar_open; auto. lia.
        pose proof (free_svars_svar_open ϕ s0 0). set_solver.
        pose proof (set_svar_fresh_is_fresh' sg). set_solver.
        by case_match.
  Defined.

  Corollary no_positives_namify :
    forall ϕ n,
    no_positive_occurrence_db_b n ϕ ->
    forall eg sg evars svars X,
    X ∉ free_svars ϕ ->
    X ∈ sg ->
    X ∉ svars ->
    named_no_positive_occurrence X (namify eg sg evars svars (svar_open X n ϕ)).
  Proof.
    apply Private_no_negatives_namify.
  Defined.

  Corollary no_negatives_namify :
    forall ϕ n,
    no_negative_occurrence_db_b n ϕ ->
    (forall eg sg evars svars X, X ∉ free_svars ϕ ->
    X ∈ sg ->
    X ∉ svars ->
    named_no_negative_occurrence X (namify eg sg evars svars (svar_open X n ϕ))).
  Proof.
    apply Private_no_negatives_namify.
  Defined.

  Theorem namify_well_formed :
    forall ϕ evars svars eg sg,
      well_formed_positive ϕ ->
      free_svars ϕ ⊆ sg ->
      list_to_set svars ## free_svars ϕ ->
      named_well_formed (namify eg sg evars svars ϕ).
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity.
    * simp namify. simpl. move: H0 =>/andP [H0_1 H0_2].
      rewrite IHs; auto. lia. set_solver. admit.
      rewrite IHs; auto. lia. set_solver. admit.
    * simp namify. simpl. move: H0 =>/andP [H0_1 H0_2].
      rewrite IHs; auto. lia. set_solver. admit.
      rewrite IHs; auto. lia. set_solver. admit.
    * destruct evars; simp namify; simpl; rewrite IHs; auto.
      1,4: rewrite evar_open_size'; lia.
      1-4: by rewrite free_svars_evar_open.
    * destruct svars; simp namify; simpl.
      1-2: move: H0 => /andP [H0_1 H0_2].
      - rewrite no_negatives_namify; auto.
        admit.
        1-2: set_solver.
        (* simpl. rewrite IHs; auto. rewrite svar_open_size'. lia. *)
        pose proof (free_svars_svar_open ϕ (svar_fresh (elements sg)) 0).
        (* clear -H0 H1. set_solver. *) admit.
        (* set_solver. *)
      - rewrite no_negatives_namify; auto.
        admit.
        simpl in H2.
        (* simpl. rewrite IHs; auto. rewrite svar_open_size'. lia. *)
  Admitted.

  (* NOTE: do not use option type, because then inversion would be needed in the proofs,
     which is disallowed on Set. *)
  Fixpoint combine_names (el1 el2 : list evar) (sl1 sl2 : list svar)
    (ϕ : Pattern) (x : evar + svar) : list evar * list svar :=
  match ϕ with
  | patt_app ϕ1 ϕ2 =>
      match combine_names (take (count_ebinders ϕ1) el1) el2 (take (count_sbinders ϕ1) sl1) sl2 ϕ1 x,
          combine_names (drop (count_ebinders ϕ1) el1) el2 (drop (count_sbinders ϕ1) sl1) sl2 ϕ2 x with
      | (el1', sl1'), (el2', sl2') => (el1' ++ el2', sl1' ++ sl2')
    end
  | patt_imp ϕ1 ϕ2 =>
      match combine_names (take (count_ebinders ϕ1) el1) el2 (take (count_sbinders ϕ1) sl1) sl2 ϕ1 x,
            combine_names (drop (count_ebinders ϕ1) el1) el2 (drop (count_sbinders ϕ1) sl1) sl2 ϕ2 x with
      | (el1', sl1'), (el2', sl2') => (el1' ++ el2', sl1' ++ sl2')
      end
  | patt_exists ϕ =>
      match el1 with
      | y::el1' =>
        match combine_names el1' el2 sl1 sl2 ϕ x with
        | (el', sl') => (y::el', sl')
        end
      | _ => ([], []) (* side condition is needed to avoid this *)
      end
  | patt_mu ϕ =>
      match sl1 with
      | y::sl1' =>
        match combine_names el1 el2 sl1' sl2 ϕ x with
        | (el', sl') => (el', y::sl')
        end
      | _ => ([], []) (* side condition is needed to avoid this *)
      end
  | patt_free_evar y =>
      match x with
      | inl x =>
        match decide (x = y) with
        | left _ => (el2, sl2)
        | _ => (el1, sl1)
        end
      | inr x => (el1, sl1)
      end
  | patt_free_svar y =>
      match x with
      | inr x =>
        match decide (x = y) with
        | left _ => (el2, sl2)
        | _ => (el1, sl1)
        end
      | inl x => (el1, sl1)
      end
  | _ => (el1, sl1)
  end.

  Lemma count_ebinders_evar_open :
    forall ϕ n x, count_ebinders ϕ = count_ebinders (evar_open x n ϕ).
  Proof.
    induction ϕ; intros m y; cbn; auto.
    * by case_match.
    * by erewrite IHϕ1, IHϕ2.
    * by erewrite IHϕ1, IHϕ2.
    * by erewrite IHϕ.
    * by erewrite IHϕ.
  Defined.

  Lemma count_sbinders_evar_open :
    forall ϕ n x, count_sbinders ϕ = count_sbinders (evar_open x n ϕ).
  Proof.
    induction ϕ; intros m y; cbn; auto.
    * by case_match.
    * by erewrite IHϕ1, IHϕ2.
    * by erewrite IHϕ1, IHϕ2.
    * by erewrite IHϕ.
    * by erewrite IHϕ.
  Defined.

  Lemma count_sbinders_svar_open :
    forall ϕ N X, count_sbinders ϕ = count_sbinders (svar_open X N ϕ).
  Proof.
    induction ϕ; intros M Y; cbn; auto.
    * by case_match.
    * by erewrite IHϕ1, IHϕ2.
    * by erewrite IHϕ1, IHϕ2.
    * by erewrite IHϕ.
    * by erewrite IHϕ.
  Defined.

  Lemma count_ebinders_svar_open :
    forall ϕ N X, count_ebinders ϕ = count_ebinders (svar_open X N ϕ).
  Proof.
    induction ϕ; intros M Y; cbn; auto.
    * by case_match.
    * by erewrite IHϕ1, IHϕ2.
    * by erewrite IHϕ1, IHϕ2.
    * by erewrite IHϕ.
    * by erewrite IHϕ.
  Defined.

  Lemma combine_evar_evar_open :
  forall ϕ evarsϕ evarsψ svarsϕ svarsψ n y x,
    x <> y ->
    combine_names evarsϕ evarsψ svarsϕ svarsψ (evar_open y n ϕ) (inl x) =
    combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inl x).
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity.
    * cbn. case_match; simpl; auto.
      repeat case_match; auto. subst. congruence.
    * destruct combine_names eqn:EQ1.
      destruct combine_names eqn:EQ2 at 2.
      rewrite IHs in EQ1. lia. auto.
      rewrite -count_ebinders_evar_open -count_sbinders_evar_open in EQ1.
      rewrite EQ2 in EQ1. inversion EQ1. subst.
      destruct combine_names eqn:EQ3 at 1.
      destruct combine_names eqn:EQ4 at 1.
      rewrite IHs in EQ3. lia. auto.
      rewrite -count_ebinders_evar_open -count_sbinders_evar_open in EQ3.
      rewrite EQ3 in EQ4. by inversion EQ4.
    * destruct combine_names eqn:EQ1.
      destruct combine_names eqn:EQ2 at 2.
      rewrite IHs in EQ1. lia. auto.
      rewrite -count_ebinders_evar_open -count_sbinders_evar_open in EQ1.
      rewrite EQ2 in EQ1. inversion EQ1. subst.
      destruct combine_names eqn:EQ3 at 1.
      destruct combine_names eqn:EQ4 at 1.
      rewrite IHs in EQ3. lia. auto.
      rewrite -count_ebinders_evar_open -count_sbinders_evar_open in EQ3.
      rewrite EQ3 in EQ4. by inversion EQ4.
    * case_match. reflexivity.
      rewrite IHs. lia. assumption. reflexivity.
    * case_match. reflexivity.
      rewrite IHs. lia. assumption. reflexivity.
  Defined.

  Lemma combine_evar_svar_open :
  forall ϕ evarsϕ evarsψ svarsϕ svarsψ n y x,
    combine_names evarsϕ evarsψ svarsϕ svarsψ (svar_open y n ϕ) (inl x) =
    combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inl x).
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity.
    * cbn. case_match; simpl; auto.
    * destruct combine_names eqn:EQ1.
      destruct combine_names eqn:EQ2 at 2.
      rewrite IHs in EQ1. lia. auto.
      rewrite -count_ebinders_svar_open -count_sbinders_svar_open in EQ1.
      rewrite EQ2 in EQ1. inversion EQ1. subst.
      destruct combine_names eqn:EQ3 at 1.
      destruct combine_names eqn:EQ4 at 1.
      rewrite IHs in EQ3. lia. auto.
      rewrite -count_ebinders_svar_open -count_sbinders_svar_open in EQ3.
      rewrite EQ3 in EQ4. by inversion EQ4.
    * destruct combine_names eqn:EQ1.
      destruct combine_names eqn:EQ2 at 2.
      rewrite IHs in EQ1. lia. auto.
      rewrite -count_ebinders_svar_open -count_sbinders_svar_open in EQ1.
      rewrite EQ2 in EQ1. inversion EQ1. subst.
      destruct combine_names eqn:EQ3 at 1.
      destruct combine_names eqn:EQ4 at 1.
      rewrite IHs in EQ3. lia. auto.
      rewrite -count_ebinders_svar_open -count_sbinders_svar_open in EQ3.
      rewrite EQ3 in EQ4. by inversion EQ4.
    * case_match. reflexivity.
      rewrite IHs. lia. reflexivity.
    * case_match. reflexivity.
      rewrite IHs. lia. reflexivity.
  Defined.

  Lemma combine_svar_svar_open :
  forall ϕ evarsϕ evarsψ svarsϕ svarsψ n y x,
    x <> y ->
    combine_names evarsϕ evarsψ svarsϕ svarsψ (svar_open y n ϕ) (inr x) =
    combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inr x).
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity.
    * cbn. case_match; simpl; auto.
      repeat case_match; auto. subst. congruence.
    * destruct combine_names eqn:EQ1.
      destruct combine_names eqn:EQ2 at 2.
      rewrite IHs in EQ1. lia. auto.
      rewrite -count_ebinders_svar_open -count_sbinders_svar_open in EQ1.
      rewrite EQ2 in EQ1. inversion EQ1. subst.
      destruct combine_names eqn:EQ3 at 1.
      destruct combine_names eqn:EQ4 at 1.
      rewrite IHs in EQ3. lia. auto.
      rewrite -count_ebinders_svar_open -count_sbinders_svar_open in EQ3.
      rewrite EQ3 in EQ4. by inversion EQ4.
    * destruct combine_names eqn:EQ1.
      destruct combine_names eqn:EQ2 at 2.
      rewrite IHs in EQ1. lia. auto.
      rewrite -count_ebinders_svar_open -count_sbinders_svar_open in EQ1.
      rewrite EQ2 in EQ1. inversion EQ1. subst.
      destruct combine_names eqn:EQ3 at 1.
      destruct combine_names eqn:EQ4 at 1.
      rewrite IHs in EQ3. lia. auto.
      rewrite -count_ebinders_svar_open -count_sbinders_svar_open in EQ3.
      rewrite EQ3 in EQ4. by inversion EQ4.
    * case_match. reflexivity.
      rewrite IHs. lia. assumption. reflexivity.
    * case_match. reflexivity.
      rewrite IHs. lia. assumption. reflexivity.
  Defined.

  Lemma combine_svar_evar_open :
  forall ϕ evarsϕ evarsψ svarsϕ svarsψ n y x,
    combine_names evarsϕ evarsψ svarsϕ svarsψ (evar_open y n ϕ) (inr x) =
    combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inr x).
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity.
    * cbn. case_match; simpl; auto.
    * destruct combine_names eqn:EQ1.
      destruct combine_names eqn:EQ2 at 2.
      rewrite IHs in EQ1. lia. auto.
      rewrite -count_ebinders_evar_open -count_sbinders_evar_open in EQ1.
      rewrite EQ2 in EQ1. inversion EQ1. subst.
      destruct combine_names eqn:EQ3 at 1.
      destruct combine_names eqn:EQ4 at 1.
      rewrite IHs in EQ3. lia. auto.
      rewrite -count_ebinders_evar_open -count_sbinders_evar_open in EQ3.
      rewrite EQ3 in EQ4. by inversion EQ4.
    * destruct combine_names eqn:EQ1.
      destruct combine_names eqn:EQ2 at 2.
      rewrite IHs in EQ1. lia. auto.
      rewrite -count_ebinders_evar_open -count_sbinders_evar_open in EQ1.
      rewrite EQ2 in EQ1. inversion EQ1. subst.
      destruct combine_names eqn:EQ3 at 1.
      destruct combine_names eqn:EQ4 at 1.
      rewrite IHs in EQ3. lia. auto.
      rewrite -count_ebinders_evar_open -count_sbinders_evar_open in EQ3.
      rewrite EQ3 in EQ4. by inversion EQ4.
    * case_match. reflexivity.
      rewrite IHs. lia. reflexivity.
    * case_match. reflexivity.
      rewrite IHs. lia. reflexivity.
  Defined.

  (* the following 4 proofs are completely the same (2 cases are swapped in the last 2 proofs) *)
  Lemma count_ebinders_free_evar_subst :
    forall ϕ ψ evarsϕ evarsψ svarsϕ svarsψ x l l0,
    combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inl x) = (l, l0) ->
    length evarsϕ = count_ebinders ϕ ->
    length svarsϕ = count_sbinders ϕ ->
    length evarsψ = count_ebinders ψ ->
    length svarsψ = count_sbinders ψ ->
    count_ebinders (free_evar_subst ψ x ϕ) = length l.
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity; simp combine_names in *.
    * case_match; inversion H0; subst; auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * destruct combine_names eqn:EQ1.
      destruct (combine_names _ _ _ _ ϕ2 _) eqn:EQ2.
      inversion H0. subst.
      erewrite IHs; eauto. erewrite IHs; eauto.
      rewrite -app_length. reflexivity. 1,4: lia.
      all: try rewrite drop_length; try rewrite take_length; lia.
    * inversion H0. subst. auto.
    * destruct combine_names eqn:EQ1.
      destruct (combine_names _ _ _ _ ϕ2 _) eqn:EQ2.
      inversion H0. subst.
      erewrite IHs; eauto. erewrite IHs; eauto.
      rewrite -app_length. reflexivity. 1,4: lia.
      all: try rewrite drop_length; try rewrite take_length; lia.
    * destruct evarsϕ. simpl in H1. congruence.
      destruct combine_names eqn:EQ. inversion H0. subst.
      simpl. erewrite IHs. reflexivity. lia.
      eassumption. all: auto.
    * destruct svarsϕ. simpl in H2. congruence.
      destruct combine_names eqn:EQ. inversion H0. subst.
      simpl. erewrite IHs. reflexivity. lia.
      eassumption. all: auto.
  Defined.


  Lemma count_sbinders_free_evar_subst :
    forall ϕ ψ evarsϕ evarsψ svarsϕ svarsψ x l l0,
    combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inl x) = (l, l0) ->
    length evarsϕ = count_ebinders ϕ ->
    length svarsϕ = count_sbinders ϕ ->
    length evarsψ = count_ebinders ψ ->
    length svarsψ = count_sbinders ψ ->
    count_sbinders (free_evar_subst ψ x ϕ) = length l0.
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity; simp combine_names in *.
    * case_match; inversion H0; subst; auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * destruct combine_names eqn:EQ1.
      destruct (combine_names _ _ _ _ ϕ2 _) eqn:EQ2.
      inversion H0. subst.
      erewrite IHs; eauto. erewrite IHs; eauto.
      rewrite -app_length. reflexivity. 1,4: lia.
      all: try rewrite drop_length; try rewrite take_length; lia.
    * inversion H0. subst. auto.
    * destruct combine_names eqn:EQ1.
      destruct (combine_names _ _ _ _ ϕ2 _) eqn:EQ2.
      inversion H0. subst.
      erewrite IHs; eauto. erewrite IHs; eauto.
      rewrite -app_length. reflexivity. 1,4: lia.
      all: try rewrite drop_length; try rewrite take_length; lia.
    * destruct evarsϕ. simpl in H1. congruence.
      destruct combine_names eqn:EQ. inversion H0. subst.
      simpl. erewrite IHs. reflexivity. lia.
      eassumption. all: auto.
    * destruct svarsϕ. simpl in H2. congruence.
      destruct combine_names eqn:EQ. inversion H0. subst.
      simpl. erewrite IHs. reflexivity. lia.
      eassumption. all: auto.
  Defined.

  Lemma count_ebinders_free_svar_subst :
    forall ϕ ψ evarsϕ evarsψ svarsϕ svarsψ x l l0,
    combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inr x) = (l, l0) ->
    length evarsϕ = count_ebinders ϕ ->
    length svarsϕ = count_sbinders ϕ ->
    length evarsψ = count_ebinders ψ ->
    length svarsψ = count_sbinders ψ ->
    count_ebinders (free_svar_subst ψ x ϕ) = length l.
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity; simp combine_names in *.
    * inversion H0. subst. auto.
    * case_match; inversion H0; subst; auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * destruct combine_names eqn:EQ1.
      destruct (combine_names _ _ _ _ ϕ2 _) eqn:EQ2.
      inversion H0. subst.
      erewrite IHs; eauto. erewrite IHs; eauto.
      rewrite -app_length. reflexivity. 1,4: lia.
      all: try rewrite drop_length; try rewrite take_length; lia.
    * inversion H0. subst. auto.
    * destruct combine_names eqn:EQ1.
      destruct (combine_names _ _ _ _ ϕ2 _) eqn:EQ2.
      inversion H0. subst.
      erewrite IHs; eauto. erewrite IHs; eauto.
      rewrite -app_length. reflexivity. 1,4: lia.
      all: try rewrite drop_length; try rewrite take_length; lia.
    * destruct evarsϕ. simpl in H1. congruence.
      destruct combine_names eqn:EQ. inversion H0. subst.
      simpl. erewrite IHs. reflexivity. lia.
      eassumption. all: auto.
    * destruct svarsϕ. simpl in H2. congruence.
      destruct combine_names eqn:EQ. inversion H0. subst.
      simpl. erewrite IHs. reflexivity. lia.
      eassumption. all: auto.
  Defined.

  Lemma count_sbinders_free_svar_subst :
    forall ϕ ψ evarsϕ evarsψ svarsϕ svarsψ x l l0,
    combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inr x) = (l, l0) ->
    length evarsϕ = count_ebinders ϕ ->
    length svarsϕ = count_sbinders ϕ ->
    length evarsψ = count_ebinders ψ ->
    length svarsψ = count_sbinders ψ ->
    count_sbinders (free_svar_subst ψ x ϕ) = length l0.
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity; simp combine_names in *.
    * inversion H0. subst. auto.
    * case_match; inversion H0; subst; auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * inversion H0. subst. auto.
    * destruct combine_names eqn:EQ1.
      destruct (combine_names _ _ _ _ ϕ2 _) eqn:EQ2.
      inversion H0. subst.
      erewrite IHs; eauto. erewrite IHs; eauto.
      rewrite -app_length. reflexivity. 1,4: lia.
      all: try rewrite drop_length; try rewrite take_length; lia.
    * inversion H0. subst. auto.
    * destruct combine_names eqn:EQ1.
      destruct (combine_names _ _ _ _ ϕ2 _) eqn:EQ2.
      inversion H0. subst.
      erewrite IHs; eauto. erewrite IHs; eauto.
      rewrite -app_length. reflexivity. 1,4: lia.
      all: try rewrite drop_length; try rewrite take_length; lia.
    * destruct evarsϕ. simpl in H1. congruence.
      destruct combine_names eqn:EQ. inversion H0. subst.
      simpl. erewrite IHs. reflexivity. lia.
      eassumption. all: auto.
    * destruct svarsϕ. simpl in H2. congruence.
      destruct combine_names eqn:EQ. inversion H0. subst.
      simpl. erewrite IHs. reflexivity. lia.
      eassumption. all: auto.
  Defined.

  Equations? no_accidental_capture (el : list evar) (sl : list svar) (ϕ : Pattern) : bool
    by wf (size' ϕ) lt  :=
    no_accidental_capture el sl (patt_imp ϕ1 ϕ2) :=
      no_accidental_capture (take (count_ebinders ϕ1) el) (take (count_sbinders ϕ1) sl) ϕ1 &&
      no_accidental_capture (drop (count_ebinders ϕ1) el) (drop (count_sbinders ϕ1) sl) ϕ2;
    no_accidental_capture el sl (patt_app ϕ1 ϕ2) :=
      no_accidental_capture (take (count_ebinders ϕ1) el) (take (count_sbinders ϕ1) sl) ϕ1 &&
      no_accidental_capture (drop (count_ebinders ϕ1) el) (drop (count_sbinders ϕ1) sl) ϕ2;
    no_accidental_capture (x::el) sl (patt_exists ϕ) :=
      match decide (x ∈ free_evars ϕ) with
      | left _  => false
      | right _ => no_accidental_capture el sl (evar_open x 0 ϕ)
      end;
    no_accidental_capture [] sl (patt_exists ϕ) := false; (* <- ill-formed input list el *)
    no_accidental_capture el (X::sl) (patt_mu ϕ) :=
      match decide (X ∈ free_svars ϕ) with
      | left _  => false
      | right _ => no_accidental_capture el sl (svar_open X 0 ϕ)
      end;
    no_accidental_capture el [] (patt_mu ϕ) := false; (* <- ill-formed input list el *)
    no_accidental_capture _ _ _ := true.
  Proof.
    all: simpl; try lia.
    rewrite evar_open_size'; lia.
    rewrite svar_open_size'; lia.
  Defined.

  Lemma well_formed_namify_free_evars :
    forall ϕ eg sg evarsϕ svarsϕ, well_formed ϕ ->
    no_accidental_capture evarsϕ svarsϕ ϕ ->
    named_free_evars (namify eg sg evarsϕ svarsϕ ϕ) = free_evars ϕ.
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros; simpl in *; try lia; try reflexivity; simp namify in *; try now wf_auto2.
    * simpl. revert H1. simp no_accidental_capture. move=> /andP [H1_1 H1_2].
      rewrite IHs; auto. lia. wf_auto2.
      rewrite IHs; auto. lia. wf_auto2.
    * simpl. revert H1. simp no_accidental_capture. move=> /andP [H1_1 H1_2].
      rewrite IHs; auto. lia. wf_auto2.
      rewrite IHs; auto. lia. wf_auto2.
    * destruct evarsϕ; simp namify.
      - simp no_accidental_capture in H1. congruence.
      - simpl. simp no_accidental_capture in H1. destruct decide. congruence.
        rewrite IHs; auto.
        rewrite evar_open_size'. lia.
        wf_auto2.
        clear -n.
        pose proof (free_evars_evar_open ϕ e 0).
        pose proof (free_evars_evar_open' ϕ e 0).
        set_solver.
    * destruct svarsϕ; simp namify.
    - simp no_accidental_capture in H1. congruence.
    - simpl. simp no_accidental_capture in H1. destruct decide. congruence.
      rewrite IHs; auto.
      rewrite svar_open_size'. lia.
      wf_auto2.
      clear -n.
      by pose proof (free_evars_svar_open ϕ 0 s0).
  Qed.

  (* Always use the functions above with sufficient number of names supplemented, i.e.,
     for any ϕ, length evars = count_ebinders ϕ and length svars = count_sbinders ϕ *)
  Theorem free_evar_subst_namify :
    forall ϕ ψ x evarsϕ evarsψ svarsϕ svarsψ eg sg evars svars,
      combine_names evarsϕ evarsψ svarsϕ svarsψ ϕ (inl x) = (evars, svars) ->
      length evarsϕ = count_ebinders ϕ ->
      length svarsϕ = count_sbinders ϕ ->
      length evarsψ = count_ebinders ψ ->
      length svarsψ = count_sbinders ψ ->
      well_formed ψ ->
      x ∉ evarsϕ ->
      x ∈ eg ->
      no_accidental_capture evarsϕ svarsϕ ϕ ->
      no_accidental_capture evarsψ svarsψ ψ ->
      list_to_set evarsϕ ## free_evars ψ ->
      namify eg sg evars svars (free_evar_subst ψ x ϕ) = 
      standard_evar_subst (namify eg sg evarsϕ svarsϕ ϕ) x (namify eg sg evarsψ svarsψ ψ) : Set.
  Proof.
    intros ϕ. remember (size' ϕ) as s.
    assert (size' ϕ <= s) by lia. clear Heqs. revert ϕ H.
    induction s; destruct ϕ; intros Hs ψ y evarsϕ evarsψ svarsϕ svarsψ eg sg evars svars Hcomb 
      Hl1 Hl2 Hl3 Hl4 Hwf Hnin Hin Hnoa1 Hnoa2 Hdis;
      simpl in *; try lia; try reflexivity; simp combine_names in *.
    * case_match.
      - apply pair_equal_spec in Hcomb as [? ?]; subst.
        simp namify. simp standard_evar_subst. rewrite H. simpl. reflexivity.
      - apply pair_equal_spec in Hcomb as [? ?]; subst.
        simp namify. simp standard_evar_subst. rewrite H. simpl. reflexivity.
    * simp namify. remember (evar_fresh _) as xx. simp standard_evar_subst.
      destruct decide; simpl. 2: reflexivity.
      apply X_eq_evar_fresh_impl_X_notin_S in Heqxx. induction n; set_solver.
    * intros. simp namify. simp standard_evar_subst. simp no_accidental_capture in Hnoa1.
      move: Hnoa1 => /andP [Hnoa1_1 Hnoa1_2].
      erewrite IHs. erewrite IHs. reflexivity. all: auto; try lia.
      all: try rewrite take_length; try rewrite drop_length; try lia.
      3: {
        pose proof (drop_subseteq evarsϕ). set_solver.
      }
      5: {
        pose proof (take_subseteq evarsϕ). set_solver.
      }
      2: by apply drop_notin. 3: by apply take_notin.
      - destruct combine_names eqn:Eq1.
        destruct (combine_names _ _ _ _ ϕ2 _) eqn:Eq2.
        apply pair_equal_spec in Hcomb as [? ?]; subst.
        eapply count_ebinders_free_evar_subst in Eq1 as Eq1'.
        eapply count_sbinders_free_evar_subst in Eq1 as Eq1''.
        rewrite Eq1' Eq1''. by rewrite 2!drop_app.
        all: try rewrite take_length; try rewrite drop_length; try lia.
        eapply count_sbinders_free_evar_subst in Eq1 as Eq1''.
        all: try rewrite take_length; try rewrite drop_length; try lia.
        all: eassumption.
      - destruct combine_names eqn:Eq1.
        destruct (combine_names _ _ _ _ ϕ2 _) eqn:Eq2.
        apply pair_equal_spec in Hcomb as [? ?]; subst.
        eapply count_ebinders_free_evar_subst in Eq1 as Eq1'.
        eapply count_sbinders_free_evar_subst in Eq1 as Eq1''.
        rewrite Eq1' Eq1''. by rewrite 2!take_app.
        all: try rewrite take_length; try rewrite drop_length; try lia.
        eapply count_sbinders_free_evar_subst in Eq1 as Eq1''.
        all: try rewrite take_length; try rewrite drop_length; try lia.
        all: eassumption.
    * intros. simp namify. simp standard_evar_subst. simp no_accidental_capture in Hnoa1.
      move: Hnoa1 => /andP [Hnoa1_1 Hnoa1_2].
      erewrite IHs. erewrite IHs. reflexivity. all: auto; try lia.
      all: try rewrite take_length; try rewrite drop_length; try lia.
      3: {
        pose proof (drop_subseteq evarsϕ). set_solver.
      }
      5: {
        pose proof (take_subseteq evarsϕ). set_solver.
      }
      2: by apply drop_notin. 3: by apply take_notin.
      - destruct combine_names eqn:Eq1.
        destruct (combine_names _ _ _ _ ϕ2 _) eqn:Eq2.
        apply pair_equal_spec in Hcomb as [? ?]; subst.
        eapply count_ebinders_free_evar_subst in Eq1 as Eq1'.
        eapply count_sbinders_free_evar_subst in Eq1 as Eq1''.
        rewrite Eq1' Eq1''. by rewrite 2!drop_app.
        all: try rewrite take_length; try rewrite drop_length; try lia.
        eapply count_sbinders_free_evar_subst in Eq1 as Eq1''.
        all: try rewrite take_length; try rewrite drop_length; try lia.
        all: eassumption.
      - destruct combine_names eqn:Eq1.
        destruct (combine_names _ _ _ _ ϕ2 _) eqn:Eq2.
        apply pair_equal_spec in Hcomb as [? ?]; subst.
        eapply count_ebinders_free_evar_subst in Eq1 as Eq1'.
        eapply count_sbinders_free_evar_subst in Eq1 as Eq1''.
        rewrite Eq1' Eq1''. by rewrite 2!take_app.
        all: try rewrite take_length; try rewrite drop_length; try lia.
        eapply count_sbinders_free_evar_subst in Eq1 as Eq1''.
        all: try rewrite take_length; try rewrite drop_length; try lia.
        all: eassumption.
    * destruct evarsϕ; simp no_accidental_capture in Hnoa1. congruence.
      destruct decide. congruence. simpl in Hl1.
      destruct combine_names eqn:Eq. destruct evars. congruence.
      apply pair_equal_spec in Hcomb as [? ?]; subst.
      simp namify. simp standard_evar_subst.
      inversion H. (* TODO: is this inversion okay? *)
      subst.
      destruct decide. set_solver.
      simpl. destruct decide.
      - simpl in Hdis. pose proof a as He. rewrite well_formed_namify_free_evars in He; auto.
        set_solver.
      - simpl. erewrite <- IHs; auto. 3: rewrite combine_evar_evar_open; eassumption.
        2: rewrite evar_open_size'; lia.
        2: rewrite -count_ebinders_evar_open; lia.
        2: by rewrite -count_sbinders_evar_open.
        by rewrite evar_open_free_evar_subst_swap.
        set_solver.
        set_solver.
    * destruct svarsϕ. simpl in Hl2. congruence.
      destruct combine_names eqn:Eq. destruct svars.
      congruence.
      apply pair_equal_spec in Hcomb as [? ?]; subst.
      simp namify. simp standard_evar_subst.
      inversion H0. (* TODO: is this inversion okay? *)
      subst.
      erewrite <- IHs; auto. 3: rewrite combine_evar_svar_open; eassumption.
      2: rewrite svar_open_size'; lia.
      2: by rewrite -count_ebinders_svar_open.
      2: rewrite -count_sbinders_svar_open; simpl in Hl2; lia.
      rewrite free_evar_subst_bsvar_subst; auto.
      wf_auto2.
      unfold evar_is_fresh_in. set_solver.
      simp no_accidental_capture in Hnoa1. destruct decide. congruence. assumption.
  Defined.

  End whitelist_translation.
  (* Equations? named_evar_subst'
    (eg : EVarGen) (sg : SVarGen) (ϕ ψ : NamedPattern) (x : evar) : NamedPattern
    by wf (nsize' ϕ) lt :=
    named_evar_subst' eg sg (npatt_evar x') ψ x with (decide (x = x')) => {
      | left _ := ψ
      | right _ := npatt_evar x'
    } ;
    named_evar_subst' eg sg (npatt_bott) _ _ := npatt_bott ;
    named_evar_subst' eg sg (npatt_svar X) _ _ := npatt_svar X ;
    named_evar_subst' eg sg (npatt_sym s) _ _ := npatt_sym s ;
    named_evar_subst' eg sg (npatt_imp phi1 phi2) ψ x :=
      npatt_imp (named_evar_subst' eg sg phi1 ψ x)
                (named_evar_subst' eg sg phi2 ψ x) ;
    named_evar_subst' eg sg (npatt_app phi1 phi2) ψ x :=
      npatt_app (named_evar_subst' eg sg phi1 ψ x)
                (named_evar_subst' eg sg phi2 ψ x) ;
    named_evar_subst' eg sg (npatt_exists x' ϕ') ψ x with (decide (x = x')) => {
      | right _ := npatt_exists x' ϕ'
      | left _ with (decide (x' ∈ named_free_evars ψ)) => {
        | right _ := npatt_exists x' (named_evar_subst' eg sg ϕ' ψ x)
        | left _ :=
          let avoid := union (named_free_evars ψ) (named_free_evars ϕ') in
          let fresh_x := eg_get eg avoid in
          let renamed_ϕ' := rename_free_evar ϕ' fresh_x x' in
          npatt_exists fresh_x (named_evar_subst' eg sg renamed_ϕ' ψ x)
      }
    } ;
    named_evar_subst' eg sg (npatt_mu X' ϕ') ψ x
    with (decide (X' ∈ named_free_svars ψ)) => {
      | right _ := npatt_mu X' (named_evar_subst' eg sg ϕ' ψ x)
      | left _ :=
        let Avoid := union (named_free_svars ψ) (named_free_svars ϕ') in
        let fresh_X := sg_get sg Avoid in
        let renamed_ϕ' := rename_free_svar ϕ' fresh_X X' in
        npatt_mu fresh_X (named_evar_subst' eg sg renamed_ϕ' ψ x)
    }.
    Proof.
      all: cbn; try lia.
      { unfold renamed_ϕ'. rewrite nsize'_rename_free_evar. lia. }
      { unfold renamed_ϕ'. rewrite nsize'_rename_free_svar. lia. }
    Qed.

  Equations? named_svar_subst'
    (eg : EVarGen) (sg : SVarGen) (ϕ ψ : NamedPattern) (X : svar) : NamedPattern
    by wf (nsize' ϕ) lt :=
    named_svar_subst' eg sg (npatt_svar X') ψ X with (decide (X = X')) => {
      | left _ := ψ
      | right _ := npatt_svar X'
    } ;
    named_svar_subst' eg sg (npatt_bott) _ _ := npatt_bott ;
    named_svar_subst' eg sg (npatt_evar x) _ _ := npatt_evar x ;
    named_svar_subst' eg sg (npatt_sym s) _ _ := npatt_sym s ;
    named_svar_subst' eg sg (npatt_imp phi1 phi2) ψ X :=
      npatt_imp (named_svar_subst' eg sg phi1 ψ X)
                (named_svar_subst' eg sg phi2 ψ X) ;
    named_svar_subst' eg sg (npatt_app phi1 phi2) ψ X :=
      npatt_app (named_svar_subst' eg sg phi1 ψ X)
                (named_svar_subst' eg sg phi2 ψ X) ;
    named_svar_subst' eg sg (npatt_exists x' ϕ') ψ X
    with (decide (x' ∈ named_free_evars ψ)) => {
      | right _ := npatt_exists x' (named_svar_subst' eg sg ϕ' ψ X)
      | left _ :=
        let avoid := union (named_free_evars ψ) (named_free_evars ϕ') in
        let fresh_x := eg_get eg avoid in
        let renamed_ϕ' := rename_free_evar ϕ' fresh_x x' in
        npatt_exists fresh_x (named_svar_subst' eg sg renamed_ϕ' ψ X)
    }; 
    named_svar_subst' eg sg (npatt_mu X' ϕ') ψ X with (decide (X = X')) => {
      | right _ := npatt_mu X' ϕ'
      | left _ with (decide (X' ∈ named_free_svars ψ)) => {
        | right _ := npatt_mu X' (named_svar_subst' eg sg ϕ' ψ X)
        | left _ :=
          let Avoid := union (named_free_svars ψ) (named_free_svars ϕ') in
          let fresh_X := sg_get sg Avoid in
          let renamed_ϕ' := rename_free_svar ϕ' fresh_X X' in
          npatt_mu fresh_X (named_svar_subst' eg sg renamed_ϕ' ψ X)
      }
    } .
    Proof.
      all: cbn; try lia.
      { unfold renamed_ϕ'. rewrite nsize'_rename_free_evar. lia. }
      { unfold renamed_ϕ'. rewrite nsize'_rename_free_svar. lia. }
    Qed.

  Definition named_evar_subst
    (phi psi : NamedPattern) (x : evar) : NamedPattern
    := named_evar_subst' (default_EVarGen ∅) (default_SVarGen ∅) phi psi x
  .

  Definition named_svar_subst
    (phi psi : NamedPattern) (X : svar) : NamedPattern
    := named_svar_subst' (default_EVarGen ∅) (default_SVarGen ∅) phi psi X
  . *)

  (* Derived named operators *)
  Definition npatt_not (phi : NamedPattern) := npatt_imp phi npatt_bott.
  Definition npatt_or  (l r : NamedPattern) := npatt_imp (npatt_not l) r.
  Definition npatt_and (l r : NamedPattern) :=
    npatt_not (npatt_or (npatt_not l) (npatt_not r)).
  Definition npatt_top := (npatt_not npatt_bott).
  Definition npatt_iff (l r : NamedPattern) :=
    npatt_and (npatt_imp l r) (npatt_imp r l).
  Definition npatt_forall (phi : NamedPattern) (x : evar) :=
    npatt_not (npatt_exists x (npatt_not phi)).
  (* Definition npatt_nu (phi : NamedPattern) (X : svar) :=
    npatt_not (npatt_mu X (npatt_not (named_svar_subst phi (npatt_not (npatt_svar X)) X))). *)
(*
  Check @kmap.
  (* TODO: use kmap. Check kmap. *)
  Definition evm_incr (evm : EVarMap) : EVarMap :=
    kmap S evm.

  Definition svm_incr (svm : SVarMap) : SVarMap :=
    kmap S svm.

  Definition incr_one_evar (phi : Pattern) : Pattern :=
    match phi with
    | patt_bound_evar n => patt_bound_evar (S n)
    | x => x
    end.

  Definition incr_one_svar (phi : Pattern) : Pattern :=
    match phi with
    | patt_bound_svar n => patt_bound_svar (S n)
    | x => x
    end.

  Definition cache_incr_evar (cache : gmap Pattern NamedPattern) : gmap Pattern NamedPattern :=
    kmap incr_one_evar cache.

  Definition cache_incr_svar (cache : gmap Pattern NamedPattern) : gmap Pattern NamedPattern :=
    kmap incr_one_svar cache.

  Definition evm_fresh (evm : EVarMap) (ϕ : Pattern) : evar
    := evar_fresh (elements (free_evars ϕ ∪ (list_to_set (map snd (map_to_list evm))))).

  Definition evs_fresh (evs : EVarSet) (ϕ : Pattern) : evar
    := evar_fresh (elements (free_evars ϕ ∪ evs)).

  Definition svm_fresh (svm : SVarMap) (ϕ : Pattern) : svar
    := svar_fresh (elements (free_svars ϕ ∪ (list_to_set (map snd (map_to_list svm))))).

  Definition svs_fresh (svs : SVarSet) (ϕ : Pattern) : svar
    := svar_fresh (elements (free_svars ϕ ∪ svs)).

  Fixpoint to_NamedPattern' (ϕ : Pattern) (evm : EVarMap) (svm : SVarMap)
    : NamedPattern * EVarMap * SVarMap :=
    match ϕ with
    | patt_free_evar x => (npatt_evar x, evm, svm)
    | patt_free_svar X => (npatt_svar X, evm, svm)
    | patt_bound_evar n =>
      (if (evm !! n) is Some x then npatt_evar x else npatt_bott, evm, svm)
    | patt_bound_svar n =>
      (if (svm !! n) is Some X then npatt_svar X else npatt_bott, evm, svm)
    | patt_sym s => (npatt_sym s, evm, svm)
    | patt_app phi1 phi2 =>
      let: (nphi1, evm', svm') := to_NamedPattern' phi1 evm svm in
      let: (nphi2, evm'', svm'') := to_NamedPattern' phi2 evm' svm' in
      (npatt_app nphi1 nphi2, evm'', svm'')
    | patt_bott => (npatt_bott, evm, svm)
    | patt_imp phi1 phi2 =>
      let: (nphi1, evm', svm') := to_NamedPattern' phi1 evm svm in
      let: (nphi2, evm'', svm'') := to_NamedPattern' phi2 evm' svm' in
      (npatt_imp nphi1 nphi2, evm'', svm'')
    | patt_exists phi =>
      let: x := evm_fresh evm phi in
      let: evm_ex := <[0:=x]>(evm_incr evm) in
      let: (nphi, evm', svm') := to_NamedPattern' phi evm_ex svm in
      (npatt_exists x nphi, evm, svm)
    | patt_mu phi =>
      let: X := svm_fresh svm phi in
      let: svm_ex := <[0:=X]>(svm_incr svm) in
      let: (nphi, evm', svm') := to_NamedPattern' phi evm svm_ex in
      (npatt_mu X nphi, evm, svm)
    end.

  Definition to_NamedPattern (ϕ : Pattern) : NamedPattern :=
    (to_NamedPattern' ϕ ∅ ∅).1.1.

  Definition not_contain_bound_evar_0 ϕ : Prop := ~~ bevar_occur ϕ 0.
  Definition not_contain_bound_svar_0 ϕ : Prop := ~~ bsvar_occur ϕ 0.


  Definition CacheEntry := (Pattern * NamedPattern)%type.

  Definition is_bound_evar (ϕ : Pattern) : Prop := exists b, ϕ = patt_bound_evar b.

  Global Instance is_bound_evar_dec (ϕ : Pattern) : Decision (is_bound_evar ϕ).
  Proof.
    unfold Decision; destruct ϕ; simpl;
      try solve[right; intros [b Hcontra]; inversion Hcontra].
    left. exists n. reflexivity.
  Defined.

  Definition is_bound_evar_entry (ϕnϕ : CacheEntry) : Prop := is_bound_evar (fst ϕnϕ).

  Global Instance is_bound_evar_entry_dec (ce : CacheEntry) : Decision (is_bound_evar_entry ce).
  Proof.
    destruct ce as [ϕ nϕ].
    destruct (decide (is_bound_evar ϕ)) as [L|R].
    - left. destruct L as [dbi Hdbi]. subst ϕ. exists dbi. reflexivity.
    - right. intros Hcontra. inversion Hcontra. simpl in H. subst ϕ.
      apply R. exists x. reflexivity.
  Defined.

  Definition is_bound_svar (ϕ : Pattern) : Prop := exists b, ϕ = patt_bound_svar b.

  Global Instance is_bound_svar_dec (ϕ : Pattern) : Decision (is_bound_svar ϕ).
  Proof.
    unfold Decision; destruct ϕ; simpl;
      try solve[right; intros [b Hcontra]; inversion Hcontra].
    left. exists n. reflexivity.
  Defined.

  Definition is_bound_svar_entry (ϕnϕ : CacheEntry) : Prop := is_bound_svar (fst ϕnϕ).
  
  Global Instance is_bound_svar_entry_dec (ce : CacheEntry) : Decision (is_bound_svar_entry ce).
  Proof.
    destruct ce as [ϕ nϕ].
    destruct (decide (is_bound_svar ϕ)) as [L|R].
    - left. destruct L as [dbi Hdbi]. subst ϕ. exists dbi. reflexivity.
    - right. intros Hcontra. inversion Hcontra. simpl in H. subst ϕ.
      apply R. exists x. reflexivity.
  Defined.


  Definition keep_bound_evars (cache : gmap Pattern NamedPattern) :=
    filter is_bound_evar_entry cache.

  Definition remove_bound_evars (cache : gmap Pattern NamedPattern) :=
    filter (fun e => ~ is_bound_evar_entry e) cache.

  Definition keep_bound_svars (cache : gmap Pattern NamedPattern) :=
    filter is_bound_svar_entry cache.

  Definition remove_bound_svars (cache : gmap Pattern NamedPattern) :=
    filter (fun e => ~ is_bound_svar_entry e) cache.


  (* pre: all dangling variables of [\phi] are in [cache].  *)
  Fixpoint to_NamedPattern2'
           (ϕ : Pattern)
           (cache : gmap Pattern NamedPattern)
           (used_evars : EVarSet)
           (used_svars : SVarSet)
    : (NamedPattern * (gmap Pattern NamedPattern) * EVarSet * SVarSet)%type :=
    if cache !! ϕ is Some ψ
    then (ψ, cache, used_evars, used_svars)
    else
      let: (ψ, cache', used_evars', used_svars') :=
         match ϕ return (NamedPattern * (gmap Pattern NamedPattern) * EVarSet * SVarSet)%type with
         | patt_bott
           => (npatt_bott, cache, used_evars, used_svars)
         | patt_bound_evar n (* never happens - it is always in cache *)
         | patt_bound_svar n (* the same *)
           => (npatt_bott, cache, used_evars, used_svars)
         | patt_free_evar x
           => (npatt_evar x, cache, used_evars, used_svars)
         | patt_free_svar X
           => (npatt_svar X, cache, used_evars, used_svars)
         | patt_sym s
           => (npatt_sym s, cache, used_evars, used_svars)
         | patt_imp ϕ₁ ϕ₂
           => let: (nϕ₁, cache', used_evars', used_svars')
                 := to_NamedPattern2' ϕ₁ cache used_evars used_svars in
              let: (nϕ₂, cache'', used_evars'', used_svars'')
                 := to_NamedPattern2' ϕ₂ cache' used_evars' used_svars' in
              ((npatt_imp nϕ₁ nϕ₂), cache'', used_evars'', used_svars'')
         | patt_app ϕ₁ ϕ₂
           => let: (nϕ₁, cache', used_evars', used_svars')
                 := to_NamedPattern2' ϕ₁ cache used_evars used_svars in
              let: (nϕ₂, cache'', used_evars'', used_svars'')
                 := to_NamedPattern2' ϕ₂ cache' used_evars' used_svars' in
              ((npatt_app nϕ₁ nϕ₂), cache'', used_evars'', used_svars'')
         | patt_exists phi
           => let: x := evs_fresh used_evars phi in
              let: used_evars_ex := used_evars ∪ {[x]} in
              let: cache_ex := <[patt_bound_evar 0:=npatt_evar x]>(cache_incr_evar cache) in
              let: (nphi, cache', used_evars', used_svars')
                := to_NamedPattern2' phi cache_ex used_evars_ex used_svars in
              let: cache'' := (remove_bound_evars cache') ∪ (keep_bound_evars cache) in
              (npatt_exists x nphi, cache'', used_evars', used_svars)
         | patt_mu phi
           => let: X := svs_fresh used_svars phi in
              let: used_svars_ex := used_svars ∪ {[X]} in
              let: cache_ex := <[patt_bound_svar 0:=npatt_svar X]>(cache_incr_svar cache) in
              let: (nphi, cache', used_evars', used_svars')
                := to_NamedPattern2' phi cache_ex used_evars used_svars_ex in
              let: cache'' := (remove_bound_svars cache') ∪ (keep_bound_svars cache) in
              (npatt_mu X nphi, cache'', used_evars', used_svars)
         end
      in
      (ψ, <[ϕ:=ψ]>cache', used_evars', used_svars).

  Definition to_NamedPattern2 (ϕ : Pattern) : NamedPattern :=
    (to_NamedPattern2' ϕ gmap_empty ∅ ∅).1.1.1.

 

  Definition SVarMap_injective_prop (svm : SVarMap) : Prop :=
    forall dbi1 dbi2 X1 X2, svm !! dbi1 = Some X1 -> svm !! dbi2 = Some X2 ->
                            X1 = X2 -> dbi1 = dbi2.


  (* This is very suspicious. *)
  Lemma to_NamedPattern'_SVarMap_injective (evm : EVarMap) (svm : SVarMap) (ϕ : Pattern):
    SVarMap_injective_prop svm ->
    SVarMap_injective_prop (to_NamedPattern' ϕ evm svm).2.
  Proof.
    intros Hinj.
    move: evm svm Hinj.
    induction ϕ; intros evm svm Hinj; simpl; auto.
    - remember (to_NamedPattern' ϕ1 evm svm) as tonϕ1.
      destruct tonϕ1 as [[nphi1 evm'] svm'].
      remember (to_NamedPattern' ϕ2 evm' svm') as tonϕ2.
      destruct tonϕ2 as [[nphi2 evm''] svm''].
      simpl.
      apply (f_equal snd) in Heqtonϕ2. simpl in Heqtonϕ2. subst svm''. apply IHϕ2.
      apply (f_equal snd) in Heqtonϕ1. simpl in Heqtonϕ1. subst svm'. apply IHϕ1.
      exact Hinj.
    - remember (to_NamedPattern' ϕ1 evm svm) as tonϕ1.
      destruct tonϕ1 as [[nphi1 evm'] svm'].
      remember (to_NamedPattern' ϕ2 evm' svm') as tonϕ2.
      destruct tonϕ2 as [[nphi2 evm''] svm''].
      simpl.
      apply (f_equal snd) in Heqtonϕ2. simpl in Heqtonϕ2. subst svm''. apply IHϕ2.
      apply (f_equal snd) in Heqtonϕ1. simpl in Heqtonϕ1. subst svm'. apply IHϕ1.
      exact Hinj.
    - remember (to_NamedPattern' ϕ (<[0:=evm_fresh evm ϕ]> (evm_incr evm)) svm) as tonϕ.
      destruct tonϕ as [[nphi evm'] svm'].
      simpl.
      exact Hinj.
    - remember (to_NamedPattern' ϕ evm (<[0:=svm_fresh svm ϕ]> (svm_incr svm))) as tonϕ.
      destruct tonϕ as [[nphi evm'] svm'].
      simpl.
      apply Hinj.
  Qed.



  Lemma to_NamedPattern'_occurrence
        (evm : EVarMap) (svm : SVarMap) (X : svar) (dbi : db_index) (ϕ : Pattern):
    SVarMap_injective_prop svm ->
    svm !! dbi = Some X ->
    svar_is_fresh_in X ϕ ->
    named_no_negative_occurrence X (to_NamedPattern' ϕ evm svm).1.1 = no_negative_occurrence_db_b dbi ϕ
    /\ named_no_positive_occurrence X (to_NamedPattern' ϕ evm svm).1.1 = no_positive_occurrence_db_b dbi ϕ.
  Proof.
    intros Hinj Hdbi Hfresh.
    move: evm svm Hinj Hdbi.
    induction ϕ; intros evm svm Hinj Hdbi.
    - unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b; simpl.
      split; reflexivity.
    - unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b; simpl.
      split; [reflexivity|]. unfold svar_is_fresh_in in Hfresh. simpl in Hfresh.
      apply not_elem_of_singleton_1 in Hfresh.
      destruct (decide (X = x)); [contradiction|].
      reflexivity.
    - unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b; simpl.
      destruct (evm !! n); simpl; split; reflexivity.
    - unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b; simpl.
      destruct (decide (n = dbi)).
      + subst. rewrite Hdbi. simpl. split; [reflexivity|].
        destruct (decide (X = X)); [|contradiction].
        simpl.
        reflexivity.
      + pose proof (Hneq := n0).
        apply Nat.eqb_neq in n0.
        remember (svm !! n) as svm_n.
        destruct svm_n; split; try reflexivity.
        simpl.
        symmetry in Heqsvm_n.
        specialize (Hinj n dbi s X Heqsvm_n Hdbi).
        unfold not in Hneq.
        destruct (decide (X = s)); auto.
    - unfold no_negative_occurrence_db_b, no_positive_occurrence_db_b; simpl.
      split; reflexivity.
    - feed specialize IHϕ1.
      { eapply svar_is_fresh_in_app_l. apply Hfresh. }
      feed specialize IHϕ2.
      { eapply svar_is_fresh_in_app_r. apply Hfresh. }
      clear Hfresh.

      simpl.
      remember (to_NamedPattern' ϕ1 evm svm) as tnϕ1.
      destruct tnϕ1 as [[nphi1 evm'] svm'].
      remember (to_NamedPattern' ϕ2 evm' svm') as tnϕ2.
      destruct tnϕ2 as [[nphi2 evm''] svm''].
      simpl.

      (* For some reason, simpl did not simplify this. So we unfold and fold manually. *)
      unfold no_negative_occurrence_db_b.
      fold (no_negative_occurrence_db_b dbi ϕ1).
      fold (no_negative_occurrence_db_b dbi ϕ2).

      (* The same. *)
      unfold no_positive_occurrence_db_b.
      fold (no_positive_occurrence_db_b dbi ϕ1).
      fold (no_positive_occurrence_db_b dbi ϕ2).

      pose proof (IHϕ10 := IHϕ1 evm svm Hinj Hdbi).
      rewrite -Heqtnϕ1 in IHϕ10. simpl in IHϕ10. destruct IHϕ10 as [IHϕ11 IHϕ12].


      (* TODO: prove that a call to [to_NamedPattern'] preserves injectivity. *)
      (*
      pose proof (IHϕ20 := IHϕ2 evm' svm' Hinj Hdbi).

      rewrite -Heqtnϕ2 in IHϕ20.
      destruct IHϕ20 as [IHϕ21 IHϕ22].

      (* simpl in , IHϕ21, IHϕ22. *)
      simpl in IHϕ11, IHϕ12.
      rewrite IHϕ11 IHϕ12.
      rewrite -Heqtnϕ2 in IHϕ21.
       *)
  Abort.


  Fixpoint named_well_formed_positive (phi : NamedPattern) : bool :=
    match phi with
    | npatt_evar _ => true
    | npatt_svar _ => true
    | npatt_sym _ => true
    | npatt_app psi1 psi2 => named_well_formed_positive psi1 && named_well_formed_positive psi2
    | npatt_bott => true
    | npatt_imp psi1 psi2 => named_well_formed_positive psi1 && named_well_formed_positive psi2
    | npatt_exists _ psi => named_well_formed_positive psi
    | npatt_mu X psi => named_no_negative_occurrence X psi && named_well_formed_positive psi
    end.

  Definition named_well_formed := named_well_formed_positive.

  Inductive Named_Application_context : Type :=
  | nbox
  | nctx_app_l (cc : Named_Application_context) (p : NamedPattern) (Prf : named_well_formed p)
  | nctx_app_r (p : NamedPattern) (cc : Named_Application_context) (Prf : named_well_formed p)
  .

  Fixpoint named_subst_ctx (C : Named_Application_context) (p : NamedPattern)
    : NamedPattern :=
    match C with
    | nbox => p
    | @nctx_app_l C' p' prf => npatt_app (named_subst_ctx C' p) p'
    | @nctx_app_r p' C' prf => npatt_app p' (named_subst_ctx C' p)
    end.

(*
  Print well_formed_positive.


  Inductive NML_proof_system (theory : propset NamedPattern) :
    NamedPattern -> Set :=

  (* Hypothesis *)
  | hypothesis (axiom : Pattern) :
      well_formed axiom ->
      (axiom ∈ theory) -> theory ⊢ axiom

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
      theory ⊢ (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi))

  (* Existential generalization *)
  | Ex_gen (phi1 phi2 : Pattern) (x : evar) :
      well_formed phi1 -> well_formed phi2 ->
      theory ⊢ (phi1 ---> phi2) ->
      x ∉ (free_evars phi2) ->
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
      well_formed (ex , phi) -> well_formed psi ->
      theory ⊢ (((ex , phi) $ psi) ---> (ex , phi $ psi))

  | Prop_ex_right (phi psi : Pattern) :
      well_formed (ex , phi) -> well_formed psi ->
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
      well_formed phi -> well_formed psi ->
      theory ⊢ phi -> theory ⊢ (free_svar_subst phi psi X)

  (* Pre-Fixpoint *)
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

*)*)
  
End named.

(*
Section named_test.

  Inductive Symbols : Set := a.
  Instance Symbols_dec : EqDecision Symbols.
  Proof.
    unfold EqDecision. intros x y. unfold Decision.
    repeat decide equality.
  Defined.

  #[local]
  Program Instance Symbols_fin : Finite Symbols
  := {|
    enum := [a];
  |}.
  Next Obligation.
    repeat constructor; set_solver.
  Qed.
  Next Obligation.
    intros []. set_solver.
  Qed.


  Definition sig : Signature :=
    {| variables := StringMLVariables;
       ml_symbols := {|
         symbols := Symbols;
         sym_eqdec := Symbols_dec;
       |} ;
    |}.

  (* Consider the following pattern in locally nameless representation:
       ex, ex, 0 ---> ex, 0
     When we convert this to a named pattern, we want to maintain the invariant
     that identical subterms are equivalent using normal equalty. Specifically,
     the `ex, 0` terms appearing on both sides of the implication should be
     converted to identical named patterns. However, when we convert the above
     pattern using `to_NamedPattern`, we get
       ex x0, ex x1, x1 ---> ex x0, x0
     Now, we have no identical subterms on both sides of the implication.
     However, using `to_Named_Pattern2` on the same initial pattern, we get
       ex x0, ex x1, x1 ---> ex x1, x1
     This time, we maintain the identical subterm invariant.
     This example is shown below, along with an analogous version for mu patterns.
  *)
  Definition phi_ex1 := (@patt_exists sig (patt_exists (patt_bound_evar 0))).
  Definition phi_ex2 := (@patt_exists sig (patt_bound_evar 0)).
  Definition phi_ex := (patt_imp phi_ex1 phi_ex2).
  Compute to_NamedPattern phi_ex.
  Compute to_NamedPattern2 phi_ex.

  Compute to_NamedPattern2 (@patt_mu sig (patt_mu (patt_bound_svar 1))).

  Compute to_NamedPattern2 (@patt_mu sig (patt_imp (patt_mu (patt_bound_svar 1)) (patt_bound_svar 0))).

  Definition phi_mu1 := (@patt_mu sig (patt_mu (patt_bound_svar 0))).
  Definition phi_mu2 := (@patt_mu sig (patt_bound_svar 0)).
  Definition phi_mu := (patt_imp phi_mu1 phi_mu2).
  Compute to_NamedPattern phi_mu.
  Compute to_NamedPattern2 phi_mu.

End named_test.
*)

Arguments named_evars _ / phi.
Arguments named_svars _ / phi.