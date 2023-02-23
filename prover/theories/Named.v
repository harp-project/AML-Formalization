From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base pmap gmap fin_maps finite.
From MatchingLogic Require Import
  Syntax
  Utils.stdpp_ext
.

Require Import String.

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

  Fixpoint named_evars (phi : NamedPattern) : EVarSet :=
    match phi with
    | npatt_evar x => singleton x
    | npatt_svar X => empty
    | npatt_sym sigma => empty
    | npatt_app phi1 phi2 => union (named_evars phi1) (named_evars phi2)
    | npatt_bott => empty
    | npatt_imp phi1 phi2 => union (named_evars phi1) (named_evars phi2)
    | npatt_exists x phi => union (named_evars phi) (singleton x)
    | npatt_mu X phi => named_evars phi
    end.

  Fixpoint named_svars (phi : NamedPattern) : SVarSet :=
    match phi with
    | npatt_evar x => empty
    | npatt_svar X => singleton X
    | npatt_sym sigma => empty
    | npatt_app phi1 phi2 => union (named_svars phi1) (named_svars phi2)
    | npatt_bott => empty
    | npatt_imp phi1 phi2 => union (named_svars phi1) (named_svars phi2)
    | npatt_exists x phi => named_svars phi
    | npatt_mu X phi => union (named_svars phi) (singleton X)
    end.

  Lemma named_free_evars_subseteq_named_evars ϕ:
    named_free_evars ϕ ⊆ named_evars ϕ.
  Proof.
    induction ϕ; cbn; set_solver.
  Qed.

  Lemma named_free_svars_subseteq_named_svars ϕ:
    named_free_svars ϕ ⊆ named_svars ϕ.
  Proof.
    induction ϕ; cbn; set_solver.
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

  CoInductive SVarGen := mkSvarGen {
    sg_get : gset svar -> svar ;
    sg_get_correct : forall svs, sg_get svs ∉ svs ;
    sg_next : gset svar -> SVarGen ;
  }.

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

  Definition eg_getf (eg : EVarGen) (ϕ : NamedPattern) : evar
    := eg_get eg (named_free_evars ϕ)
  .

  Lemma eg_getf_correct (eg : EVarGen) (ϕ : NamedPattern) :
    (eg_getf eg ϕ) ∉ (named_free_evars ϕ)
  .
  Proof.
    apply eg_get_correct.
  Qed.

  Definition eg_nextf (eg : EVarGen) (ϕ : NamedPattern) : EVarGen
    := eg_next eg (named_free_evars ϕ)
  .

  Definition sg_getf (sg : SVarGen) (ϕ : NamedPattern) : svar
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
  .


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

  (*
  (* substitute variable x for psi in phi: phi[psi/x] *)
  Fixpoint named_evar_subst'
    (eg : EVarGen) (phi ψ : NamedPattern) (x : evar) : NamedPattern :=
    match phi with
    | npatt_evar x' => if decide (x = x') is left _ then ψ else npatt_evar x'
    | npatt_svar X => npatt_svar X
    | npatt_sym sigma => npatt_sym sigma
    | npatt_app phi1 phi2 => npatt_app (named_evar_subst' eg phi1 ψ x)
                                       (named_evar_subst' eg phi2 ψ x)
    | npatt_bott => npatt_bott
    | npatt_imp phi1 phi2 => npatt_imp (named_evar_subst' eg phi1 ψ x)
                                       (named_evar_subst' eg phi2 ψ x)
    | npatt_exists x' phi'
      => match (decide (x = x')) with
         | left _ => (
            match (decide (x' ∈ named_free_evars ψ)) with
            | left _ =>
              let avoid := union (named_free_evars ψ) (named_free_evars phi') in
              let fresh_x := eg_get eg avoid in
              let renamed_phi' := (named_evar_subst' eg phi' (npatt_evar fresh_x) x) in
              npatt_exists fresh_x (named_evar_subst' eg renamed_phi' ψ x)
            | right _ => npatt_exists x' (named_evar_subst' eg phi' ψ x)
            end
           )
         | right _ => (
            npatt_exists x' phi'
           )
         end
    | npatt_mu X phi'
      => npatt_mu X (named_evar_subst' eg phi' ψ x)
    end.
    *)

  (* FIXME this is wrong *)
  (* substitute variable X for psi in phi: phi[psi/X] *)
  Fixpoint named_svar_subst'
    (sg : SVarGen)
    (phi psi : NamedPattern) (X : svar) :=
    match phi with
    | npatt_evar x => npatt_evar x
    | npatt_svar X' => if decide (X = X') is left _ then psi else npatt_svar X'
    | npatt_sym sigma => npatt_sym sigma
    | npatt_app phi1 phi2 => npatt_app (named_svar_subst' sg phi1 psi X)
                                       (named_svar_subst' sg phi2 psi X)
    | npatt_bott => npatt_bott
    | npatt_imp phi1 phi2 => npatt_imp (named_svar_subst' sg phi1 psi X)
                                       (named_svar_subst' sg phi2 psi X)
    | npatt_exists x phi' => npatt_exists x (named_svar_subst' sg phi' psi X)
    | npatt_mu X' phi' => if decide (X = X') is left _
                          then let fX := sg_getf sg phi' in
                               npatt_mu fX (named_svar_subst' (sg_nextf sg phi') phi' (npatt_svar fX) X)
                          else npatt_mu X' (named_svar_subst' sg phi' psi X)
    end.

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
  (*
  Definition npatt_nu (phi : NamedPattern) (X : svar) :=
    npatt_not (npatt_mu X (npatt_not (named_svar_subst phi (npatt_not (npatt_svar X)) X))).
*)

  Definition not_contain_bound_evar_0 ϕ : Prop := ~~ bevar_occur ϕ 0.
  Definition not_contain_bound_svar_0 ϕ : Prop := ~~ bsvar_occur ϕ 0.

  Definition is_bound_evar (ϕ : Pattern) : Prop := exists b, ϕ = patt_bound_evar b.

  Global Instance is_bound_evar_dec (ϕ : Pattern) : Decision (is_bound_evar ϕ).
  Proof.
    unfold Decision; destruct ϕ; simpl;
      try solve[right; intros [b Hcontra]; inversion Hcontra].
    left. exists n. reflexivity.
  Defined.

  Definition is_bound_svar (ϕ : Pattern) : Prop := exists b, ϕ = patt_bound_svar b.

  Global Instance is_bound_svar_dec (ϕ : Pattern) : Decision (is_bound_svar ϕ).
  Proof.
    unfold Decision; destruct ϕ; simpl;
      try solve[right; intros [b Hcontra]; inversion Hcontra].
    left. exists n. reflexivity.
  Defined.


  Fixpoint named_no_negative_occurrence (X : svar) (ϕ : NamedPattern) : bool :=
    match ϕ with
    | npatt_evar _ | npatt_sym _ | npatt_bott => true
    | npatt_svar Y => true
    | npatt_app ϕ₁ ϕ₂ => named_no_negative_occurrence X ϕ₁ && named_no_negative_occurrence X ϕ₂
    | npatt_imp ϕ₁ ϕ₂ => named_no_positive_occurrence X ϕ₁ && named_no_negative_occurrence X ϕ₂
    | npatt_exists _ ϕ' => named_no_negative_occurrence X ϕ'
    | npatt_mu _ ϕ' => named_no_negative_occurrence X ϕ'
    end
  with
  named_no_positive_occurrence (X : svar) (ϕ : NamedPattern) : bool :=
    match ϕ with
    | npatt_evar _ | npatt_sym _ | npatt_bott => true
    | npatt_svar Y => negb (if decide (X = Y) is left _ then true else false)
    | npatt_app ϕ₁ ϕ₂ => named_no_positive_occurrence X ϕ₁ && named_no_positive_occurrence X ϕ₂
    | npatt_imp ϕ₁ ϕ₂ => named_no_negative_occurrence X ϕ₁ && named_no_positive_occurrence X ϕ₂
    | npatt_exists _ ϕ' => named_no_positive_occurrence X ϕ'
    | npatt_mu _ ϕ' => named_no_positive_occurrence X ϕ'
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

End named.

Section named_test.

  Definition StringMLVariables : MLVariables :=
    {| evar := string;
       svar := string;
    |}.

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
