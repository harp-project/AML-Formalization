From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base pmap gmap.
From MatchingLogic Require Import Syntax.

Require Import String.

Section named.
  Context
    {Σ : Signature}
    {symbols_countable : Countable symbols}
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

  Instance NamedPattern_eqdec : EqDecision NamedPattern.
  Proof. solve_decision. Defined.

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

  Definition named_fresh_evar ϕ := evar_fresh (elements (named_free_evars ϕ)).
  Definition named_fresh_svar ϕ := svar_fresh (elements (named_free_svars ϕ)).

  (* substitute variable x for psi in phi: phi[psi/x] *)
  Fixpoint named_evar_subst (phi psi : NamedPattern) (x : evar) :=
    match phi with
    | npatt_evar x' => if decide (x = x') is left _ then psi else npatt_evar x'
    | npatt_svar X => npatt_svar X
    | npatt_sym sigma => npatt_sym sigma
    | npatt_app phi1 phi2 => npatt_app (named_evar_subst phi1 psi x)
                                       (named_evar_subst phi2 psi x)
    | npatt_bott => npatt_bott
    | npatt_imp phi1 phi2 => npatt_imp (named_evar_subst phi1 psi x)
                                       (named_evar_subst phi2 psi x)
    | npatt_exists x' phi' => if decide (x = x') is left _
                              then let fx := named_fresh_evar phi' in
                                   npatt_exists fx (named_evar_subst phi' (npatt_evar fx) x)
                              else npatt_exists x' (named_evar_subst phi' psi x)
    | npatt_mu X phi' => npatt_mu X (named_evar_subst phi' psi x)
    end.

  (* substitute variable X for psi in phi: phi[psi/X] *)
  Fixpoint named_svar_subst (phi psi : NamedPattern) (X : svar) :=
    match phi with
    | npatt_evar x => npatt_evar x
    | npatt_svar X' => if decide (X = X') is left _ then psi else npatt_svar X'
    | npatt_sym sigma => npatt_sym sigma
    | npatt_app phi1 phi2 => npatt_app (named_svar_subst phi1 psi X)
                                       (named_svar_subst phi2 psi X)
    | npatt_bott => npatt_bott
    | npatt_imp phi1 phi2 => npatt_imp (named_svar_subst phi1 psi X)
                                       (named_svar_subst phi2 psi X)
    | npatt_exists x phi' => npatt_exists x (named_svar_subst phi' psi X)
    | npatt_mu X' phi' => if decide (X = X') is left _
                          then let fX := named_fresh_svar phi' in
                               npatt_mu fX (named_svar_subst phi' (npatt_svar fX) X)
                          else npatt_mu X' (named_svar_subst phi' psi X)
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
  Definition npatt_nu (phi : NamedPattern) (X : svar) :=
    npatt_not (npatt_mu X (npatt_not (named_svar_subst phi (npatt_not (npatt_svar X)) X))).

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
              (npatt_exists x nphi, cache', used_evars', used_svars)
         | patt_mu phi
           => let: X := svs_fresh used_svars phi in
              let: used_svars_ex := used_svars ∪ {[X]} in
              let: cache_ex := <[patt_bound_svar 0:=npatt_svar X]>(cache_incr_svar cache) in
              let: (nphi, cache', used_evars', used_svars')
                 := to_NamedPattern2' phi cache_ex used_evars used_svars_ex in
              (npatt_mu X nphi, cache', used_evars', used_svars)
         end
      in
      (ψ, <[ϕ:=ψ]>cache', used_evars', used_svars).

  Definition to_NamedPattern2 (ϕ : Pattern) : NamedPattern :=
    (to_NamedPattern2' ϕ gmap_empty ∅ ∅).1.1.1.
  
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

*)
  
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

  Definition sig : Signature :=
    {| variables := StringMLVariables;
       symbols := Symbols;
       sym_eqdec := Symbols_dec;
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

  Definition phi_mu1 := (@patt_mu sig (patt_mu (patt_bound_svar 0))).
  Definition phi_mu2 := (@patt_mu sig (patt_bound_svar 0)).
  Definition phi_mu := (patt_imp phi_mu1 phi_mu2).
  Compute to_NamedPattern phi_mu.
  Compute to_NamedPattern2 phi_mu.

End named_test.
