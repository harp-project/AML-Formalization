From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import base pmap gmap.
From MatchingLogic Require Import Syntax.


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

  Check @kmap.
  (* TODO: use kmap. Check kmap. *)
  Definition evm_incr (evm : EVarMap) : EVarMap :=
    kmap S evm.

  Definition svm_incr (svm : SVarMap) : SVarMap :=
    kmap S svm.

  Definition evm_fresh (evm : EVarMap) (ϕ : Pattern) : evar
    := evar_fresh (elements (free_evars ϕ ∪ (list_to_set (map snd (map_to_list evm))))).

  Definition svm_fresh (svm : SVarMap) (ϕ : Pattern) : svar
    := svar_fresh (elements (free_svars ϕ ∪ (list_to_set (map snd (map_to_list svm))))).
  
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
         | _ => (npatt_bott, cache, used_evars, used_svars)
         end
      in
      (ψ, <[ϕ:=ψ]>cache', used_evars', used_svars).
  
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
    | npatt_svar Y => negb (if decide (X = Y) then true else false)
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
        rewrite Nat.eqb_refl.
        reflexivity.
      + pose proof (Hneq := n0).
        apply Nat.eqb_neq in n0.
        rewrite n0. simpl.
        clear n0.
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
