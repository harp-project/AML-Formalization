From Coq Require Import ssreflect ssrfun ssrbool.

From Coq.Logic Require Import FunctionalExtensionality PropExtensionality Classical_Pred_Type Classical_Prop.
From Coq.micromega Require Import Lia.
From Coq.Program Require Import Wf.

From Equations Require Import Equations.

From stdpp Require Import base fin_sets.
From stdpp Require Import pmap gmap mapset fin_sets sets propset list_numbers.

From MatchingLogic.Utils Require Import Lattice stdpp_ext extralibrary.
From MatchingLogic Require Import
  Syntax
  Freshness
  NamedAxioms
  IndexManipulation
.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Substitution.Notations.

(** ** Matching Logic Semantics *)
Section semantics.

  Context {signature : Signature}.
  Open Scope ml_scope.

  (* Model of AML ref. snapshot: Definition 2 *)

  Polymorphic Cumulative
  Record Model := {
    Domain :> Type;
    Domain_inhabited :> Inhabited Domain;
    app_interp : Domain -> Domain -> propset Domain;
    sym_interp (sigma : symbols) : propset Domain;
  }.

  Section with_model.
    Context {M : Model}.

  Definition Empty : propset (Domain M) := @empty (propset (Domain M)) _.
  Definition Full : propset (Domain M) := @top (propset (Domain M)) _.

  (* full set and empty set are distinct *)
  Lemma empty_impl_not_full : forall (S : propset (Domain M)),
      S = Empty -> S <> Full.
  Proof.
    intros S H.
    intros HContra. rewrite -> HContra in H.
    assert (Hw1: (@inhabitant _ (Domain_inhabited M)) ∈ Full).
    { unfold Full. apply elem_of_top. exact I. }
    rewrite H in Hw1.
    unfold Empty in Hw1.
    apply not_elem_of_empty in Hw1. exact Hw1.
  Qed.

  Lemma full_impl_not_empty : forall (S : propset (Domain M)),
      S = Full -> S <> Empty.
  Proof.
    intros S H HContra.
    rewrite -> HContra in H.
    assert (Hw1: (@inhabitant _ (Domain_inhabited M)) ∈ Full).
    { unfold Full. apply elem_of_top. exact I. }
    rewrite <- H in Hw1.
    unfold Empty in Hw1.
    apply not_elem_of_empty in Hw1. exact Hw1.
  Qed.

  (* element and set variable valuations *)
  Polymorphic Record Valuation : Type := mkValuation
  { evar_valuation : evar -> Domain M ;
    svar_valuation : svar -> propset (Domain M) ;
  }.

  Definition update_evar_val
    (ev : evar) (x : Domain M) (val : Valuation) : Valuation :=
    {|
    evar_valuation := fun ev' : evar =>
      if decide (ev = ev') is left _ then x else evar_valuation val ev' ;
    svar_valuation := (svar_valuation val)
    |}.

  Definition update_svar_val
    (sv : svar) (X : propset (Domain M)) (val : Valuation) : Valuation :=
    {| 
    evar_valuation := (evar_valuation val);
    svar_valuation := fun sv' : svar =>
      if decide (sv = sv') is left _ then X else svar_valuation val sv' ;
    |}.

  Lemma update_evar_val_svar_val_comm
    (ev : evar) (x : Domain M)
    (sv : svar) (X : propset (Domain M))
    (ρ : Valuation) :
    update_evar_val ev x (update_svar_val sv X ρ)
    = update_svar_val sv X (update_evar_val ev x ρ).
  Proof.
    unfold update_evar_val, update_svar_val. simpl.
    reflexivity.
  Qed.

  Lemma update_svar_val_comm :
    forall (X1 X2 : svar) (S1 S2 : propset (Domain M)) (ρ : Valuation),
      X1 <> X2 ->
      update_svar_val X1 S1 (update_svar_val X2 S2 ρ)
      = update_svar_val X2 S2 (update_svar_val X1 S1 ρ).
  Proof.
    intros.
    unfold update_svar_val. simpl. f_equal.
    apply functional_extensionality.
    intros.
    destruct (decide (X1 = x)),(decide (X2 = x)); subst.
    * unfold not in H. assert (x = x). reflexivity. apply H in H0. destruct H0.
    * reflexivity.
    * reflexivity.
    * reflexivity.
  Qed.

  Lemma update_svar_val_shadow : forall (X : svar)
                                        (S1 S2 : propset (Domain M))
                                        (ρ : Valuation),
      update_svar_val X S1 (update_svar_val X S2 ρ) = update_svar_val X S1 ρ.
  Proof.
    intros. unfold update_svar_val. simpl.
    f_equal.
    apply functional_extensionality.
    intros. destruct (decide (X = x)); reflexivity.
  Qed.

  Lemma update_svar_val_neq (ρ : Valuation) X1 S X2 :
    X1 <> X2 -> svar_valuation (update_svar_val X1 S ρ) X2 = svar_valuation ρ X2.
  Proof.
    unfold update_svar_val. intros. simpl.
    destruct (decide (X1 = X2)); simpl.
    - contradiction.
    - auto.
  Qed.
  
  Lemma update_evar_val_comm :
    forall (x1 x2 : evar) (m1 m2 : Domain M) (ρ : Valuation),
      x1 <> x2 ->
      update_evar_val x1 m1 (update_evar_val x2 m2 ρ)
      = update_evar_val x2 m2 (update_evar_val x1 m1 ρ).
  Proof.
    intros.
    unfold update_evar_val. simpl. f_equal.
    apply functional_extensionality.
    intros.
    destruct (decide (x1 = x)),(decide (x2 = x)); subst.
    * unfold not in H. assert (x = x). reflexivity. apply H in H0. destruct H0.
    * reflexivity.
    * reflexivity.
    * reflexivity.
  Qed.

  Lemma update_evar_val_shadow : forall (x : evar)
                                        (m1 m2 : Domain M)
                                        (ρ : Valuation),
      update_evar_val x m1 (update_evar_val x m2 ρ) = update_evar_val x m1 ρ.
  Proof.
    intros. unfold update_evar_val. simpl. f_equal. apply functional_extensionality.
    intros. destruct (decide (x = x0)); reflexivity.
  Qed.

  Lemma update_evar_val_same x m ρ :
    evar_valuation (update_evar_val x m ρ) x = m.
  Proof.
    unfold update_evar_val. simpl.
    rewrite decide_eq_same. reflexivity.
  Qed.

  Lemma update_evar_val_neq (ρ : Valuation) x1 e x2 :
    x1 <> x2 -> evar_valuation (update_evar_val x1 e ρ) x2 = evar_valuation ρ x2.
  Proof.
    unfold update_evar_val. simpl. intros.
    destruct (decide (x1 = x2)); simpl.
    - contradiction.
    - auto.
  Qed.

  Lemma update_evar_val_same_2 x ρ :
    update_evar_val x (evar_valuation ρ x) ρ = ρ.
  Proof.
    destruct ρ as [ρₑ ρₛ]. simpl. unfold update_evar_val. simpl. f_equal.
    apply functional_extensionality. intros x0.
    unfold update_evar_val. destruct (decide (x = x0)); simpl.
    - subst. reflexivity.
    - reflexivity.
  Qed.

  Lemma update_svar_val_same X S ρ :
    svar_valuation (update_svar_val X S ρ) X = S.
  Proof.
    unfold update_svar_val. simpl. destruct (decide (X = X)); simpl.
    + reflexivity.
    + contradiction.
  Qed.

  Lemma update_svar_val_same_2 x ρ :
    update_svar_val x (svar_valuation ρ x) ρ = ρ.
  Proof.
    destruct ρ as [ρₑ ρₛ]. simpl. unfold update_svar_val. simpl. f_equal.
    apply functional_extensionality. intros x0.
    unfold update_svar_val. destruct (decide (x = x0)); simpl.
    - subst. reflexivity.
    - reflexivity.
  Qed.


  (* We use propositional extensionality here. *)
  #[export]
  Instance propset_leibniz_equiv : LeibnizEquiv (propset (Domain M)).
  Proof.
    intros x y H. unfold equiv in H. unfold set_equiv_instance in H.
    destruct x,y.
    apply f_equal. apply functional_extensionality.
    intros x. apply propositional_extensionality.
    specialize (H x). destruct H as [H1 H2].
    split; auto.
  Qed.

  (* extending pointwise application *)
  Polymorphic
  Definition app_ext
             (l r : propset (Domain M)) :
    propset (Domain M) :=
    PropSet (fun (e : (Domain M)) => exists (le re : (Domain M)), le ∈ l /\ re ∈ r /\ e ∈ (app_interp _) le re).

  Lemma app_ext_bot_r :
      forall S : propset (Domain M),
        app_ext S ∅ = ∅.
  Proof.
    intros S. unfold app_ext.
    rewrite -> elem_of_equiv_empty_L.
    intros x Hcontra. rewrite -> elem_of_PropSet in Hcontra.
    destruct Hcontra as [le [re [H1 [H2 H3] ] ] ].
    apply not_elem_of_empty in H2. exact H2.
  Qed.

  Lemma app_ext_bot_l :
      forall S : propset (Domain M),
        app_ext ∅ S = ∅.
  Proof.
    intros S. unfold app_ext.
    rewrite -> elem_of_equiv_empty_L.
    intros x Hcontra. rewrite -> elem_of_PropSet in Hcontra.
    destruct Hcontra as [le [re [H1 [H2 H3] ] ] ].
    apply not_elem_of_empty in H1. exact H1.
  Qed.

  Lemma app_ext_monotonic_l :
      forall (S1 S2 S : propset (Domain M)),
        S1 ⊆ S2 -> (app_ext S1 S) ⊆ (app_ext S2 S).
  Proof.
    intros S1 S2 S H. rewrite -> elem_of_subseteq in H.
    rewrite -> elem_of_subseteq. intros x H'.
    unfold app_ext in H'.
    rewrite -> elem_of_PropSet in H'.
    destruct H' as [le [re [H1 [H2 H3] ] ] ].
    unfold app_ext.
    rewrite -> elem_of_PropSet.
    exists le,re. firstorder.
  Qed.

  Lemma app_ext_monotonic_r :
      forall (S S1 S2 : propset (Domain M)),
        S1 ⊆ S2 -> (app_ext S S1) ⊆ (app_ext S S2).
  Proof.
    intros S1 S2 S H. rewrite -> elem_of_subseteq in H.
    rewrite -> elem_of_subseteq. intros x H'.
    unfold app_ext in H'.
    rewrite -> elem_of_PropSet in H'.
    destruct H' as [le [re [H1 [H2 H3] ] ] ].
    unfold app_ext.
    rewrite -> elem_of_PropSet.
    exists le,re. firstorder.
  Qed.


  (* Semantics of AML ref. snapshot: Definition 3 *)

    Let OS := PropsetOrderedSet (Domain M).
    Let  L := PowersetLattice (Domain M).

    Equations? eval (ρ : Valuation) (ϕ : Pattern)
      : propset (@Domain M) by wf (size ϕ) :=
    eval ρ (patt_free_evar x)  := {[ evar_valuation ρ x ]} ;
    eval ρ (patt_free_svar X)  := svar_valuation ρ X ;
    eval ρ (patt_bound_evar n) := ∅ ;
    eval ρ (patt_bound_svar n) := ∅ ;
    eval ρ (patt_sym s)        := @sym_interp M s ;
    eval ρ (patt_app ϕ₁ ϕ₂)    := app_ext (eval ρ ϕ₁) (eval ρ ϕ₂) ;
    eval ρ (patt_bott)         := ∅ ;
    eval ρ (patt_imp ϕ₁ ϕ₂)    := (difference ⊤ (eval ρ ϕ₁)) ∪ (eval ρ ϕ₂) ;
    eval ρ (patt_exists ϕ')    := let x := fresh_evar ϕ' in
                                  propset_fa_union
                                  (fun e =>
                                    let ρ' := (update_evar_val x e ρ) in
                                    eval ρ' (ϕ'^{evar: 0 ↦ x})
                                  ) ;
    eval ρ (patt_mu ϕ')        := let X := fresh_svar ϕ' in
                                  @LeastFixpointOf _ OS L
                                  (fun S =>
                                    let ρ' := (update_svar_val X S ρ) in
                                    eval ρ' (ϕ'^{svar: 0 ↦ X})
                                  ) .
    Proof.
      all: simpl; try lia.
      { rewrite -evar_open_size. lia. }
      { rewrite -svar_open_size. lia. }
    Defined.

    Definition Fassoc ρ ϕ X :=
      λ S, eval (update_svar_val X S ρ) ϕ.

    Lemma eval_free_evar_simpl
          (ρ : Valuation)
          (x : evar) :
      eval ρ (patt_free_evar x) = {[ evar_valuation ρ x ]}.
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_free_svar_simpl
          (ρ : Valuation)
          (X : svar) :
      eval ρ (patt_free_svar X) = svar_valuation ρ X.
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_bound_evar_simpl
          (ρ : Valuation)
          (x : db_index) :
      eval ρ (patt_bound_evar x) = ∅.
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_bound_svar_simpl
          (ρ : Valuation)
          (X : db_index) :
      eval ρ (patt_bound_svar X) = ∅.
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_sym_simpl
          (ρ : Valuation)
          (s : symbols) :
      eval ρ (patt_sym s) = @sym_interp M s.
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_app_simpl
          (ρ : Valuation)
          (ϕ₁ ϕ₂ : Pattern) :
      eval ρ (patt_app ϕ₁ ϕ₂) = app_ext (eval ρ ϕ₁) (eval ρ ϕ₂).
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_bott_simpl
          (ρ : Valuation) :
      eval ρ patt_bott = ∅.
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_imp_simpl
          (ρ : Valuation)
          (ϕ₁ ϕ₂ : Pattern) :
      eval ρ (patt_imp ϕ₁ ϕ₂) = (difference ⊤ (eval ρ ϕ₁)) ∪ (eval ρ ϕ₂).
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_ex_simpl
          (ρ : Valuation)
          (ϕ' : Pattern) :
      eval ρ (patt_exists ϕ') =
      let x := fresh_evar ϕ' in
      propset_fa_union
      (fun e =>
        let ρ' := (update_evar_val x e ρ) in
        eval ρ' (ϕ'^{evar: 0 ↦ x})
      ).
    Proof. simp eval. reflexivity. Qed.

    Lemma eval_mu_simpl
          (ρ : Valuation)
          (ϕ' : Pattern) :
      eval ρ (patt_mu ϕ') =
      let X := fresh_svar ϕ' in
      @LeastFixpointOf _ OS L
      (fun S =>
        let ρ' := (update_svar_val X S ρ) in
        eval ρ' (ϕ'^{svar: 0 ↦ X})
      ).
    Proof. simp eval. reflexivity. Qed.

    (* TODO extend with derived constructs using typeclasses *)
    Definition eval_simpl :=
      ( eval_free_evar_simpl,
        eval_free_svar_simpl,
        eval_bound_evar_simpl,
        eval_bound_svar_simpl,
        eval_sym_simpl,  
        eval_app_simpl,
        eval_bott_simpl,
        eval_imp_simpl,
        eval_ex_simpl,
        eval_mu_simpl
      ).

End with_model.

Section with_explicit_model.
  Context (M : Model).
  (* Model predicate. Useful mainly if the pattern is well-formed. *)
  Definition M_predicate (ϕ : Pattern) : Prop := forall ρ,
      @eval M ρ ϕ = ⊤ \/ eval ρ ϕ = ∅.

  Lemma M_predicate_impl ϕ₁ ϕ₂ : M_predicate ϕ₁ -> M_predicate ϕ₂ -> M_predicate (patt_imp ϕ₁ ϕ₂).
  Proof.
    unfold M_predicate. intros Hp1 Hp2 ρ.
    specialize (Hp1 ρ). specialize (Hp2 ρ).
    rewrite -> eval_imp_simpl.
    destruct Hp1, Hp2; rewrite -> H; rewrite -> H0.
    + left. set_solver by fail.
    + right. set_solver by fail.
    + left. set_solver by fail.
    + left. set_solver by fail.
  Qed.

  Hint Resolve M_predicate_impl : core.

  Lemma M_predicate_bott : M_predicate patt_bott.
  Proof.
    unfold M_predicate. intros. right.
    apply eval_bott_simpl.
  Qed.

  Hint Resolve M_predicate_bott : core.

  Lemma M_predicate_exists ϕ :
    let x := evar_fresh (elements (free_evars ϕ)) in
    M_predicate (ϕ^{evar: 0 ↦ x}) -> M_predicate (patt_exists ϕ).
  Proof.
    simpl. unfold M_predicate. intros.
    rewrite -> eval_ex_simpl.
    simpl.
    pose proof (H' := classic
                        (exists e : Domain M,
                            (eval
                               (update_evar_val (evar_fresh (elements (free_evars ϕ))) e ρ)
                               (ϕ^{evar: 0 ↦ evar_fresh (elements (free_evars ϕ))})
                            = ⊤))).
    destruct H'.
    - (* For some member, the subformula evaluates to full set. *)
      left.
      apply set_eq_subseteq.
      split.
      { set_solver by fail. }
      apply elem_of_subseteq.
      intros x _.
      destruct H0 as [x0 H0]. unfold fresh_evar.
      unfold propset_fa_union. rewrite -> elem_of_PropSet.
      exists x0. rewrite H0. apply elem_of_top'.
    - (* The subformula does not evaluate to full set for any member. *)
      right.
      apply set_eq_subseteq.
      split.
      2: { apply empty_subseteq. }
      apply elem_of_subseteq.
      intros x H1.
      unfold propset_fa_union in H1.
      rewrite -> elem_of_PropSet in H1.
      destruct H1 as [c H1].
      unfold not in H0.
      specialize (H (update_evar_val (evar_fresh (elements (free_evars ϕ))) c ρ)).
      destruct H.
      + exfalso. apply H0. exists c. apply H.
      + apply set_eq_subseteq in H. destruct H as [H _].
        rewrite ->  elem_of_subseteq in H. auto.
  Qed.

  Hint Resolve M_predicate_exists : core.

  Lemma predicate_not_empty_iff_full ϕ ρ :
    M_predicate ϕ ->
    @eval M ρ ϕ <> ∅ <->
    eval ρ ϕ = ⊤.
  Proof.
    intros Hmp.
    split.
    - intros Hne. specialize (Hmp ρ).
      destruct Hmp.
      + assumption.
      + contradiction.
    - intros Hf.
      apply full_impl_not_empty.
      assumption.
  Qed.

  Lemma predicate_not_full_iff_empty ϕ ρ :
    M_predicate ϕ ->
    @eval M ρ ϕ <> ⊤ <->
    eval ρ ϕ = ∅.
  Proof.
    intros Hmp.
    split.
    - intros Hne. specialize (Hmp ρ).
      destruct Hmp.
      + contradiction.
      + assumption.
    - intros Hf.
      apply empty_impl_not_full.
      assumption.
  Qed.

  Lemma eval_impl_MP ϕ₁ ϕ₂ ρ :
    @eval M ρ (patt_imp ϕ₁ ϕ₂) = ⊤ ->
    eval ρ ϕ₁ = ⊤ ->
    eval ρ ϕ₂ = ⊤.
  Proof.
    unfold Full.
    rewrite eval_imp_simpl.
    intros H1 H2.
    rewrite -> H2 in H1.
    set_solver by auto.
  Qed.

  Lemma eval_predicate_impl ϕ₁ ϕ₂ ρ :
    M_predicate ϕ₁ ->
    @eval M ρ (patt_imp ϕ₁ ϕ₂) = ⊤
    <-> (eval ρ ϕ₁ = ⊤
         -> eval ρ ϕ₂ = ⊤).
  Proof.
    intros Hpred.
    split.
    - intros H H1.
      apply (eval_impl_MP _ _ _ H H1).
    - intros H.
      rewrite -> eval_imp_simpl.
      destruct (classic (eval ρ ϕ₁ = ⊤)).
      + specialize (H H0).
        rewrite -> H. rewrite -> H0.
        set_solver by fail.
      + apply predicate_not_full_iff_empty in H0. 2: apply Hpred.
        rewrite -> H0.
        set_solver by fail.
  Qed.
  
  (* ϕ is a well-formed body of ex *)
  Lemma eval_exists_predicate_full ϕ ρ :
    let x := fresh_evar ϕ in
    M_predicate (ϕ^{evar: 0 ↦ x}) ->
    eval ρ (patt_exists ϕ) = ⊤ <->
    ∃ (m : Domain M), eval (update_evar_val x m ρ) (ϕ^{evar: 0 ↦ x}) = ⊤.
  Proof.
    intros x Hpred.
    pose proof (Hpredex := M_predicate_exists _ Hpred).
    rewrite -[eval _ _ = ⊤]predicate_not_empty_iff_full.
    { apply Hpredex. }
    
    (*
        (* TODO: I would like to simplify the RHS, but cannot find a way. *)
        under [fun m => _]functional_extensionality => m.
        (* This fails *)
        Fail rewrite <- predicate_not_empty_iff_full.
        Fail rewrite -[_ = Full]predicate_not_empty_iff_full.
        over.
     *)


    rewrite -> Not_Empty_iff_Contains_Elements.
    split.
    - intros [x0 Hx0].
      rewrite -> eval_ex_simpl in Hx0.
      simpl in Hx0. unfold propset_fa_union in Hx0. rewrite -> elem_of_PropSet in Hx0.
      destruct Hx0 as [c Hc].
      exists c.
      rewrite -predicate_not_empty_iff_full.
      { apply Hpred. }
      rewrite Not_Empty_iff_Contains_Elements.
      exists x0. apply Hc.
    - intros [m Hm].
      apply full_impl_not_empty in Hm.
      apply Not_Empty_iff_Contains_Elements in Hm.
      destruct Hm as [x0 Hx0].
      exists x0.
      rewrite eval_ex_simpl. simpl.
      unfold propset_fa_union. rewrite -> elem_of_PropSet.
      exists m. assumption.
  Qed.

  Lemma eval_exists_empty ϕ ρ :
    let x := fresh_evar ϕ in
    eval ρ (patt_exists ϕ) = ∅ <->
    ∀ (m : Domain M), eval (update_evar_val x m ρ) (ϕ^{evar: 0 ↦ x}) = ∅.
  Proof.
    intros x.
    rewrite -> eval_ex_simpl. simpl.
    rewrite -> set_eq_subseteq.
    split.
    - intros [H1 _] m.
      rewrite -> elem_of_subseteq in H1.
      unfold propset_fa_union in H1.
      setoid_rewrite -> elem_of_PropSet in H1.
      rewrite -> set_eq_subseteq.
      split.
      2: { apply empty_subseteq. }
      rewrite -> elem_of_subseteq.
      intros x0.
      intros Contra.
      specialize (H1 x0). apply H1.
      exists m. assumption.
    - intros H.
      split.
      2: { apply empty_subseteq. }
      rewrite -> elem_of_subseteq.
      intros x0.
      intros Contra.
      unfold propset_fa_union in Contra.
      rewrite -> elem_of_PropSet in Contra.
      destruct Contra as [m Contra].
      rewrite H in Contra.
      exact Contra.
  Qed.


  (* Theory,axiom ref. snapshot: Definition 5 *)
  End with_explicit_model.

  Definition satisfies_model (M : Model) (ϕ : Pattern) : Prop :=
    forall (ρ : Valuation),
      eval (M := M) ρ ϕ = ⊤.

  Definition satisfies_theory (m : Model) (theory : Theory)
    : Prop := forall axiom : Pattern, axiom ∈ theory -> (satisfies_model m axiom).

  (* TODO rename *)
  Definition satisfies (theory : Theory) (p: Pattern)
    : Prop := forall m : Model, (satisfies_theory m theory) -> (satisfies_model m p).

  Lemma satisfies_theory_iff_satisfies_named_axioms {Σ : Signature} NAs M:
    satisfies_theory M (theory_of_NamedAxioms NAs) <->
    forall (n : NAName NAs), satisfies_model M (NAAxiom _ n).
  Proof.
    split.
    - intros. unfold satisfies_theory in H.
      specialize (H (NAAxiom _ n)). apply H.
      unfold In. unfold theory_of_NamedAxioms.
      exists n. auto.
    - intros H.
      intros ax Hax.
      unfold In in Hax.
      unfold theory_of_NamedAxioms in Hax.
      destruct Hax as [axname Haxname].
      subst ax.
      apply H.
  Qed.

  Lemma satisfies_theory_subseteq M Γ₁ Γ₂:
    Γ₁ ⊆ Γ₂ ->
    satisfies_theory M Γ₂ ->
    satisfies_theory M Γ₁.
  Proof.
    unfold satisfies_theory.
    set_solver by fail.
  Qed.


  (* theory predicate *)
  Definition T_predicate Γ ϕ := forall M, satisfies_theory M Γ -> M_predicate M ϕ.

  Hint Extern 4 (M_predicate _ (evar_open _ _ _)) => mlSimpl : core.
  Hint Extern 4 (T_predicate _ (evar_open _ _ _)) => mlSimpl : core.
  Hint Extern 4 (M_predicate _ (svar_open _ _ _)) => mlSimpl : core.
  Hint Extern 4 (T_predicate _ (svar_open _ _ _)) => mlSimpl : core.

  Lemma T_predicate_impl_M_predicate M Γ ϕ:
    satisfies_theory M Γ -> T_predicate Γ ϕ -> M_predicate M ϕ.
  Proof.
    unfold T_predicate. auto.
  Qed.

  Hint Resolve T_predicate_impl_M_predicate : core.

  Lemma T_predicate_impl Γ ϕ₁ ϕ₂ : T_predicate Γ ϕ₁ -> T_predicate Γ ϕ₂ -> T_predicate Γ (patt_imp ϕ₁ ϕ₂).
  Proof.
    unfold T_predicate.
    intros.
    auto using M_predicate_impl.
  Qed.

  Hint Resolve T_predicate_impl : core.

  Lemma T_predicate_bot Γ : T_predicate Γ patt_bott.
  Proof.
    unfold T_predicate.
    intros.
    auto using M_predicate_bott.
  Qed.

  Hint Resolve T_predicate_bot : core.

  (* TODO: top iff exists forall *)

Section with_model.
  Context {M : Model}.

  (* If phi1 \subseteq phi2, then U_x phi1 \subseteq U_x phi2 *)
  Lemma eval_subset_union x ϕ₁ ϕ₂ :
    (forall ρ, (eval ρ ϕ₁) ⊆ (@eval M ρ ϕ₂) )
    -> (forall ρ,
                    (propset_fa_union (fun e => eval (update_evar_val x e ρ) ϕ₁))
                    ⊆
                    (propset_fa_union (fun e => @eval M (update_evar_val x e ρ) ϕ₂))
       ).
  Proof.
    intros H. induction ϕ₁; intros; apply propset_fa_union_included; auto.
  Qed.

  (* eval unchanged when using fresh element varaiable *)
  Lemma eval_free_evar_independent ρ x v ϕ:
    evar_is_fresh_in x ϕ ->
    @eval M (update_evar_val x v ρ) ϕ = eval ρ ϕ.
  Proof.
    intros Hfr. unfold evar_is_fresh_in in Hfr.
    funelim (eval (update_evar_val x v ρ) ϕ); try simp eval; try reflexivity;
      simpl in Hfr.
    - simpl. destruct (decide (x0 = x)); simpl.
      + subst. unfold evar_is_fresh_in in Hfr. simpl in Hfr.
        apply not_elem_of_singleton_1 in Hfr.
        contradiction.
      + reflexivity.
    - rewrite H.
      { set_solver. }
      rewrite H0.
      { set_solver. }
      reflexivity.
    - rewrite H.
      { set_solver. }
      rewrite H0.
      { set_solver. }
      reflexivity.
    - simpl.
      apply f_equal. apply functional_extensionality. intros e.
      destruct (decide ((fresh_evar ϕ') = x)) as [Heq|Hneq].
      + rewrite -> Heq. rewrite -> update_evar_val_shadow. reflexivity.
      + rewrite -> update_evar_val_comm.
        2: apply Hneq.
        rewrite -> H with (e := e).
        { reflexivity. }
        { 
          intros Contra.
          pose proof (Hfeeo := @free_evars_evar_open signature ϕ' (fresh_evar ϕ') 0).
           rewrite -> elem_of_subseteq in Hfeeo.
           specialize (Hfeeo x Contra).
           apply elem_of_union in Hfeeo.
           destruct Hfeeo as [H'|H'].
           * apply elem_of_singleton_1 in H'. symmetry in H'. contradiction.
           * contradiction.
      }
      { f_equal. apply update_evar_val_comm. apply Hneq. }
      { f_equal. apply update_evar_val_comm. apply Hneq. }
    - simpl.
      apply f_equal. apply functional_extensionality.
      intros e.
      rewrite -update_evar_val_svar_val_comm.
      erewrite -> H.
      { reflexivity. }
      { intros Contra.
         rewrite -> free_evars_svar_open in Contra.
         contradiction.
      }
      { reflexivity. }
      rewrite update_evar_val_svar_val_comm.
      reflexivity.
  Qed.

  Lemma eval_free_svar_independent ρ X S ϕ:
    svar_is_fresh_in X ϕ ->
    @eval M (update_svar_val X S ρ) ϕ = eval ρ ϕ.
  Proof.
    intros Hfr. unfold svar_is_fresh_in in Hfr.
    funelim (eval (update_svar_val X S ρ) ϕ);
      try simp eval; try reflexivity;
      simpl in Hfr.
    {
      unfold update_svar_val. simpl.
      destruct (decide (X0 = X)); simpl.
      + subst.
        destruct ρ0 as [ρₑ ρₛ]. simpl.
        apply not_elem_of_singleton_1 in Hfr.
        contradiction.
      + reflexivity.
    }
    {
      rewrite H.
      { set_solver. }
      rewrite H0.
      { set_solver. }
      reflexivity.
    }
    {
      rewrite H.
      { set_solver. }
      rewrite H0.
      { set_solver. }
      reflexivity.
    }
    {
      simpl.
      apply f_equal. apply functional_extensionality. intros e.
      rewrite update_evar_val_svar_val_comm.
      rewrite -> H with (e := e).
      { reflexivity. }
      { apply svar_fresh_evar_open. apply Hfr. }
      { reflexivity. }
      { rewrite update_evar_val_svar_val_comm. reflexivity. }
    }
    {
      apply f_equal. apply functional_extensionality.
      intros e. simpl.
      destruct (decide ((fresh_svar ϕ') = X)) as [Heq|Hneq].
      + rewrite Heq. rewrite update_svar_val_shadow. reflexivity.
      + rewrite update_svar_val_comm.
        { apply Hneq.  }
        rewrite -> H with (S := e).
        { reflexivity. }
        { intros Contra.
          pose proof (Hfeeo := @free_svars_svar_open signature ϕ' (fresh_svar ϕ') 0).
          rewrite -> elem_of_subseteq in Hfeeo.
          specialize (Hfeeo X Contra).
          apply elem_of_union in Hfeeo.
          destruct Hfeeo as [H'|H'].
          * apply elem_of_singleton_1 in H'. symmetry in H'. contradiction.
          * contradiction.
        }
        { f_equal. rewrite update_svar_val_comm. apply Hneq. reflexivity. }
        { f_equal. rewrite update_svar_val_comm. apply Hneq. reflexivity. }
    }
  Qed.

  (* Can change updated/opened fresh variable variable *)
  Lemma Private_eval_fresh_var_open sz ϕ dbi ρ:
    size ϕ <= sz ->
    (
      forall X Y S,
        svar_is_fresh_in X ϕ ->
        svar_is_fresh_in Y ϕ ->
        eval (update_svar_val X S ρ) (ϕ^{svar: dbi ↦ X})
        = @eval M (update_svar_val Y S ρ) (ϕ^{svar: dbi ↦ Y})
    ) /\
    (
      forall x y c,
        evar_is_fresh_in x ϕ ->
        evar_is_fresh_in y ϕ ->
        @eval M (update_evar_val x c ρ) (ϕ^{evar: dbi ↦ x})
        = eval (update_evar_val y c ρ) (ϕ^{evar: dbi ↦ y})
    )
  .
  Proof.
    move: ϕ dbi ρ.
    induction sz.
    - move=> ϕ dbi ρ Hsz.
      split.
      {
        (* base case - svar *)
        move=> X Y S HfrX HfrY.
        destruct ϕ; simpl in Hsz; try lia.
        + rewrite 2!eval_free_evar_simpl. reflexivity.
        + rewrite 2!eval_free_svar_simpl.
          unfold svar_is_fresh_in in HfrX, HfrY. simpl in HfrX, HfrY.
          apply not_elem_of_singleton_1 in HfrX.
          apply not_elem_of_singleton_1 in HfrY.
          unfold update_svar_val.
          destruct ρ as [ρₑ ρₛ]. simpl.
          destruct (decide (X = x)),(decide (Y = x)); simpl; congruence.
        + rewrite 2!eval_bound_evar_simpl. reflexivity.
        + unfold svar_open. simpl. case_match.
          * rewrite 2!eval_bound_svar_simpl.
            reflexivity.
          * rewrite 2!eval_free_svar_simpl.
            rewrite 2!update_svar_val_same. reflexivity.
          * rewrite 2!eval_bound_svar_simpl.
            reflexivity.
        + rewrite 2!eval_sym_simpl.
          reflexivity.
        + rewrite 2!eval_bott_simpl.
          reflexivity.
      }
      {
        (* base case - evar *)
        move=> x y c Hfrx Hfry.
        destruct ϕ; simpl in Hsz; try lia.
        + rewrite 2!eval_free_evar_simpl.
          unfold evar_is_fresh_in in Hfrx, Hfry. simpl in Hfrx, Hfry.
          apply not_elem_of_singleton_1 in Hfrx.
          apply not_elem_of_singleton_1 in Hfry.
          apply f_equal. unfold update_evar_val.
          destruct ρ as [ρₑ ρₛ]. simpl.
          destruct (decide (x = x0)),(decide (y = x0)); simpl; congruence.
        + rewrite 2!eval_free_svar_simpl.
          reflexivity.
        + unfold evar_open. simpl. case_match.
          * rewrite 2!eval_bound_evar_simpl.
            reflexivity.
          * rewrite 2!eval_free_evar_simpl.
            rewrite 2!update_evar_val_same. reflexivity.
          * rewrite 2!eval_bound_evar_simpl.
            reflexivity.
        + rewrite 2!eval_bound_svar_simpl. reflexivity.
        + rewrite 2!eval_sym_simpl.
          reflexivity.
        + rewrite 2!eval_bott_simpl.
          reflexivity.
      }
    - move=> ϕ dbi ρ Hsz.
      split.
      {
        (* inductive case - svar *)
        move=> X Y S HfrX HfrY.
        destruct ϕ; simpl in Hsz.
        + rewrite (proj1 (IHsz _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite (proj1 (IHsz _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite (proj1 (IHsz _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite (proj1 (IHsz _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite (proj1 (IHsz _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite 2!eval_app_simpl. fold svar_open.
          rewrite (proj1 (IHsz _ _ _ _) X Y). 4: rewrite (proj1 (IHsz _ _ _ _) X Y). lia.
          eapply svar_is_fresh_in_app_l. apply HfrX.
          eapply svar_is_fresh_in_app_l. apply HfrY.
          lia.
          eapply svar_is_fresh_in_app_r. apply HfrX.
          eapply svar_is_fresh_in_app_r. apply HfrY.
          reflexivity.
        + rewrite (proj1 (IHsz _ _ _ _) X Y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite 2!eval_imp_simpl. fold svar_open.
          rewrite (proj1 (IHsz _ _ _ _) X Y). 4: rewrite (proj1 (IHsz _ _ _ _) X Y). lia.
          eapply svar_is_fresh_in_app_l. apply HfrX.
          eapply svar_is_fresh_in_app_l. apply HfrY.
          lia.
          eapply svar_is_fresh_in_app_r. apply HfrX.
          eapply svar_is_fresh_in_app_r. apply HfrY.
          reflexivity.
        + rewrite 2!eval_ex_simpl. fold svar_open. simpl.
          apply f_equal. apply functional_extensionality. intros e.
          rewrite 2!svar_open_evar_open_comm.
          fold bsvar_subst.
          simpl. rewrite 2!update_evar_val_svar_val_comm.
          rewrite (proj1 (IHsz _ _ _ _) X Y).
          { rewrite -evar_open_size. lia. }
          { apply svar_is_fresh_in_exists in HfrX.
            apply svar_is_fresh_in_exists in HfrY.
            apply svar_fresh_evar_open. apply HfrX.
          }
          { apply svar_fresh_evar_open. apply HfrY. 
          }
          rewrite -2!svar_open_evar_open_comm.
          rewrite -2!update_evar_val_svar_val_comm.
          rewrite (proj2 (IHsz _ _ _ _) _ (fresh_evar (ϕ^{svar: dbi ↦ Y}))). rewrite -svar_open_size. lia.
          rewrite fresh_evar_svar_open.
          apply evar_fresh_svar_open. apply set_evar_fresh_is_fresh.
          apply set_evar_fresh_is_fresh.
          repeat rewrite update_evar_val_svar_val_comm.
          fold bsvar_subst.
          unfold svar_open.
          reflexivity.
        + mlSimpl. simpl.
          rewrite 2!eval_mu_simpl. simpl.
          apply f_equal. apply functional_extensionality.
          intros S'.

          remember (fresh_svar (ϕ^{svar: Datatypes.S dbi ↦ X})) as X'.
          remember (fresh_svar (ϕ^{svar: Datatypes.S dbi ↦ Y})) as Y'.
          remember ((@singleton svar (@SVarSet signature) _ X)
                      ∪ ((singleton Y)
                           ∪ ((singleton X')
                                ∪ ((singleton Y')
                                     ∪ ((free_svars (ϕ^{svar: Datatypes.S dbi ↦ X}))
                                          ∪ (free_svars (ϕ^{svar: Datatypes.S dbi ↦ Y})
                                                        ∪ (free_svars ϕ))))))) as B.
          remember (svar_fresh (elements B)) as fresh3.
          assert(HB: fresh3 ∉ B).
          {
            subst. apply set_svar_fresh_is_fresh'.
          }

          remember (free_svars (ϕ^{svar: Datatypes.S dbi ↦ Y}) ∪ (free_svars ϕ)) as B0.
          remember ((free_svars (ϕ^{svar: Datatypes.S dbi ↦ X})) ∪ B0) as B1.
          remember ({[Y']} ∪ B1) as B2.
          remember ({[X']} ∪ B2) as B3.
          remember ({[Y]} ∪ B3) as B4.
          pose proof (i := not_elem_of_union fresh3 {[X]} B4).
          pose proof (i0 := not_elem_of_union fresh3 {[Y]} B3).
          pose proof (i1 := not_elem_of_union fresh3 {[X']} B2).
          pose proof (i2 := not_elem_of_union fresh3 {[Y']} B1).
          pose proof (i3 := not_elem_of_union fresh3 
                                              (free_svars (ϕ^{svar: Datatypes.S dbi ↦ X})) 
                                              B0).
          subst B0. subst B1. subst B2. subst B3. subst B4. subst B.
          
          apply i in HB. clear i. destruct HB as [Hneqfr1 HB].        
          apply not_elem_of_singleton_1 in Hneqfr1.

          apply i0 in HB. clear i0. destruct HB as [Hneqfr2 HB].
          apply not_elem_of_singleton_1 in Hneqfr2.

          apply i1 in HB. clear i1. destruct HB as [Hneqfr11 HB].
          apply not_elem_of_singleton_1 in Hneqfr11.

          apply i2 in HB. clear i2. destruct HB as [Hneqfr22 HB].
          apply not_elem_of_singleton_1 in Hneqfr22.

          apply i3 in HB. clear i3. destruct HB as [HnotinFree1 HB].
          apply not_elem_of_union in HB.
          destruct HB as [HnotinFree2 HnotinFree].
          fold bsvar_subst.

          rewrite (proj1 (IHsz _ _ _ _) X' fresh3). rewrite -svar_open_size. lia.
          rewrite HeqX'. apply set_svar_fresh_is_fresh. unfold svar_is_fresh_in. apply HnotinFree1.
          rewrite (proj1 (IHsz _ _ _ _) Y' fresh3). rewrite -svar_open_size. lia.
          rewrite HeqY'. apply set_svar_fresh_is_fresh. unfold svar_is_fresh_in. apply HnotinFree2.
          rewrite (svar_open_comm_higher 0 (Datatypes.S dbi) _ fresh3 X ϕ). lia.
          rewrite (svar_open_comm_higher 0 (Datatypes.S dbi) _ fresh3 Y ϕ). lia.
          replace (pred (Datatypes.S dbi)) with dbi by lia.
          rewrite (update_svar_val_comm fresh3 X). apply Hneqfr1.
          rewrite (update_svar_val_comm fresh3 Y). apply Hneqfr2.
          apply svar_is_fresh_in_exists in HfrX.
          apply svar_is_fresh_in_exists in HfrY.
          rewrite (proj1 (IHsz _ _ _ _) X Y). rewrite -svar_open_size. lia.
          unfold svar_is_fresh_in.
          apply svar_open_fresh_notin.
          apply HfrX. apply HnotinFree. intros Contra. symmetry in Contra. contradiction.
          apply svar_open_fresh_notin.
          apply HfrY. apply HnotinFree. intros Contra. symmetry in Contra. contradiction.
          reflexivity.
      }
      {
        (* inductive case - evar *)
        move=> x y c Hfrx Hfry.
        destruct ϕ; simpl in Hsz.
        + rewrite (proj2 (IHsz _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite (proj2 (IHsz _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite (proj2 (IHsz _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite (proj2 (IHsz _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite (proj2 (IHsz _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite 2!eval_app_simpl. fold evar_open.
          rewrite (proj2 (IHsz _ _ _ _) x y). 4: rewrite (proj2 (IHsz _ _ _ _) x y). lia.
          eapply evar_is_fresh_in_app_l. apply Hfrx.
          eapply evar_is_fresh_in_app_l. apply Hfry.
          lia.
          eapply evar_is_fresh_in_app_r. apply Hfrx.
          eapply evar_is_fresh_in_app_r. apply Hfry.
          reflexivity.
        + rewrite (proj2 (IHsz _ _ _ _) x y). 4: reflexivity. 3,2: auto. simpl. lia.
        + rewrite 2!eval_imp_simpl. fold evar_open.
          rewrite (proj2 (IHsz _ _ _ _) x y). 4: rewrite (proj2 (IHsz _ _ _ _) x y). lia.
          eapply evar_is_fresh_in_app_l. apply Hfrx.
          eapply evar_is_fresh_in_app_l. apply Hfry.
          lia.
          eapply evar_is_fresh_in_app_r. apply Hfrx.
          eapply evar_is_fresh_in_app_r. apply Hfry.
          reflexivity.
        + mlSimpl. simpl.
          rewrite 2!eval_ex_simpl. fold evar_open. simpl.
          apply f_equal. apply functional_extensionality. intros e.
          remember (fresh_evar (ϕ^{evar: Datatypes.S dbi ↦ x})) as x'.
          remember (fresh_evar (ϕ^{evar: Datatypes.S dbi ↦ y})) as y'.
          remember ((@singleton evar (@EVarSet signature) _ x)
                      ∪ ((singleton y)
                           ∪ ((singleton x')
                                ∪ ((singleton y')
                                     ∪ ((free_evars (ϕ^{evar: Datatypes.S dbi ↦ x}))
                                          ∪ (free_evars (ϕ^{evar: Datatypes.S dbi ↦ y})
                                                        ∪ (free_evars ϕ))))))) as B.
          remember (evar_fresh (elements B)) as fresh3.
          assert(HB: fresh3 ∉ B).
          {
            subst. apply set_evar_fresh_is_fresh'.
          }

          remember (free_evars (ϕ^{evar: Datatypes.S dbi ↦ y}) ∪ (free_evars ϕ)) as B0.
          remember ((free_evars (ϕ^{evar: Datatypes.S dbi ↦ x})) ∪ B0) as B1.
          remember ({[y']} ∪ B1) as B2.
          remember ({[x']} ∪ B2) as B3.
          remember ({[y]} ∪ B3) as B4.
          pose proof (i := not_elem_of_union fresh3 {[x]} B4).
          pose proof (i0 := not_elem_of_union fresh3 {[y]} B3).
          pose proof (i1 := not_elem_of_union fresh3 {[x']} B2).
          pose proof (i2 := not_elem_of_union fresh3 {[y']} B1).
          pose proof (i3 := not_elem_of_union fresh3 
                                              (free_evars (ϕ^{evar: Datatypes.S dbi ↦ x})) 
                                              B0).
          subst B0. subst B1. subst B2. subst B3. subst B4. subst B.

          apply i in HB. clear i. destruct HB as [Hneqfr1 HB].
          apply not_elem_of_singleton_1 in Hneqfr1.

          apply i0 in HB. clear i0. destruct HB as [Hneqfr2 HB].
          apply not_elem_of_singleton_1 in Hneqfr2.

          apply i1 in HB. clear i1. destruct HB as [Hneqfr11 HB].
          apply not_elem_of_singleton_1 in Hneqfr11.

          apply i2 in HB. clear i2. destruct HB as [Hneqfr22 HB].
          apply not_elem_of_singleton_1 in Hneqfr22.

          apply i3 in HB. clear i3. destruct HB as [HnotinFree1 HB].
          apply not_elem_of_union in HB.
          destruct HB as [HnotinFree2 HnotinFree].
          rewrite (proj2 (IHsz _ _ _ _) x' fresh3). rewrite -evar_open_size. lia.
          rewrite Heqx'. apply set_evar_fresh_is_fresh. unfold evar_is_fresh_in. apply HnotinFree1.
          rewrite (proj2 (IHsz _ _ _ _) y' fresh3). rewrite -evar_open_size. lia.
          rewrite Heqy'. apply set_evar_fresh_is_fresh. unfold evar_is_fresh_in. apply HnotinFree2.
          rewrite (evar_open_comm_higher 0 (Datatypes.S dbi) _ fresh3 x ϕ). lia.
          rewrite (evar_open_comm_higher 0 (Datatypes.S dbi) _ fresh3 y ϕ). lia.
          replace (pred (Datatypes.S dbi)) with dbi by lia.
          rewrite (update_evar_val_comm fresh3 x). apply Hneqfr1.
          rewrite (update_evar_val_comm fresh3 y). apply Hneqfr2.
          apply evar_is_fresh_in_exists in Hfrx.
          apply evar_is_fresh_in_exists in Hfry.
          rewrite (proj2 (IHsz _ _ _ _) x y). rewrite -evar_open_size. lia.
          unfold evar_is_fresh_in.
          apply evar_open_fresh_notin.
          apply Hfrx. apply HnotinFree. intros Contra. symmetry in Contra. contradiction.
          apply evar_open_fresh_notin.
          apply Hfry. apply HnotinFree. intros Contra. symmetry in Contra. contradiction.
          reflexivity.
        + rewrite 2!eval_mu_simpl. fold evar_open. simpl.
          apply f_equal. apply functional_extensionality.
          intros S'.
          rewrite -2!svar_open_evar_open_comm.
          fold bevar_subst.
          rewrite -2!update_evar_val_svar_val_comm.
          rewrite (proj2 (IHsz _ _ _ _) x y). rewrite -svar_open_size. lia.
          apply evar_is_fresh_in_mu in Hfrx.
          apply evar_is_fresh_in_mu in Hfry.
          apply evar_fresh_svar_open. apply Hfrx.
          apply evar_fresh_svar_open. apply Hfry.
          rewrite 2!svar_open_evar_open_comm.
          rewrite 2!update_evar_val_svar_val_comm.
          rewrite (proj1 (IHsz _ _ _ _) _ (fresh_svar (ϕ^{evar: dbi ↦ y}))).
          rewrite -evar_open_size. lia.
          apply svar_fresh_evar_open.
          rewrite fresh_svar_evar_open. apply set_svar_fresh_is_fresh.
          apply set_svar_fresh_is_fresh.
          reflexivity.
      }
  Qed.


  Lemma eval_fresh_evar_open ϕ x y c dbi ρ:
    evar_is_fresh_in x ϕ ->
    evar_is_fresh_in y ϕ ->
    @eval M (update_evar_val x c ρ) (ϕ^{evar: dbi ↦ x})
    = eval (update_evar_val y c ρ) (ϕ^{evar: dbi ↦ y}).
  Proof.
    move=> Hfrx Hfry.
    eapply (proj2 (Private_eval_fresh_var_open (size ϕ) ϕ dbi ρ _) x y c); assumption.
    Unshelve. lia.
  Qed.

  Lemma eval_fresh_svar_open ϕ X Y S dbi ρ:
    svar_is_fresh_in X ϕ ->
    svar_is_fresh_in Y ϕ ->
    @eval M (update_svar_val X S ρ) (ϕ^{svar: dbi ↦ X})
    = eval (update_svar_val Y S ρ) (ϕ^{svar: dbi ↦ Y}).
  Proof.
    move=> HfrX HfrY.
    eapply (proj1 (Private_eval_fresh_var_open (size ϕ) ϕ dbi ρ _) X Y S); assumption.
    Unshelve. lia.
  Qed.

  (* There are two ways how to plug a pattern phi2 into a pattern phi1:
   either substitute it for some variable,
   or evaluate phi2 first and then evaluate phi1 with valuation updated to the result of phi2
  *)
  Lemma Private_plugging_patterns : forall (sz : nat) (dbi : db_index) (phi1 phi2 : Pattern),
      size phi1 <= sz -> forall (ρ : Valuation) (X : svar),
        well_formed_closed phi2 -> well_formed_closed_mu_aux phi1 (S dbi) ->
        ~ elem_of X (free_svars phi1) ->
        @eval M ρ (phi1^[svar:dbi ↦ phi2])
        = eval (update_svar_val X (@eval M ρ phi2) ρ)
                                (phi1^{svar: dbi ↦ X}).
  Proof.
    induction sz; intros dbi phi1 phi2 Hsz ρ X Hwfc2 Hwfphi1 H.
    - (* sz == 0 *)
      destruct phi1; simpl in Hsz; simpl.
      + (* free_evar *)
        repeat rewrite -> eval_free_evar_simpl. auto.
      + (* free_svar *)
        unfold svar_open. simpl.
        do 2 rewrite -> eval_free_svar_simpl.
        unfold update_svar_val.
        destruct ρ as [ρₑ ρₛ]. simpl.
        destruct (decide (X = x)).
        * simpl in H. simpl. unfold not in H. exfalso. apply H.
          apply elem_of_singleton_2. auto.
        * auto.
      + (* bound_evar *)
        rewrite 2!eval_bound_evar_simpl.
        reflexivity.
      + (* bound_svar *)
        unfold svar_open. simpl.  case_match; simpl.
        * repeat rewrite -> eval_bound_svar_simpl; auto.
        * rewrite eval_free_svar_simpl. unfold update_svar_val.
          destruct ρ as [ρₑ ρₛ]. simpl.
          destruct (decide (X = X)). auto. contradiction.
        * repeat rewrite -> eval_bound_svar_simpl; auto.
      + (* sym *)
        simpl. repeat rewrite -> eval_sym_simpl; auto.
      + (* app *)
        lia.
      + (* bot *)
        simpl. repeat rewrite eval_bott_simpl; auto.
      + (* impl *)
        lia.
      + (* ex *)
        lia.
      + (* mu *)
        lia.
    - (* sz = S sz' *)
      destruct phi1; simpl.
      (* HERE we duplicate some of the effort. I do not like it. *)
      + (* free_evar *)
        repeat rewrite eval_free_evar_simpl. auto.
      + (* free_svar *)
        unfold svar_open. simpl.
        do 2 rewrite -> eval_free_svar_simpl.
        unfold update_svar_val.
        destruct ρ as [ρₑ ρₛ]. simpl.
        destruct (decide (X = x)).
        * simpl in H. simpl. unfold not in H. exfalso. apply H.
          apply elem_of_singleton_2. auto.
        * auto.
      + (* bound_evar *)
        rewrite !eval_bound_evar_simpl. reflexivity.
      + (* bound_svar *)
        unfold svar_open. simpl. case_match.
        * repeat rewrite -> eval_bound_evar_simpl; auto.
        * rewrite eval_free_svar_simpl. unfold update_svar_val.
          destruct ρ as [ρₑ ρₛ]. simpl.
          rewrite decide_eq_same. reflexivity.
        * repeat rewrite -> eval_bound_svar_simpl; auto.
      + (* sym *)
        simpl. repeat rewrite -> eval_sym_simpl; auto.
      (* HERE the duplication ends *)
      + (* app *) mlSimpl.
        simpl in H. apply not_elem_of_union in H. destruct H.
        do 2 rewrite -> eval_app_simpl.
        simpl in Hsz.
        rewrite <- (IHsz _ phi1_1), <- (IHsz _ phi1_2).
        * reflexivity.
        * lia.
        * assumption.
        * now apply andb_true_iff in Hwfphi1.
        * auto.
        * lia.
        * assumption.
        * now apply andb_true_iff in Hwfphi1.
        * auto.
      + (* Bot. Again, a duplication of the sz=0 case *)
        simpl. repeat rewrite eval_bott_simpl; auto.
      + (* imp *)
        mlSimpl.
        simpl in Hsz. simpl in H. simpl.
        apply not_elem_of_union in H. destruct H.
        do 2 rewrite -> eval_imp_simpl.
        rewrite <- IHsz, <- IHsz.
        * reflexivity.
        * lia.
        * assumption.
        * now apply andb_true_iff in Hwfphi1.
        * auto.
        * lia.
        * assumption.
        * now apply andb_true_iff in Hwfphi1.
        * auto.

      + simpl in Hsz. simpl in H. unfold svar_open in *. simpl.
        do 2 rewrite -> eval_ex_simpl. simpl.
        apply propset_fa_union_same. intros c.

        (* x = fresh_evar phi1' *)
        (* y = evar_fresh (elements (free_evars phi1') U (free_evars phi2)) *)

        remember (phi1^[svar: dbi ↦ (patt_free_svar X)]) as phi1'.
        remember (fresh_evar phi1') as Xfr2'.
        remember (evar_fresh (elements (union (free_evars phi1') (free_evars phi2)))) as Xu.
        remember (update_svar_val X (eval ρ phi2) ρ) as ρ2'.
        pose proof (Hfresh_subst := eval_fresh_evar_open phi1' Xfr2' Xu c 0 ρ2').

        rewrite -> Hfresh_subst.
        2: { subst Xfr2'. apply set_evar_fresh_is_fresh. }
        2: { pose proof (Hfr := set_evar_fresh_is_fresh').
             specialize (Hfr (union (free_evars phi1') (free_evars phi2))).
             subst Xu.
             apply not_elem_of_union in Hfr. destruct Hfr as [Hfr _]. auto.
        }

        remember (update_evar_val (fresh_evar (phi1^[svar: dbi ↦ phi2])) c ρ) as ρe1'.
        remember (update_evar_val Xu c ρ) as ρe2'.
        rewrite -> evar_open_bsvar_subst. 2: auto.
        remember (fresh_evar (phi1^[svar: dbi ↦ phi2])) as Xfr1.

        (* dbi may or may not occur in phi1 *)
        remember (bsvar_occur phi1 dbi) as Hoc.
        move: HeqHoc.
        case: Hoc => HeqHoc.
        -- (* dbi ocurs in phi1 *)
          pose proof (HXfr1Fresh := set_evar_fresh_is_fresh (phi1^[svar: dbi ↦ phi2])).
          rewrite <- HeqXfr1 in HXfr1Fresh.
          symmetry in HeqHoc.
          pose proof (Hsub := bsvar_subst_contains_subformula phi1 phi2 dbi HeqHoc).
          pose proof (HXfr1Fresh2 := evar_fresh_in_subformula _ _ _ Hsub HXfr1Fresh).

          assert (Hinterp:
                    (eval ρe1' phi2) =
                    (eval ρ phi2)
                 ).
          { subst. apply eval_free_evar_independent. auto. }

          assert (He1e1':
                    (update_svar_val X (eval ρe1' phi2) ρ) =
                    (update_svar_val X (eval ρ phi2) ρ)
                 ).
          { congruence. }
          subst ρ2'.
          rewrite <- He1e1'.
          subst phi1'.
          rewrite -> evar_open_bsvar_subst.
          2: { wf_auto2. }

          assert (HXu: (Xfr1 = Xu)).
          { subst Xfr1. subst Xu. unfold fresh_evar.
            rewrite -> free_evars_bsvar_subst_eq.
            fold (phi1^{svar: dbi ↦ X}).
            rewrite -> free_evars_svar_open. auto. auto.
          }
          rewrite -> HXu in *.
          (*
          assert (He1e2 : ρe1' = ρe2').
          { subst. auto. }
          rewrite <- He1e2. *)
          rewrite update_evar_val_svar_val_comm.
          rewrite -Heqρe1'.
          rewrite <- IHsz.
        * reflexivity.
        * rewrite <- evar_open_size. lia. 
        * auto.
        * now apply wfc_mu_aux_body_ex_imp1.
        * rewrite -> free_svars_evar_open. auto.
          -- (* dbi does not occur in phi1 *)
            pose proof (HeqHoc' := HeqHoc).
            rewrite -> bsvar_subst_not_occur.
            2: { apply wfc_mu_aux_body_ex_imp1. apply wfc_mu_lower in Hwfphi1; wf_auto2. }
            (* Now svar_open does nothing to phi1, since it does not contain dbi (see HeqHoc). *)
            symmetry in HeqHoc. simpl in Hwfphi1. apply wfc_mu_lower in Hwfphi1; auto.
            apply svar_open_not_occur with (x:=X) in Hwfphi1 as HWF.
            (* X is not free in phi1, so the fact that in svar_val2' it is updated to some 
           value is irrelevant. *)
            subst ρ2' ρe1' ρe2'.
            replace (eval (update_evar_val Xu c (update_svar_val X (eval ρ phi2) ρ)) (phi1'^{evar: 0 ↦ Xu}))
            with (eval (update_evar_val Xu c ρ) (phi1'^{evar: 0 ↦ Xu})).
            2: {
              rewrite update_evar_val_svar_val_comm.
              symmetry.
              apply eval_free_svar_independent.
              unfold svar_is_fresh_in. rewrite -> free_svars_evar_open. subst phi1'.
              fold (phi1^{svar: dbi ↦ X}).
              rewrite -> HWF. auto.
            }
            subst phi1'. unfold svar_open in HWF. rewrite -> HWF.
            rewrite -> eval_fresh_evar_open with (y := Xu).
            { reflexivity. }
            { subst Xfr1.
              symmetry in HeqHoc'.
              pose proof (Hsubst := bsvar_subst_not_occur dbi phi2 _ Hwfphi1).
              rewrite Hsubst. auto.
            }
            { pose proof (Hfr := set_evar_fresh_is_fresh').
              specialize (Hfr (union (free_evars (phi1^{svar: dbi ↦ X})) (free_evars phi2))).
              subst Xu.
              apply not_elem_of_union in Hfr. destruct Hfr as [Hfr _].
              rewrite free_evars_svar_open in Hfr.
              rewrite free_evars_svar_open. auto.
            }

      + (* Mu case *)
        mlSimpl. simpl.
        rewrite 2!eval_mu_simpl. simpl.
        apply f_equal. apply functional_extensionality. intros E.

        remember (phi1^[svar: S dbi ↦ phi2]) as phi_subst.
        remember (union (union (union (union (union (free_svars phi_subst) (singleton (fresh_svar phi1))) (free_svars phi1)) (free_svars (phi1^{svar: S dbi ↦ X}))) (singleton X)) (free_svars phi2)) as B.

        remember (svar_fresh (elements B)) as Y.
        assert (Hfreshy: Y <> fresh_svar phi1).
        { solve_fresh_svar_neq. }

        assert (Hfreshy': svar_is_fresh_in Y phi1).
        {
          subst.
          eapply svar_is_fresh_in_richer'.
          2: apply set_svar_fresh_is_fresh'.
          solve_free_svars_inclusion 5.
        }

        assert (Hfreshy'': svar_is_fresh_in Y (phi1^{svar: S dbi ↦ X})).
        {
          subst.
          eapply svar_is_fresh_in_richer'.
          2: apply set_svar_fresh_is_fresh'.
          solve_free_svars_inclusion 5.
        }

        assert (Hfreshy''': Y <> X).
        { solve_fresh_svar_neq. }

        assert (Hfreshy'''': svar_is_fresh_in Y phi2).
        {
          subst.
          eapply svar_is_fresh_in_richer'.
          2: apply set_svar_fresh_is_fresh'.
          solve_free_svars_inclusion 5.
        }

        assert (Hfreshy5: svar_is_fresh_in Y (phi1^[svar: S dbi ↦ phi2])).
        {
          subst.
          eapply svar_is_fresh_in_richer'.
          2: apply set_svar_fresh_is_fresh'.
          solve_free_svars_inclusion 7.
        }

        remember (bsvar_occur phi1 (S dbi)) as Hoc.
        destruct Hoc.
        --
          subst phi_subst.

          rewrite (eval_fresh_svar_open _ ((fresh_svar (phi1^{svar: S dbi ↦ X}))) Y).
          { apply set_svar_fresh_is_fresh. }
          { apply Hfreshy''. }

          rewrite update_svar_val_comm.
          { apply Hfreshy'''. }
          rewrite svar_open_comm_higher.
          { lia. }
          replace (pred (S dbi)) with dbi by lia.

          replace (eval ρ phi2) with (eval (update_svar_val Y E ρ) phi2).
          2: {
            apply eval_free_svar_independent.
            apply Hfreshy''''.
          }

          rewrite <- IHsz.
          4: { apply wfc_mu_aux_body_mu_imp3. lia. auto. }
          4: { apply svar_is_fresh_in_svar_open.
               apply not_eq_sym.
               apply Hfreshy'''.
               simpl in H.
               apply H.
          }
          3: { apply Hwfc2. }
          2: { rewrite -svar_open_size. simpl in Hsz. lia. }

          rewrite svar_open_bsvar_subst_higher.
          { apply Hwfc2. }
          { lia. }
          remember  (fresh_svar (phi1^[svar: S dbi ↦ phi2])) as X'.

          rewrite -svar_open_bsvar_subst_higher.
          { apply Hwfc2. }
          { lia. }
          replace dbi with (pred (S dbi)) by lia.
          rewrite <- svar_open_bsvar_subst_higher.
          2: { apply Hwfc2. }
          2: { lia. }
          replace (pred (S dbi)) with dbi by lia.
          apply eval_fresh_svar_open.
          { subst X'. apply set_svar_fresh_is_fresh. }
          { apply Hfreshy5.  }

        --
          rewrite Heqphi_subst.
          rewrite bsvar_subst_not_occur. auto.
          rewrite bsvar_subst_not_occur in Heqphi_subst. all: auto.
          1-2: apply wfc_mu_lower; auto.

          rewrite -> eval_fresh_svar_open with (X := fresh_svar phi1) (Y := Y).
          2: { apply set_svar_fresh_is_fresh. }
          2: { subst.
               eapply svar_is_fresh_in_richer'.
               2: apply set_svar_fresh_is_fresh'.
               solve_free_svars_inclusion 5.
          }

          simpl in Hsz.

          subst phi_subst.

          rewrite -> svar_open_not_occur with (x := X)(n := S dbi).
          2: { apply wfc_mu_lower; auto. }

          destruct (decide (X = (fresh_svar phi1))).
          ++ subst X. rewrite update_svar_val_shadow.
             apply eval_fresh_svar_open.
             { apply Hfreshy'. }
             apply set_svar_fresh_is_fresh.
          ++ rewrite update_svar_val_comm.
             { apply not_eq_sym. apply n. }
             rewrite -> eval_free_svar_independent with (X:=X).
             2: { apply svar_is_fresh_in_svar_open. apply n.
                  simpl in H. apply H.
             }
             apply eval_fresh_svar_open.
             { apply Hfreshy'. }
             apply set_svar_fresh_is_fresh.
  Qed.

  Lemma set_substitution_lemma : forall (dbi : db_index) (phi1 phi2 : Pattern),
      forall (ρ : Valuation) (X : svar),
        well_formed_closed phi2 -> well_formed_closed_mu_aux phi1 (S dbi) ->
        ~ elem_of X (free_svars phi1) ->
        @eval M ρ (phi1^[svar: dbi ↦ phi2])
        = eval (update_svar_val X (@eval M ρ phi2) ρ) (phi1^{svar: dbi ↦ X}).
  Proof.
    intros.
    apply Private_plugging_patterns with (sz := size phi1).
    lia. all: auto.
  Qed.

  Lemma Private_plugging_patterns_bevar_subst : forall (sz : nat) (dbi : db_index) 
    (phi : Pattern) (y : evar),
      size phi <= sz -> forall (ρ : Valuation) (x : evar),
        evar_is_fresh_in x phi -> well_formed_closed_ex_aux phi (S dbi) ->
        @eval M ρ (phi^[evar: dbi ↦ patt_free_evar y])
        = eval (update_evar_val x (evar_valuation ρ y) ρ) (phi^{evar: dbi ↦ x}).
  Proof.
    induction sz; intros dbi phi y Hsz ρ x H Hwf.
    - (* sz == 0 *)
      destruct phi; simpl in Hsz; simpl.
      + (* free_evar *)
        unfold evar_is_fresh_in in H.
        cbn.
        repeat rewrite -> eval_free_evar_simpl.
        unfold update_evar_val.
        destruct ρ as [ρₑ ρₛ]. simpl.
        destruct (decide (x = x0)).
        * simpl. unfold not in H. exfalso. apply H.
          apply elem_of_singleton_2. auto.
        * auto.
      + (* free_svar *)
        cbn.
        auto.
      + (* bound_evar *)
        cbn.
        case_match; subst.
        * auto.
        * do 2 rewrite eval_free_evar_simpl.
          destruct ρ as [ρₑ ρₛ]. simpl.
          unfold update_evar_val.
          case_match; auto. contradiction.
        * auto.
      + (* bound_svar *)
        rewrite 2!eval_bound_svar_simpl; auto.
      + (* sym *)
        simpl. repeat rewrite -> eval_sym_simpl; auto.
      + (* app *)
        lia.
      + (* bot *)
        simpl. repeat rewrite eval_bott_simpl; auto.
      + (* impl *)
        lia.
      + (* ex *)
        lia.
      + (* mu *)
        lia.
    - (* sz = S sz' *)
      destruct phi; simpl.
      (* HERE we duplicate some of the effort. I do not like it. *)
      + (* free_evar *)
        unfold evar_is_fresh_in in H. cbn.
        do 2 rewrite -> eval_free_evar_simpl.
        unfold update_evar_val.
        destruct ρ as [ρₑ ρₛ]. simpl.
        destruct (decide (x = x0)).
        * simpl. unfold not in H. exfalso. apply H.
          apply elem_of_singleton_2. auto.
        * auto.
      + (* free_svar *)
        cbn.
        auto.
      + (* bound_evar *)
        cbn.
        case_match.
        * auto.
        * repeat rewrite eval_free_evar_simpl. unfold update_evar_val.
          destruct ρ as [ρₑ ρₛ]. simpl.
          destruct (decide (x = x)). auto. contradiction.
        * auto.
      + (* bound_svar *)
        rewrite 2!eval_bound_svar_simpl; auto.
      + (* sym *)
        simpl. repeat rewrite -> eval_sym_simpl; auto.
      (* HERE the duplication ends *)
      + (* app *)
        mlSimpl.
        unfold evar_is_fresh_in in H. simpl in H. apply not_elem_of_union in H. destruct H.
        repeat rewrite -> eval_app_simpl.
        simpl in Hsz.
        repeat rewrite <- IHsz.
        * reflexivity.
        * lia.
        * assumption.
        * now apply andb_true_iff in Hwf.
        * lia.
        * auto.
        * now apply andb_true_iff in Hwf.
      + (* Bot. Again, a duplication of the sz=0 case *)
        simpl. repeat rewrite eval_bott_simpl; auto.
      + (* imp *)
        mlSimpl.
        simpl in Hsz.
        unfold evar_is_fresh_in in H. simpl in H. apply not_elem_of_union in H. destruct H.
        repeat rewrite -> eval_imp_simpl.
        repeat rewrite <- IHsz.
        * reflexivity.
        * lia.
        * assumption.
        * now apply andb_true_iff in Hwf.
        * lia.
        * auto.
        * now apply andb_true_iff in Hwf.

      + (* ex *)
        mlSimpl. simpl.
        simpl in Hsz.
        unfold evar_is_fresh_in in H. simpl in H.
        repeat rewrite -> eval_ex_simpl. simpl.
        apply propset_fa_union_same. intros c.
        remember (fresh_evar (phi^[evar: S dbi ↦ patt_free_evar y])) as x'.
        (* rewrite evar_open_bevar_subst_higher.
        { auto. }
        { lia. } *)

        remember (phi^{evar: S dbi ↦ x}) as phi'.
        remember (fresh_evar phi') as Xfr'.
        remember (evar_fresh (elements (union (free_evars phi') (singleton x')))) as Xu.

        (* The same destruct as in the mu case of the set substitution lemma *)
        (* destruct (bevar_occur phi (S dbi)) eqn:Hbevar. *)
        --
          rewrite evar_open_bevar_subst_higher.
          { auto. }
          { lia. }
          remember (union (union (union (union
                                           (union (free_evars phi) (free_evars phi'))
                                           (free_evars (phi^[evar: S dbi ↦ patt_free_evar y])))
                                        (singleton Xfr'))
                                 (singleton x))
                          (singleton y))  as B.

          remember (evar_fresh (elements B)) as yB.

          assert (HyBx: yB <> x).
          { solve_fresh_neq. }

          assert (HyBXfr': yB <> Xfr').
          { solve_fresh_neq. }

          assert (HyBy: yB <> y).
          { solve_fresh_neq. }

          assert (HyBfphi: evar_is_fresh_in yB phi).
          {
            subst.
            eapply evar_is_fresh_in_richer'.
            2: apply set_evar_fresh_is_fresh'.
            rewrite <- 4!union_subseteq_l.
            apply union_subseteq_l.
          }

          assert (HyBfphi': evar_is_fresh_in yB phi').
          {
            subst.
            eapply evar_is_fresh_in_richer'.
            2: apply set_evar_fresh_is_fresh'.
            rewrite <- 4!union_subseteq_l.
            apply union_subseteq_r.
          }

          assert (HyBfbevar_open: evar_is_fresh_in yB (phi^[evar: S dbi ↦ patt_free_evar y])).
          { 
            subst.
            eapply evar_is_fresh_in_richer'.
            2: apply set_evar_fresh_is_fresh'.
            rewrite <- 3!union_subseteq_l.
            apply union_subseteq_r.
          }

          rewrite -> eval_fresh_evar_open with (x := Xfr') (y := yB).
          3: { apply HyBfphi'. }
          2: { subst. apply set_evar_fresh_is_fresh. }
          
          rewrite update_evar_val_comm.
          { apply HyBx. }
          subst phi'.
          rewrite evar_open_comm_higher.
          { lia. }

          remember (update_evar_val yB c ρ) as ρ'.
          remember (phi^{evar: 0 ↦ yB}^{evar: S dbi ↦ x}) as phi'.

          subst phi'.

          assert (Hevar_val: evar_valuation ρ y = evar_valuation ρ' y).
          { subst ρ'. rewrite update_evar_val_neq. apply HyBy. reflexivity. }
          rewrite Hevar_val.

          rewrite <- IHsz.
          subst ρ'.
          rewrite <- evar_open_bevar_subst_higher.
          rewrite <- evar_open_bevar_subst_higher.
          rewrite -> eval_fresh_evar_open with (y := yB).
          reflexivity.

          { rewrite Heqx'. apply set_evar_fresh_is_fresh. }
          { apply HyBfbevar_open. }
          { auto. }
          { lia. }
          { auto. }
          { lia. }
          { rewrite <- evar_open_size. lia. }
          { apply evar_is_fresh_in_evar_open. apply not_eq_sym. apply HyBx. apply H. }
          { replace (pred (S dbi)) with dbi by lia. apply wfc_mu_aux_body_ex_imp3; auto. lia. }
      + mlSimpl. simpl.
        rewrite 2!eval_mu_simpl. simpl.
        apply f_equal. apply functional_extensionality. intros x0.
        (* fold (evar_open dbi y phi). *)
        remember (phi^{evar: dbi ↦ x}) as phi'.
        remember (fresh_svar phi') as Xfr'.
        remember (svar_fresh (elements (free_svars phi'))) as Xu.
        remember (update_evar_val x (evar_valuation ρ y) ρ) as ρ'.
        pose proof (Hfresh_subst := eval_fresh_svar_open phi' Xfr' Xu x0 0 ρ').
        rewrite -> Hfresh_subst.
        2: { subst Xfr'. apply set_svar_fresh_is_fresh. }
        2: { subst Xu. apply set_svar_fresh_is_fresh'. }

        remember (update_svar_val (fresh_svar (phi^[evar: dbi ↦ patt_free_evar y])) x0 ρ) as ρs1'.
        remember (update_svar_val Xu x0 ρ) as ρs2'.
        rewrite -> svar_open_bevar_subst. 2: wf_auto2.
        remember (fresh_svar (phi^[evar: dbi ↦ patt_free_evar y])) as Xfr1.

        (* dbi may or may not occur in phi1 *)
        remember (bevar_occur phi dbi) as Hoc.
        move: HeqHoc.
        case: Hoc => HeqHoc.
        -- (* dbi ocurs in phi1 *)
          pose proof (HXfr1Fresh := set_svar_fresh_is_fresh (phi^[evar: dbi ↦ patt_free_evar y])).
          rewrite <- HeqXfr1 in HXfr1Fresh.
          symmetry in HeqHoc.
          pose proof (Hsub := bevar_subst_contains_subformula phi (patt_free_evar y) dbi HeqHoc).
          pose proof (HXfr1Fresh2 := svar_fresh_in_subformula _ _ _ Hsub HXfr1Fresh).

          assert (HXu: (Xfr1 = Xu)).
          { subst Xfr1. subst Xu. subst phi'. unfold fresh_svar.
            rewrite -> free_svars_bevar_subst_eq.
            rewrite -> free_svars_evar_open.
            assert (Hsvev: free_svars (patt_free_evar y) = ∅) by auto.
            rewrite Hsvev.
            rewrite union_empty_r_L.
            reflexivity.
            assumption.
          }

          rewrite -> HXu in *.
          replace (ρs1') with (ρs2').
          2: { subst. reflexivity. }
          subst ρs2' ρ'.
          assert (Hs1s1': update_svar_val Xu x0 ρs1' = update_svar_val Xu x0 ρ).
          { subst. rewrite update_svar_val_shadow. reflexivity. }

          subst phi'.
          rewrite <- svar_open_evar_open_comm.
          rewrite -update_evar_val_svar_val_comm. subst Xfr1.
          subst ρs1'.
          replace (evar_valuation ρ y) with (evar_valuation (update_svar_val Xu x0 ρ) y).
          2: {
            destruct ρ as [ρₑ ρₛ]. simpl. reflexivity.
          }

          rewrite <- IHsz.
        * reflexivity.
        * rewrite <- svar_open_size. simpl in Hsz. lia.
        * apply evar_fresh_svar_open. apply evar_is_fresh_in_mu. apply H.
        * apply wfc_ex_aux_body_mu_imp1. eapply well_formed_closed_ex_aux_ind.
          2: exact Hwf. auto.

          -- (* dbi does not occur in phi1 *)
            pose proof (HeqHoc' := HeqHoc).
            rewrite -> bevar_subst_not_occur.
            2: { apply wfc_ex_aux_body_mu_imp1.
              apply wfc_ex_lower; wf_auto2.
            }
            (* Now svar_open does nothing to phi1, since it does not contain dbi (see HeqHoc). *)
            (* symmetry in HeqHoc. apply evar_open_not_occur with (x1:=x) in HeqHoc. *)
            (* X is not free in phi1, so the fact that in evar_val' it is updated to some 
           value is irrelevant. *)

            subst ρs1' ρs2' ρ'.
            replace (eval (update_svar_val Xu x0 (update_evar_val x (evar_valuation ρ y) ρ)) (phi'^{svar: 0 ↦ Xu}))
            with (eval (update_svar_val Xu x0 ρ) (phi'^{svar: 0 ↦ Xu})).
            2: {
              rewrite -update_evar_val_svar_val_comm.
              symmetry.
              apply eval_free_evar_independent.
              unfold evar_is_fresh_in.
              rewrite -> free_evars_svar_open. subst phi'.
              rewrite evar_open_not_occur; auto.
              simpl in Hwf. apply wfc_ex_lower; auto.
            }
            subst phi'. rewrite evar_open_not_occur; auto.
            { apply wfc_ex_lower; auto. }
            rewrite -> eval_fresh_svar_open with (Y := Xu). reflexivity.
            { subst Xfr1.
              simpl in Hwf. symmetry in HeqHoc'.
              apply wfc_ex_lower in Hwf; auto.
              pose proof (Hsubst := bevar_subst_not_occur _ (patt_free_evar y) _ Hwf).
              rewrite Hsubst; auto.
            }
            { pose proof (Hfr := set_svar_fresh_is_fresh').
              specialize (Hfr (free_svars (phi^{evar: dbi ↦ x}))).
              subst Xu.
              rewrite free_svars_evar_open in Hfr.
              rewrite free_svars_evar_open. auto.
            }
  Qed.

  Lemma element_substitution_lemma
        (phi : Pattern) (x y : evar) (ρ : Valuation) (dbi : db_index) :
    evar_is_fresh_in x phi -> well_formed_closed_ex_aux phi (S dbi) ->
    eval ρ (phi^[evar: dbi ↦ patt_free_evar y])
    = @eval M (update_evar_val x (evar_valuation ρ y) ρ) (phi^{evar: dbi ↦ x}).
  Proof.
    intros.
    apply Private_plugging_patterns_bevar_subst with (sz := size phi);auto.
  Qed.

  (* eval unchanged within subformula over fresh element variable *)
  Lemma eval_fresh_evar_subterm ϕ₁ ϕ₂ c dbi ρ :
    is_subformula_of_ind ϕ₁ ϕ₂ ->
    @eval M (update_evar_val (fresh_evar ϕ₂) c ρ) (ϕ₁^{evar: dbi ↦ (fresh_evar ϕ₂)})
    = eval (update_evar_val (fresh_evar ϕ₁) c ρ) (ϕ₁^{evar: dbi ↦ (fresh_evar ϕ₁)}).
  Proof.
    intros Hsub.
    apply eval_fresh_evar_open; auto.
    eapply evar_fresh_in_subformula. apply Hsub.
    apply set_evar_fresh_is_fresh.
  Qed.

  (* model predicate of evar_open is maintained with change of variables *)
  Lemma M_predicate_evar_open_fresh_evar_1 x₁ x₂ ϕ :
    evar_is_fresh_in x₁ ϕ ->
    evar_is_fresh_in x₂ ϕ ->
    M_predicate M (ϕ^{evar: 0 ↦ x₁}) ->
    M_predicate M (ϕ^{evar: 0 ↦ x₂}).
  Proof.
    intros Hfr1 Hfr2.
    unfold evar_is_fresh_in in *.
    unfold M_predicate.
    intros H ρ.
    rewrite -(update_evar_val_same_2 x₂ ρ).
    rewrite (eval_fresh_evar_open _ x₂ x₁); auto.
  Qed.

  Lemma M_predicate_evar_open_fresh_evar_2 x ϕ :
    evar_is_fresh_in x ϕ ->
    M_predicate M (ϕ^{evar: 0 ↦ (fresh_evar ϕ)}) ->
    M_predicate M (ϕ^{evar: 0 ↦ x}).
  Proof.
    intros Hfr H.
    apply M_predicate_evar_open_fresh_evar_1 with (x₁ := fresh_evar ϕ); auto.
  Qed.

  (* Similar to plugging_patterns: using free svar substitution instead of 
     bound svar substitution.
     TODO: we may be able to gneeralize this lemma to non-closed psi,
           if we deal with nest_mu properly
   *)
  Lemma Private_free_svar_subst_update_exchange :
    ∀ sz phi psi X ρ,
      le (Pattern.size phi) sz → well_formed psi → well_formed_closed phi → 
      eval ρ (phi^[[svar: X ↦ psi]]) =
      eval (@update_svar_val M X (eval ρ psi) ρ) phi.
  Proof.
    unfold free_svar_subst.
    induction sz; destruct phi; intros psi X ρ Hsz Hwf Hwfc ; simpl in *; try inversion Hsz; auto.
    - rewrite -> eval_free_svar_simpl. unfold update_svar_val.
      simpl.
      destruct (decide (X = x)); simpl.
      + reflexivity.
      + rewrite -> eval_free_svar_simpl. reflexivity.
    -  rewrite -> eval_free_svar_simpl. unfold update_svar_val.
      destruct ρ as [ρₑ ρₛ]. simpl.
      destruct (decide (X = x)); simpl.
      + reflexivity.
      + rewrite -> eval_free_svar_simpl. reflexivity.
    - repeat rewrite -> eval_app_simpl.
      erewrite -> IHsz. erewrite -> IHsz. reflexivity. lia. assumption.
      + apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
        apply andb_true_iff in Hwfc1 as [Hwfc11 Hwfc12].
        apply andb_true_iff in Hwfc2 as [Hwfc21 Hwfc22].
        apply andb_true_iff. split; auto.
      + lia.
      + auto.
      + apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
        apply andb_true_iff in Hwfc1 as [Hwfc11 Hwfc12].
        apply andb_true_iff in Hwfc2 as [Hwfc21 Hwfc22].
        apply andb_true_iff. split; auto.
    - repeat rewrite -> eval_app_simpl.
      erewrite -> IHsz. erewrite -> IHsz. reflexivity. lia. assumption.
       + apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
        apply andb_true_iff in Hwfc1 as [Hwfc11 Hwfc12].
        apply andb_true_iff in Hwfc2 as [Hwfc21 Hwfc22].
        apply andb_true_iff. split; auto.
      + lia.
      + auto.
      + apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
        apply andb_true_iff in Hwfc1 as [Hwfc11 Hwfc12].
        apply andb_true_iff in Hwfc2 as [Hwfc21 Hwfc22].
        apply andb_true_iff. split; auto.
    - repeat rewrite -> eval_imp_simpl.
      erewrite -> IHsz. erewrite -> IHsz. reflexivity. lia. assumption.
       + apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
        apply andb_true_iff in Hwfc1 as [Hwfc11 Hwfc12].
        apply andb_true_iff in Hwfc2 as [Hwfc21 Hwfc22].
        apply andb_true_iff. split; auto.
      + lia.
      + auto.
      + apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
        apply andb_true_iff in Hwfc1 as [Hwfc11 Hwfc12].
        apply andb_true_iff in Hwfc2 as [Hwfc21 Hwfc22].
        apply andb_true_iff. split; auto.
    - repeat rewrite -> eval_imp_simpl.
      erewrite -> IHsz. erewrite -> IHsz. reflexivity. lia. assumption.
       + apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
        apply andb_true_iff in Hwfc1 as [Hwfc11 Hwfc12].
        apply andb_true_iff in Hwfc2 as [Hwfc21 Hwfc22].
        apply andb_true_iff. split; auto.
      + lia.
      + auto.
      + apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
        apply andb_true_iff in Hwfc1 as [Hwfc11 Hwfc12].
        apply andb_true_iff in Hwfc2 as [Hwfc21 Hwfc22].
        apply andb_true_iff. split; auto.
    - repeat rewrite -> eval_ex_simpl. simpl.
      apply propset_fa_union_same. intros.
      rewrite -> set_eq_subseteq.
      repeat rewrite -> elem_of_subseteq.
      split.
      + intros.
        remember ((free_evars (phi^[[svar: X ↦ psi]])) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
        remember (evar_fresh  (elements B)) as fresh.
        assert(evar_is_fresh_in (fresh_evar (phi^[[svar: X ↦ psi]])) (phi^[[svar: X ↦ psi]])).
        {
          apply set_evar_fresh_is_fresh.
        }
        assert(fresh ∉ B).
        {
          subst. apply set_evar_fresh_is_fresh'.
        }
        subst fresh. subst B. apply not_elem_of_union in H2. destruct H2.
        apply not_elem_of_union in H2. destruct H2.
        remember ((free_evars (phi^[[svar: X ↦ psi]])) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
        remember (evar_fresh (elements B)) as fresh.
        assert(evar_is_fresh_in fresh (phi^[[svar: X ↦ psi]])).
        {
          unfold evar_is_fresh_in. assumption.
        }
        erewrite eval_fresh_evar_open in H.
        3: { eassumption. }
        2: { assumption. }

        assert(evar_is_fresh_in fresh phi).
        {
          unfold evar_is_fresh_in. assumption.
        }
        assert(evar_is_fresh_in (fresh_evar phi) phi).
        {
          apply set_evar_fresh_is_fresh.
        }

        epose (eval_fresh_evar_open _ _ _ c 0 (update_svar_val X (eval ρ psi) ρ) _ _) as HFresh.
        rewrite -> HFresh.
        clear HFresh.
        fold free_svar_subst in *.
        epose proof (IHsz (phi^{evar: 0 ↦ fresh}) 
                    psi X
                    (update_evar_val fresh c ρ) _ _ ) as H8.
        feed specialize H8.
        {
          wf_auto2.
        }
        pose proof (eval_free_evar_independent ρ fresh c psi) as H9.
        rewrite -> H9 in H8. clear H9.
        unfold free_svar_subst in *.
        rewrite -> (@evar_open_free_svar_subst_comm) in H.
        unfold free_svar_subst in *.
        rewrite -> H8 in H.
        all: auto.
        * exact H.
        * wf_auto2.
      + intros.
        remember ((free_evars (phi^[[svar: X ↦ psi]])) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
        remember (evar_fresh (elements B)) as fresh.
        assert(evar_is_fresh_in (fresh_evar (phi^[[svar: X ↦ psi]])) (phi^[[svar: X ↦ psi]])).
        {
          apply set_evar_fresh_is_fresh.
        }
        assert(fresh ∉ B).
        {
          subst. apply set_evar_fresh_is_fresh'.
        }
        subst fresh. subst B. apply not_elem_of_union in H2. destruct H2.
        apply not_elem_of_union in H2. destruct H2.
        remember ((free_evars (phi^[[svar: X ↦ psi]])) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
        remember (evar_fresh (elements B)) as fresh.
        assert(evar_is_fresh_in fresh (phi^[[svar: X ↦ psi]])).
        {
          unfold evar_is_fresh_in. assumption.
        }
        erewrite -> eval_fresh_evar_open.
        3: { eassumption. }
        2: { assumption. }
        assert(evar_is_fresh_in fresh phi).
        {
          unfold evar_is_fresh_in. assumption.
        }
        assert(evar_is_fresh_in (fresh_evar phi) phi).
        {
          apply set_evar_fresh_is_fresh.
        }
        epose (eval_fresh_evar_open _ _ _ c 0 (update_svar_val X (eval ρ psi) ρ) _ _) as HFresh.
        rewrite -> HFresh in H.
        clear HFresh.
        epose (IHsz (phi^{evar: 0 ↦ fresh}) 
                    psi X
                    (update_evar_val fresh c ρ) _ _ ).
        pose (eval_free_evar_independent ρ fresh c psi).
        rewrite -> e0 in e. clear e0. fold free_svar_subst.

        rewrite -> (evar_open_free_svar_subst_comm).
        unfold free_svar_subst.
        rewrite -> e.
        all: auto.
        * exact H.
        * apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
          apply andb_true_iff. split.
          -- now apply wfc_mu_aux_body_ex_imp1.
          -- now apply wfc_ex_aux_body_ex_imp1.
        * apply andb_true_iff in Hwf as [_ Hwf]. apply andb_true_iff in Hwf as [_ Hwf]. apply Hwf.
    - repeat rewrite -> eval_ex_simpl. simpl.
      apply propset_fa_union_same. intros.
      rewrite -> set_eq_subseteq.
      repeat rewrite -> elem_of_subseteq.
      split.
      + intros.
        remember ((free_evars (phi^[[svar: X ↦ psi]])) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
        remember (evar_fresh (elements B)) as fresh.
        assert(evar_is_fresh_in (fresh_evar (phi^[[svar: X ↦ psi]])) (phi^[[svar: X ↦ psi]])).
        {
          apply set_evar_fresh_is_fresh.
        }
        assert(fresh ∉ B).
        {
          subst. apply set_evar_fresh_is_fresh'.
        }
        subst fresh. subst B. apply not_elem_of_union in H3. destruct H3.
        apply not_elem_of_union in H3. destruct H3.
        remember ((free_evars (phi^[[svar: X ↦ psi]])) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
        remember (evar_fresh (elements B)) as fresh.
        assert(evar_is_fresh_in fresh (phi^[[svar: X ↦ psi]])).
        {
          unfold evar_is_fresh_in. assumption.
        }

        epose proof (eval_fresh_evar_open _ _ _ c 0 ρ
                                                    H2 H3) as HFresh.
        unfold free_svar_subst in HFresh.
        rewrite -> HFresh in H1.
        clear HFresh.
        assert(evar_is_fresh_in fresh phi).
        {
          unfold evar_is_fresh_in. assumption.
        }
        assert(evar_is_fresh_in (fresh_evar phi) phi).
        {
          apply set_evar_fresh_is_fresh.
        }
        epose (eval_fresh_evar_open _ _ _ c 0 (update_svar_val X (eval ρ psi) ρ) _ _) as HFresh.
        rewrite -> HFresh.
        clear HFresh.
        epose (IHsz (phi^{evar: 0 ↦ fresh})
                    psi X
                    (update_evar_val fresh c ρ) _ _ ).
        pose (eval_free_evar_independent ρ fresh c psi).
        rewrite -> e0 in e. clear e0. fold free_svar_subst in H1.

        rewrite -> (evar_open_free_svar_subst_comm) in H1.
        unfold free_svar_subst in H1.
        rewrite -> e in H1.
        all: auto.
        * exact H1.
        * apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
          apply andb_true_iff. split.
          -- now apply wfc_mu_aux_body_ex_imp1.
          -- now apply wfc_ex_aux_body_ex_imp1.
        * apply andb_true_iff in Hwf as [_ Hwf]. apply andb_true_iff in Hwf as [_ Hwf]. apply Hwf.
      + intros.
        remember ((free_evars (phi^[[svar: X ↦ psi]])) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
        remember (evar_fresh (elements B)) as fresh.
        assert(evar_is_fresh_in (fresh_evar (phi^[[svar: X ↦ psi]])) (phi^[[svar: X ↦ psi]])).
        {
          apply set_evar_fresh_is_fresh.
        }
        assert(fresh ∉ B).
        {
          subst. apply set_evar_fresh_is_fresh'.
        }
        subst fresh. subst B. apply not_elem_of_union in H3. destruct H3.
        apply not_elem_of_union in H3. destruct H3.
        remember ((free_evars (phi^[[svar: X ↦ psi]])) ∪ (free_evars phi) ∪ (free_evars psi)) as B.
        remember (evar_fresh (elements B)) as fresh.
        assert(evar_is_fresh_in fresh (phi^[[svar: X ↦ psi]])).
        {
          unfold evar_is_fresh_in. assumption.
        }
        epose (eval_fresh_evar_open _ _ _ c 0 ρ
                                              H2 H3) as HFresh.
        fold free_svar_subst.
        rewrite -> HFresh.
        clear HFresh.
        assert(evar_is_fresh_in fresh phi).
        {
          unfold evar_is_fresh_in. assumption.
        }
        assert(evar_is_fresh_in (fresh_evar phi) phi).
        {
          apply set_evar_fresh_is_fresh.
        }
        epose proof (eval_fresh_evar_open _ _ _ c 0 (update_svar_val X (eval ρ psi) ρ) _ _) as HFresh.
        rewrite -> HFresh in H1.
        clear HFresh.
        epose (IHsz (phi^{evar: 0 ↦ fresh}) 
                    psi X 
                    (update_evar_val fresh c ρ) _ _ ).
        pose (eval_free_evar_independent ρ fresh c psi).
        rewrite -> e0 in e. clear e0.
        rewrite -> (evar_open_free_svar_subst_comm).
        unfold free_svar_subst.
        rewrite -> e.
        all: auto.
        * exact H1.
        * apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
          apply andb_true_iff. split.
          -- now apply wfc_mu_aux_body_ex_imp1.
          -- now apply wfc_ex_aux_body_ex_imp1.
        * apply andb_true_iff in Hwf as [_ Hwf]. apply andb_true_iff in Hwf as [_ Hwf]. apply Hwf.
    - repeat rewrite -> eval_mu_simpl. simpl.
      fold free_svar_subst in *.
      assert ((λ S : propset (Domain M),
                     eval (update_svar_val (fresh_svar (phi^[[svar: X ↦ psi]])) S ρ)
                          ((phi^[[svar: X ↦ psi]])^{svar: 0 ↦ fresh_svar (phi^[[svar: X ↦ psi]])}))
              =
              (λ S : propset (Domain M),
                     eval (update_svar_val (fresh_svar phi) S (update_svar_val X (eval ρ psi) ρ))
                                            (phi^{svar: 0 ↦ fresh_svar phi}))).
      apply functional_extensionality. intros.
      + (*Create a common fresh var.*)
        remember ((free_svars phi) ∪ (free_svars psi) ∪ (free_svars (phi^[[svar: X ↦ psi]])) ∪ 
                                   (free_svars (patt_free_svar X))) as B.
        remember (svar_fresh (elements B)) as MuZ.
        remember (fresh_svar phi) as MuX.
        remember (fresh_svar (phi^[[svar: X ↦ psi]])) as MuY.
        assert(MuZ ∉ B).
        {
          subst. apply set_svar_fresh_is_fresh'.
        }
        subst B. apply not_elem_of_union in H. destruct H.
        apply not_elem_of_union in H. destruct H.
        apply not_elem_of_union in H. destruct H.
        erewrite -> (eval_fresh_svar_open _ MuX MuZ); try assumption.
        erewrite -> (eval_fresh_svar_open _ MuY MuZ); try assumption.
        erewrite -> svar_open_free_svar_subst_comm; try assumption.
        rewrite update_svar_val_comm; try assumption. 
        {
          simpl in H1. apply not_elem_of_singleton_1 in H1. assumption.
        }
        epose (IHsz (phi^{svar: 0 ↦ MuZ}) psi X 
                    (update_svar_val MuZ x ρ) _ _ _).
        rewrite e.
        erewrite (eval_free_svar_independent _ MuZ x psi).
        reflexivity.
        all: auto.
        {
          apply andb_true_iff in Hwf as [_ Hwf]. apply andb_true_iff in Hwf as [Hwf _]. apply Hwf.
        }
        {
          simpl in H1. apply not_elem_of_singleton_1 in H1. assumption.
        }
        {
          subst MuY. apply set_svar_fresh_is_fresh.
        }
        {
          subst MuX. apply set_svar_fresh_is_fresh.
        }
      + fold free_svar_subst. rewrite H. reflexivity.
        (* replace 1 with (0 + 1) by lia.
        rewrite -free_svar_subst_nest_mu_1.
        rewrite nest_mu_aux_wfc_mu.
        { unfold well_formed,well_formed_closed in Hwf. destruct_and!. assumption. }
        rewrite H. reflexivity. *)
    - repeat rewrite -> eval_mu_simpl. simpl.
      fold free_svar_subst in *.
      assert ((λ S : propset (Domain M),
                     eval (update_svar_val (fresh_svar (phi^[[svar: X ↦ psi]])) S ρ)
                          ((phi^[[svar: X ↦ psi]])^{svar: 0 ↦ fresh_svar (phi^[[svar: X ↦ psi]])}))
             =
              (λ S : propset (Domain M),
                     eval (update_svar_val (fresh_svar phi) S (update_svar_val X (eval ρ psi) ρ))
                          (phi^{svar: 0 ↦ fresh_svar phi}))).
      apply functional_extensionality. intros.
      + (*Create a common fresh var.*)
        remember ((free_svars phi) ∪ (free_svars psi) ∪ (free_svars (phi^[[svar: X ↦ psi]])) ∪ 
                                   (free_svars (patt_free_svar X))) as B.
        remember (svar_fresh (elements B)) as MuZ.
        remember (fresh_svar phi) as MuX.
        remember (fresh_svar (phi^[[svar: X ↦ psi]])) as MuY.
        assert(MuZ ∉ B).
        {
          subst. apply set_svar_fresh_is_fresh'.
        }
        subst B. apply not_elem_of_union in H1. destruct H1.
        apply not_elem_of_union in H1. destruct H1.
        apply not_elem_of_union in H1. destruct H1.

        erewrite -> (eval_fresh_svar_open _ MuX MuZ); try assumption.
        erewrite -> (eval_fresh_svar_open _ MuY MuZ); try assumption.
        erewrite -> svar_open_free_svar_subst_comm; try assumption.
        rewrite update_svar_val_comm; try assumption. 
        {
          simpl in H2. apply not_elem_of_singleton_1 in H2. assumption.
        }
        epose (IHsz (phi^{svar: 0 ↦ MuZ}) psi X 
                    (update_svar_val MuZ x ρ) _ _ ).
        rewrite e. 
        {
          apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
          apply andb_true_iff. split.
          -- now apply wfc_mu_aux_body_mu_imp1.
          -- now apply wfc_ex_aux_body_mu_imp1.
        }
        erewrite (eval_free_svar_independent _ MuZ x psi); try assumption.
        reflexivity.
        unfold well_formed,well_formed_closed in Hwf.
        destruct_and!. all: try assumption.
        {
          simpl in H2. apply not_elem_of_singleton_1 in H2. assumption.
        }
        {
          subst MuY. apply set_svar_fresh_is_fresh.
        }
        {
          subst MuX. apply set_svar_fresh_is_fresh.
        }
      + fold free_svar_subst. rewrite H1. reflexivity.
        Unshelve. 
        apply set_evar_fresh_is_fresh.
        assumption.
        {
          subst sz. erewrite <- evar_open_size. reflexivity.
        }
        assumption. apply set_evar_fresh_is_fresh. assumption.
        {
          subst sz. erewrite <- evar_open_size. reflexivity.
        }
        assumption. apply set_evar_fresh_is_fresh. assumption.
        {
          erewrite <- evar_open_size. lia.
        }
        assumption. apply set_evar_fresh_is_fresh. assumption.
        {
          erewrite <- evar_open_size. lia.
        }
        assumption.
        {
          subst sz. erewrite <- svar_open_size. reflexivity.
        }
        assumption.
        { 
          apply andb_true_iff in Hwfc as [Hwfc1 Hwfc2]. simpl in Hwfc1, Hwfc2.
          apply andb_true_iff. split.
          -- now apply wfc_mu_aux_body_mu_imp1.
          -- now apply wfc_ex_aux_body_mu_imp1.
        }
        subst sz. erewrite <- svar_open_size. lia.
        assumption.
  Qed.

  Lemma free_svar_subst_update_exchange: ∀ phi psi X ρ,
      well_formed psi → well_formed_closed phi → 
      eval ρ (phi^[[svar: X ↦ psi]]) =
      eval (@update_svar_val M X (eval ρ psi) ρ) phi.
  Proof. 
    intros. apply Private_free_svar_subst_update_exchange with (sz := size phi). 
    lia. assumption. assumption.
  Qed.

  (* rho(psi) = empty then C[rho(psi)] = empty *)
  Lemma propagate_context_empty psi ρ C :
    @eval M ρ psi = ∅ ->
    eval ρ (subst_ctx C psi) = ∅.
  Proof.
    intro Hpsi. induction C.
    * auto.
    * simpl. rewrite eval_app_simpl. rewrite IHC. apply app_ext_bot_l.
    * simpl. rewrite eval_app_simpl. rewrite IHC. apply app_ext_bot_r.
  Qed.

  (* application to a singleton *)
  Definition rel_of ρ ϕ: Domain M -> propset (Domain M) :=
    λ m₁,
    (app_ext (@eval M ρ ϕ) {[ m₁ ]}).

  Definition is_total_function f (d c : propset (Domain M)) ρ :=
    ∀ (m₁ : Domain M),
      m₁ ∈ d ->
      ∃ (m₂ : Domain M),
        m₂ ∈ c /\
        app_ext (@eval M ρ f) {[ m₁ ]}
        = {[ m₂ ]}.

  Definition total_function_is_injective f (d : propset (Domain M)) ρ :=
    ∀ (m₁ : Domain M),
      m₁ ∈ d ->
      ∀ (m₂ : Domain M),
        m₂ ∈ d ->
        (rel_of ρ f) m₁ = (rel_of ρ f) m₂ ->
        m₁ = m₂.

  Definition is_functional_pattern ϕ ρ :=
    ∃ (m : Domain M), @eval M ρ ϕ = {[ m ]}.

  Lemma functional_pattern_inj ϕ ρ m₁ m₂ :
    is_functional_pattern ϕ ρ ->
    m₁ ∈ @eval M ρ ϕ ->
    m₂ ∈ @eval M ρ ϕ ->
    m₁ = m₂.
  Proof.
    intros [m Hm] Hm₁ Hm₂.
    rewrite Hm in Hm₁. inversion Hm₁. subst. clear Hm₁.
    rewrite Hm in Hm₂. inversion Hm₂. subst. clear Hm₂.
    reflexivity.
  Qed.

  End with_model.

End semantics.


Module Notations.
  Notation "M ⊨ᴹ phi" := (satisfies_model M phi) (left associativity, at level 50) : ml_scope.
  (* FIXME this should not be called `satisfies` *)
  Notation "G ⊨ phi" := (satisfies G phi) (left associativity, at level 50) : ml_scope.
  Notation "M ⊨ᵀ Gamma" := (satisfies_theory M Gamma)
                             (left associativity, at level 50) : ml_scope.
End Notations.

(*Module Hints.*)
#[export]
 Hint Resolve M_predicate_impl : core.
#[export]
 Hint Resolve M_predicate_bott : core.
#[export]
 Hint Resolve M_predicate_exists : core.
#[export]
 Hint Extern 4 (M_predicate _ (evar_open _ _ _)) => mlSimpl : core.
#[export]
 Hint Extern 4 (T_predicate _ (evar_open _ _ _)) => mlSimpl : core.
#[export]
 Hint Extern 4 (M_predicate _ (svar_open _ _ _)) => mlSimpl : core.
#[export]
 Hint Extern 4 (T_predicate _ (svar_open _ _ _)) => mlSimpl : core.
#[export]
 Hint Resolve T_predicate_impl_M_predicate : core.
#[export]
 Hint Resolve T_predicate_impl : core.
#[export]
 Hint Resolve T_predicate_bot : core.
(*End Hints.*)

Global Instance app_ext_proper {Σ : Signature} (M : Model)
: Proper ((≡) ==> (≡) ==> (≡)) (@app_ext Σ M).
Proof.
  intros X X' HXX' Y Y' HYY'.
  unfold app_ext.
  rewrite set_equiv_subseteq.
  split.
  {
    rewrite elem_of_subseteq.
    intros x Hx.
    rewrite elem_of_PropSet in Hx.
    rewrite elem_of_PropSet.
    destruct Hx as [le [re [Hle [Hre Hx] ] ] ].
    exists le. exists re. split.
    { rewrite -HXX'. assumption. }
    split.
    { rewrite -HYY'. assumption. }
    assumption.
  }
  {
    rewrite elem_of_subseteq.
    intros x Hx.
    rewrite elem_of_PropSet in Hx.
    rewrite elem_of_PropSet.
    destruct Hx as [le [re [Hle [Hre Hx] ] ] ].
    exists le. exists re. split.
    { rewrite HXX'. assumption. }
    split.
    { rewrite HYY'. assumption. }
    assumption.
  }
Qed.