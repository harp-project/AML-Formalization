From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Relations.Relations.
Require Import Logic.IndefiniteDescription Coq.Logic.FunctionalExtensionality.

From stdpp
Require Import
    base
    decidable
    propset
    sets
.

From MatchingLogic
Require Import
    Utils.extralibrary
    Pattern
    Syntax
    Semantics
    monotonic
.

Class Surj' {A B} (R : relation B) (f : A -> B) : Type :=
    {
        surj'_inv : B -> A ;
        surj'_pf: ∀ (b : B), R (f (surj'_inv b)) b
    }.

#[export]
Instance surj_surj' {A B} (R : relation B) (f : A -> B) {_ : @Surj' A B R f} : Surj R f.
Proof.
    unfold Surj.
    intros y.
    exists (surj'_inv y).
    apply surj'_pf.
Defined.

#[export]
Instance surj'_id {A} : @Surj' A A (=) Datatypes.id.
Proof.
    exists Datatypes.id.
    intros b. reflexivity.
Defined.

#[export]
Instance compose_surj' {A B C} R (f : A → B) (g : B → C) :
  Surj' (=) f -> Surj' R g -> Surj' R (g ∘ f).
Proof.
  intros [sf Hsf] [sg Hsg].
  exists (sf ∘ sg).
  intros x. unfold compose.
  rewrite Hsf.
  apply Hsg.
Qed.

Polymorphic Cumulative
Record ModelIsomorphism {Σ : Signature} (M₁ M₂ : Model) : Type := mkModelIsomorphism
    {
        mi_f : (Domain M₁) -> (Domain M₂) ;
        mi_inj :> Inj (=) (=) mi_f ;
        mi_surj :> Surj' (=) mi_f ;
        mi_sym : ∀ (s : symbols),
            mi_f <$> (sym_interp M₁ s) ≡ sym_interp M₂ s ;
        mi_app : ∀ (x y : Domain M₁),
            mi_f <$> (@app_interp Σ M₁ x y) ≡ @app_interp Σ M₂ (mi_f x) (mi_f y) ;
    }.

Definition isom {Σ : Signature} : relation Model :=
    λ M₁ M₂, ∃ (r : ModelIsomorphism M₁ M₂), True.

Definition ModelIsomorphism_refl {Σ : Signature} (M : Model) : ModelIsomorphism M M.
Proof.
    exists Datatypes.id.
    {
        apply _.
    }
    {
        apply _.
    }
    {
        intros s.
        unfold fmap.
        with_strategy transparent [propset_fmap] unfold propset_fmap.
        unfold Datatypes.id.
        set_solver.
    }
    {
        intros x y.
        unfold fmap.
        with_strategy transparent [propset_fmap] unfold propset_fmap.
        unfold Datatypes.id.
        set_solver.
    }
Defined.

Definition ModelIsomorphism_sym {Σ : Signature} (M₁ M₂ : Model) (i : ModelIsomorphism M₁ M₂)
: ModelIsomorphism M₂ M₁.
Proof.
    destruct i. destruct mi_surj0.
    exists surj'_inv0.
    {
        intros x y H. unfold Inj in mi_inj0.
        rewrite -[x]surj'_pf0. rewrite -[y]surj'_pf0.
        f_equal. apply mi_inj0. f_equal. assumption.
    }
    {
        unfold Inj in mi_inj0.
        exists mi_f0. intros a.
        apply mi_inj0.
        rewrite surj'_pf0. reflexivity.
    }
    {
        intros x y.
        unfold fmap in *.
        with_strategy transparent [propset_fmap] unfold propset_fmap in *.
        rewrite elem_of_PropSet.
        specialize (mi_sym0 x).
        rewrite set_equiv_subseteq in mi_sym0.
        destruct mi_sym0 as [mi_sym1 mi_sym2].
        rewrite elem_of_subseteq in mi_sym1.
        rewrite elem_of_subseteq in mi_sym2.
        setoid_rewrite elem_of_PropSet in mi_sym1.
        setoid_rewrite elem_of_PropSet in mi_sym2.
        split.
        {
            intros [b [Hb1 Hb2]].
            subst.
            specialize (mi_sym2 b Hb2).
            destruct mi_sym2 as [a [Ha1 Ha2]].
            subst.
            cut (surj'_inv0 (mi_f0 a) = a).
            {
                intros Htmp. rewrite Htmp. exact Ha2.
            }
            apply mi_inj0.
            rewrite surj'_pf0.
            reflexivity.
        }
        {
            intros Hy.
            specialize (mi_sym1 (mi_f0 y)).
            feed specialize mi_sym1.
            {
                exists y.
                split;[reflexivity|].
                exact Hy.
            }
            exists (mi_f0 y).
            split.
            {
                apply mi_inj0.
                rewrite surj'_pf0.
                reflexivity.
            }
            {
                exact mi_sym1.
            }
        }
    }
    {
        intros x y.
        unfold fmap in *.
        with_strategy transparent [propset_fmap] unfold propset_fmap in *.
        specialize (mi_app0 (surj'_inv0 x) (surj'_inv0 y)).
        do 2 rewrite surj'_pf0 in mi_app0.
        rewrite set_equiv_subseteq in mi_app0.
        rewrite elem_of_subseteq in mi_app0.
        rewrite elem_of_subseteq in mi_app0.
        setoid_rewrite elem_of_PropSet in mi_app0.
        destruct mi_app0 as [mi_app1 mi_app2].
        rewrite set_equiv_subseteq.
        do 2 rewrite elem_of_subseteq.
        setoid_rewrite elem_of_PropSet.
        split.
        {
            intros a [b [Hb1 Hb2]].
            subst.
            specialize (mi_app2 b Hb2).
            destruct mi_app2 as [a [Ha1 Ha2]].
            subst.
            cut (surj'_inv0 (mi_f0 a) = a).
            {
                intros Htmp. rewrite Htmp. exact Ha2.
            }
            apply mi_inj0.
            rewrite surj'_pf0.
            reflexivity.
        }
        {
            intros a Ha.
            exists (mi_f0 a).
            split.
            {
                apply mi_inj0.
                rewrite surj'_pf0.
                reflexivity.
            }
            {
                apply mi_app1.
                exists a.
                split;[reflexivity|].
                exact Ha.
            }
        }
    }
Defined.

Program Definition ModelIsomorphism_trans {Σ : Signature} (M₁ M₂ M₃ : Model)
    (i : ModelIsomorphism M₁ M₂)
    (j : ModelIsomorphism M₂ M₃)
    : ModelIsomorphism M₁ M₃
    :=
    {|
        mi_f := (mi_f j) ∘ (mi_f i)
    |}.
Next Obligation.
    intros. destruct i,j. simpl. apply _.
Defined.
Next Obligation.
    intros. pose proof (mi_surj i). pose proof (mi_surj j). apply _.
Defined.
Next Obligation.
    intros.
    pose proof (Hi := mi_sym i s).
    pose proof (Hj := mi_sym j s).
    rewrite -Hj.
    rewrite -Hi.
    apply set_fmap_compose.
Defined.
Next Obligation.
    intros.
    pose proof (Hi := mi_app i).
    pose proof (Hj := mi_app j).
    rewrite -Hj.
    rewrite -Hi.
    apply set_fmap_compose.
Defined.

#[global]
Instance ModelIsomorphism_equiv {Σ : Signature} : Equivalence isom.
Proof.
    split.
    {
        (* reflexive *)
        unfold Reflexive.
        intros M.
        exists (ModelIsomorphism_refl M).
        exact I.
    }
    {
        (* Symmetric *)
        unfold Symmetric.
        intros M1 M2 [j _].
        exists (ModelIsomorphism_sym j).
        exact I.
    }
    {
        (* Transitive *)
        unfold Transitive.
        intros M1 M2 M3 [i _] [j _].
        exists (ModelIsomorphism_trans i j).
        exact I.
    }
Qed.

(*
#[global]
Instance ModelIsomorphism_sym_cancel
    {Σ : Signature}
    (M₁ M₂ : Model)
    (i : ModelIsomorphism M₁ M₂)
    :
    Cancel (=) (mi_f i) (mi_f (ModelIsomorphism_sym i)).
Proof.
    unfold Cancel.
    intros x.
    unfold ModelIsomorphism_sym.
    simpl.
Qed.
*)

Lemma fmap_app_ext {Σ : Signature} (M : Model) (X Y : propset (Domain M))
    (B : Type) (f : (Domain M) -> B)
    :
    f <$> app_ext X Y ≡ {[ e | ∃ le re : M, le ∈ X ∧ re ∈ Y ∧ e ∈ (f <$> (app_interp le re)) ]}.
Proof.
    unfold fmap at 1.
    with_strategy transparent [propset_fmap] unfold propset_fmap at 1.
    set_solver.
Qed.

#[local]
Hint Transparent Power : core.

Lemma update_evar_val_compose
    {Σ : Signature} (M₁ M₂ : Model) (ρₑ : @EVarVal Σ M₁) (x : evar) (m : Domain M₁)
    (f : Domain M₁ -> Domain M₂)
    :
    update_evar_val x (f m) (f ∘ ρₑ) = f ∘ (update_evar_val x m ρₑ).
Proof.
    apply functional_extensionality.
    intros y.
    unfold update_evar_val.
    simpl.
    case_match; auto.
Qed.

Theorem isomorphism_preserves_semantics
    {Σ : Signature}
    (M₁ M₂ : Model)
    (i : ModelIsomorphism M₁ M₂)
    :
    forall (ϕ : Pattern) (ρₑ : @EVarVal _ M₁) (ρₛ : @SVarVal _ M₁),
        ((mi_f i) <$> (@pattern_interpretation Σ M₁ ρₑ ρₛ ϕ))
        ≡@{propset (Domain M₂)} (@pattern_interpretation Σ M₂ ((mi_f i) ∘ ρₑ) (λ X, (mi_f i) <$> (ρₛ X)) ϕ).
Proof.
    intros ϕ.
    remember (size' ϕ) as sz.
    assert (Hsz: size' ϕ <= sz) by lia.
    clear Heqsz.
    move: ϕ Hsz.
    induction sz; intros ϕ Hsz.
    {
        destruct ϕ; simpl in Hsz; lia.
    }
    {
        destruct ϕ; intros ρₑ ρₛ.
        {
            (* patt_free_evar x *)
            do 2 rewrite pattern_interpretation_free_evar_simpl.
            simpl.
            unfold fmap.
            with_strategy transparent [propset_fmap] unfold propset_fmap.
            clear. set_solver.
        }
        {
            (* patt_free_svar X *)
            do 2 rewrite pattern_interpretation_free_svar_simpl.
            simpl.
            unfold fmap.
            with_strategy transparent [propset_fmap] unfold propset_fmap.
            clear. set_solver.
        }
        {
            (* patt_bound_evar n *)
            do 2 rewrite pattern_interpretation_bound_evar_simpl.
            simpl.
            unfold fmap.
            with_strategy transparent [propset_fmap] unfold propset_fmap.
            clear. set_solver.
        }
        {
            (* patt_bound_svar n *)
            do 2 rewrite pattern_interpretation_bound_svar_simpl.
            simpl.
            unfold fmap.
            with_strategy transparent [propset_fmap] unfold propset_fmap.
            clear. set_solver.
        }
        {
            (* patt_sym s *)
            do 2 rewrite pattern_interpretation_sym_simpl.
            apply mi_sym.
        }
        {
            (* patt_app ϕ1 ϕ2 *)
            do 2 rewrite pattern_interpretation_app_simpl.
            rewrite fmap_app_ext.
            
            simpl in Hsz.
            rewrite set_equiv_subseteq.
            do 2 rewrite elem_of_subseteq.
            split.
            {
                intros x Hx.
                rewrite elem_of_PropSet in Hx.
                destruct Hx as [le [re [Hle [Hre Hx]]]].
                rewrite mi_app in Hx.
                rewrite -IHsz.
                2: { lia. }
                rewrite -IHsz.
                2: { lia. }
                unfold app_ext.
                rewrite elem_of_PropSet.
                exists (mi_f i le).
                exists (mi_f i re).
                repeat split.
                3: { exact Hx. }
                { apply elem_of_fmap_2. assumption. }
                { apply elem_of_fmap_2. assumption. }
            }
            {
                intros x Hx.
                rewrite elem_of_PropSet in Hx.
                rewrite elem_of_PropSet.
                destruct Hx as [le [re [Hle [Hre Hx]]]].
                rewrite -IHsz in Hle.
                2: { lia. }
                rewrite -IHsz in Hre.
                2: { lia. }
                apply elem_of_fmap_1 in Hle.
                apply elem_of_fmap_1 in Hre.
                destruct Hle as [x1 [Hx1 Hle]].
                destruct Hre as [x2 [Hx2 Hre]].
                subst.
                rewrite -(mi_app i) in Hx.
                exists x1. exists x2.
                repeat split; assumption.
            }
        }
        {
            (* patt_bott *)
            do 2 rewrite pattern_interpretation_bott_simpl.
            unfold fmap.
            with_strategy transparent [propset_fmap] unfold propset_fmap.
            clear.
            set_solver.
        }
        {
            (* patt_imp ϕ1 ϕ2 *)
            do 2 rewrite pattern_interpretation_imp_simpl.
            simpl in Hsz.
            rewrite -IHsz.
            2: { lia. }
            rewrite -IHsz.
            2: { lia. }
            remember (pattern_interpretation ρₑ ρₛ ϕ1) as X1.
            remember (pattern_interpretation ρₑ ρₛ ϕ2) as X2.
            unfold fmap.
            with_strategy transparent [propset_fmap] unfold propset_fmap.
            rewrite set_equiv_subseteq.
            split.
            {
                rewrite elem_of_subseteq.
                intros x Hx.
                rewrite elem_of_PropSet in Hx.
                destruct Hx as [a [Ha Hx]].
                subst.
                destruct Hx as [Hx1|Hx2].
                {
                    left.
                    rewrite elem_of_PropSet.
                    split.
                    { clear. set_solver. }
                    intros HContra.
                    rewrite elem_of_PropSet in Hx1.
                    apply Hx1. clear Hx1.
                    rewrite elem_of_PropSet in HContra.
                    destruct HContra as [a0 [Ha0 HContra]].
                    apply (mi_inj) in Ha0. subst.
                    exact HContra.
                }
                {
                    right.
                    rewrite elem_of_PropSet.
                    exists a.
                    split;[reflexivity|assumption].
                }
            }
            {
                pose (j := ModelIsomorphism_sym i).
                rewrite elem_of_subseteq.
                intros x Hx.
                rewrite elem_of_PropSet.
                destruct Hx as [Hx|Hx].
                {
                    rewrite elem_of_PropSet in Hx.
                    destruct Hx as [_ Hx].
                    pose (mi_surj i) as i'.
                    pose (@surj'_inv _ _ (=) _ i') as d.
                    exists (d x).
                    rewrite surj'_pf.
                    split;[reflexivity|].
                    left.
                    rewrite elem_of_PropSet.
                    split;[(clear;set_solver)|].
                    rewrite elem_of_PropSet in Hx.
                    intros HContra.
                    apply Hx. clear Hx.
                    exists (d x).
                    rewrite surj'_pf.
                    split;[reflexivity|assumption].
                }
                {
                    rewrite elem_of_PropSet in Hx.
                    destruct Hx as [a [Ha Hx]].
                    subst.
                    exists a.
                    split;[reflexivity|].
                    right.
                    exact Hx.
                }
            }
        }
        {
            do 2 rewrite pattern_interpretation_ex_simpl.
            simpl.
            rewrite set_equiv_subseteq.
            split.
            {
                rewrite elem_of_subseteq.
                intros x Hx.
                with_strategy transparent [propset_fmap] unfold propset_fmap in Hx.
                rewrite elem_of_PropSet in Hx.
                destruct Hx as [a [Ha Hx]].
                subst.
                rewrite elem_of_PropSet in Hx.
                destruct Hx as [c Hc].
                under [fun e => _]functional_extensionality => e.
                {
                    replace e with (@mi_f Σ M₁ M₂ i (@surj'_inv _ _ (=) _ (mi_surj i) e)).
                    2: { apply surj'_pf. }
                    rewrite update_evar_val_compose.
                    rewrite -IHsz.
                }
            }
            rewrite IHsz.
        }
    }

Qed.