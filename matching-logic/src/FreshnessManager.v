From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base gmap sets list.

From MatchingLogic.Utils
Require Import
    extralibrary
    stdpp_ext
.

From MatchingLogic
Require Import
    Pattern
    Freshness
.


Record FreshnessManager
    {Σ : Signature}
    (fm_patterns : list Pattern)
    (fm_evars : list evar)
    (fm_svars : list svar)
    := mkFreshnessManager {

    fm_evars_nodup :
        forall (i j : nat) (x y : evar),
        fm_evars !! i = Some x ->
        fm_evars !! j = Some y ->
        i <> j ->
        x <> y ;


    fm_svars_nodup :
        forall (i j : nat) (X Y : svar),
        fm_svars !! i = Some X ->
        fm_svars !! j = Some Y ->
        i <> j ->
        X <> Y ;

    fm_evars_fresh :
        forall (i j : nat) (x : evar) (ϕ : Pattern),
        fm_evars !! i = Some x ->
        fm_patterns !! j = Some ϕ ->
        evar_is_fresh_in x ϕ ;

    fm_svars_fresh :
        forall (i j : nat) (X : svar) (ϕ : Pattern),
        fm_svars !! i = Some X ->
        fm_patterns !! j = Some ϕ ->
        svar_is_fresh_in X ϕ ;
}.


Notation "FreshMan()" := (@FreshnessManager _ _ _ _) : ml_scope.

Program Definition EmptyFreshMan {Σ : Signature} : FreshnessManager [] [] []
:= @mkFreshnessManager Σ [] [] [] _ _ _ _.
Next Obligation.
    intros Σ i j x y H1 H2 H.
    rewrite lookup_nil in H1.
    inversion H1.
Qed.
Next Obligation.
    intros Σ i j X Y H1 H2 H.
    rewrite lookup_nil in H1.
    inversion H1.
Qed.
Next Obligation.
    intros Σ i j x ϕ H1 H2.
    rewrite lookup_nil in H1.
    inversion H1.
Qed.
Next Obligation.
    intros Σ i j X ϕ H1 H2.
    rewrite lookup_nil in H1.
    inversion H1.
Qed.

Lemma FreshMan_fresh_evar
    {Σ : Signature}
    (fm_patterns : list Pattern)
    (fm_evars : list evar)
    (fm_svars : list svar)
    (FM : FreshnessManager fm_patterns fm_evars fm_svars)
    :
    { x : evar & (FreshnessManager fm_patterns (x::fm_evars) fm_svars)}
.
Proof.
    remember (free_evars <$> fm_patterns) as levs.
    remember ((@elements evar EVarSet _) <$> levs) as llevs.
    remember (mjoin llevs) as evs.
    remember (evar_fresh (fm_evars ++ evs)) as x.

    assert (He1: forall (y : evar), y ∈ evs -> x <> y).
    {
        intros y Hy HContra.
        subst y.
        subst x.
        eapply not_elem_of_larger_impl_not_elem_of in Hy.
        3: {
            apply set_evar_fresh_is_fresh''.
        }
        2: {
            clear. set_solver.
        }
        {
            exact Hy.
        }
    }

    assert (He2: forall (y : evar), y ∈ fm_evars -> x <> y).
    {
        intros y Hy HContra.
        subst y.
        subst x.
        eapply not_elem_of_larger_impl_not_elem_of in Hy.
        3: {
            apply set_evar_fresh_is_fresh''.
        }
        2: {
            clear. set_solver.
        }
        {
            exact Hy.
        }
    }

    assert (He3)

    exists x.
    constructor.
    {
        intros i j x0 y0 Hi Hj H.
        destruct i,j; cbn in *.
        {
            inversion Hi; inversion Hj; subst x0 y0.
            clear -H. contradiction.
        }
        {
            inversion Hi. subst x0.
            apply He2.
            eapply elem_of_list_lookup_2.
            apply Hj.
        }
        {
            inversion Hj. subst y0.
            apply nesym.
            apply He2.
            eapply elem_of_list_lookup_2.
            apply Hi.
        }
        {
            assert (i <> j) by lia.
            destruct FM.
            eapply fm_evars_nodup0.
            { exact Hi. }
            { exact Hj. }
            { exact H0. }
        }
    }
    {
        apply FM.
    }
    {
        intros i j x0 ϕ Hi Hj.
        destruct i; cbn in *.
        {
            inversion Hi. subst x0.
        }
    }

Qed.
    


Ltac fm_new := set EmptyFreshMan as FM.

Tactic Notation "mlFreshEvar" "as" ident(X) :=
    lazymatch goal with
    | [ FM : FreshnessManager ?ps ?evs ?svs |- _] =>
        remember (evar_fresh evs) as X
    end
.


#[local]
Example freshman_usage_1 {Σ : Signature} (ϕ : Pattern) : True.
Proof.
    fm_new.
    mlFreshEvar as x.

Abort.
