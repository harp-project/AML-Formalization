From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.
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

Set Default Proof Mode "Classic".


Record FreshnessManager
    {Σ : Signature}
    (avoided_patterns : list Pattern)
    (avoided_evars : list evar)
    (avoided_svars : list svar)
    (fm_evars : list evar)
    (fm_svars : list svar)
    := mkFreshnessManager {

    fm_avoids_evar :
        forall (i j : nat) (x y : evar),
        avoided_evars !! i = Some x ->
        fm_evars !! j = Some y ->
        x <> y ;

    fm_avoids_svar :
        forall (i j : nat) (X Y : svar),
        avoided_svars !! i = Some X ->
        fm_svars !! j = Some Y ->
        X <> Y ;


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
        avoided_patterns !! j = Some ϕ ->
        evar_is_fresh_in x ϕ ;

    fm_svars_fresh :
        forall (i j : nat) (X : svar) (ϕ : Pattern),
        fm_svars !! i = Some X ->
        avoided_patterns !! j = Some ϕ ->
        svar_is_fresh_in X ϕ ;
}.


(* For some reason this does not work *)
Notation "FreshMan()" := (@FreshnessManager _ _ _ _ _ _) : ml_scope.

Program Definition EmptyFreshMan {Σ : Signature} ps aevs asvs : FreshnessManager ps aevs asvs [] []
:= @mkFreshnessManager Σ ps aevs asvs [] [] _ _ _ _ _ _.
Next Obligation.
    intros Σ ps aevs asvs i j x y H1 H2.
    rewrite lookup_nil in H2.
    inversion H2.
Qed.
Next Obligation.
    intros Σ ps aevs asvs i j x y H1 H2.
    rewrite lookup_nil in H2.
    inversion H2.
Qed.
Next Obligation.
    intros Σ ps aevs asvs i j x y H1 H2 H.
    rewrite lookup_nil in H2.
    inversion H2.
Qed.
Next Obligation.
    intros Σ ps aevs asvs i j X Y H1 H2 H.
    rewrite lookup_nil in H2.
    inversion H2.
Qed.
Next Obligation.
    intros Σ ps aevs asvs i j x ϕ H1 H2.
    rewrite lookup_nil in H1.
    inversion H1.
Qed.
Next Obligation.
    intros Σ ps aevs asvs i j X ϕ H1 H2.
    rewrite lookup_nil in H1.
    inversion H1.
Qed.

Ltac2 _is_pattern_hyp (i, value, type) : bool :=
    lazy_match! type with
    | @Pattern _ => true
    | _ => false 
    end
.

Ltac2 _project_name (i, _, _) : ident := i.


Ltac2 _gather_patterns_from_context () : constr list :=
    let hs := (Control.hyps ())in
    let phs := List.filter _is_pattern_hyp hs in
    let names := List.map _project_name phs in
    let filtered := names in
    (List.map Control.hyp filtered)
.

Ltac2 rec _patterns_to_list (ps : constr list) : constr :=
    match ps with
    | [] => constr:(@nil (@Pattern _))
    | x::xs =>
        let r := (_patterns_to_list xs) in
        let rs := constr:($x::$r) in
        rs
    end
.


Ltac2 _fm_new () :=
    let ps := _patterns_to_list (_gather_patterns_from_context ()) in
    let fm := constr:(@EmptyFreshMan _ $ps) in
    set $fm as FM
.

Ltac _fm_new := ltac2:(_fm_new ()).


Lemma FreshMan_fresh_evar
    {Σ : Signature}
    (avoided_patterns : list Pattern)
    (aevs : list evar)
    (asvs : list svar)
    (fm_evars : list evar)
    (fm_svars : list svar)
    (FM : FreshnessManager avoided_patterns aevs asvs fm_evars fm_svars)
    :
    { x : evar & (FreshnessManager avoided_patterns aevs asvs (x::fm_evars) fm_svars)}
.
Proof.
    remember (free_evars <$> avoided_patterns) as levs.
    remember ((@elements evar EVarSet _) <$> levs) as llevs.
    remember (mjoin llevs) as evs.
    remember (evar_fresh (fm_evars ++ aevs ++ evs)) as x.

    assert (He0: forall (y : evar), y ∈ aevs -> x <> y).
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

    exists x.
    constructor.
    {
        intros i j x0 y0 Hi Hj.
        destruct j; cbn in *.
        {
            inversion Hj.
            subst y0.
            apply nesym.
            apply He0.
            rewrite elem_of_list_lookup.
            exists i.
            exact Hi.
        }
        {
            destruct FM.
            eapply fm_avoids_evar0.
            { apply Hi. }
            { apply Hj. }
        }
    }
    {
        apply FM.
    }
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
            unfold evar_is_fresh_in.
            intros HContra.
            assert (HContra': x ∈ elements (free_evars ϕ)).
            {
                rewrite elem_of_elements.
                exact HContra.
            }
            assert (Hϕinfmp: ϕ ∈ avoided_patterns).
            {
                apply elem_of_list_lookup.
                exists j. apply Hj.
            }
            clear Hj.
            subst evs.
            setoid_rewrite elem_of_list_join in He1.
            specialize (He1 x).
            apply He1.
            2: reflexivity.
            exists (elements (free_evars ϕ)).
            split.
            {
                exact HContra'.
            }
            subst llevs.
            unfold fmap.
            rewrite elem_of_list_fmap.
            eexists. split. reflexivity.
            subst levs.
            unfold fmap.
            rewrite elem_of_list_fmap.
            eexists. split. reflexivity.
            exact Hϕinfmp.
        }
        {
            eapply FM.
            { apply Hi. }
            { apply Hj. }
        }
    }
    {
        apply FM.
    }
Qed.
    

Lemma FreshMan_fresh_svar
    {Σ : Signature}
    (avoided_patterns : list Pattern)
    (fm_evars : list evar)
    (fm_svars : list svar)
    (FM : FreshnessManager avoided_patterns fm_evars fm_svars)
    :
    { X : svar & (FreshnessManager avoided_patterns fm_evars (X::fm_svars))}
.
Proof.
    remember (free_svars <$> avoided_patterns) as lsvs.
    remember ((@elements svar SVarSet _) <$> lsvs) as llsvs.
    remember (mjoin llsvs) as svs.
    remember (svar_fresh (fm_svars ++ svs)) as X.

    assert (He1: forall (Y : svar), Y ∈ svs -> X <> Y).
    {
        intros Y HY HContra.
        subst Y.
        subst X.
        eapply not_elem_of_larger_impl_not_elem_of in HY.
        3: {
            apply set_svar_fresh_is_fresh''.
        }
        2: {
            clear. set_solver.
        }
        {
            exact HY.
        }
    }

    assert (He2: forall (Y : svar), Y ∈ fm_svars -> X <> Y).
    {
        intros Y HY HContra.
        subst Y.
        subst X.
        eapply not_elem_of_larger_impl_not_elem_of in HY.
        3: {
            apply set_svar_fresh_is_fresh''.
        }
        2: {
            clear. set_solver.
        }
        {
            exact HY.
        }
    }

    exists X.
    constructor.
    {
        apply FM.
    }
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
            eapply fm_svars_nodup0.
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
            unfold evar_is_fresh_in.
            intros HContra.
            assert (HContra': X ∈ elements (free_svars ϕ)).
            {
                rewrite elem_of_elements.
                exact HContra.
            }
            assert (Hϕinfmp: ϕ ∈ avoided_patterns).
            {
                apply elem_of_list_lookup.
                exists j. apply Hj.
            }
            clear Hj.
            subst svs.
            setoid_rewrite elem_of_list_join in He1.
            specialize (He1 X).
            apply He1.
            2: reflexivity.
            exists (elements (free_svars ϕ)).
            split.
            {
                exact HContra'.
            }
            subst llsvs.
            unfold fmap.
            rewrite elem_of_list_fmap.
            eexists. split. reflexivity.
            subst lsvs.
            unfold fmap.
            rewrite elem_of_list_fmap.
            eexists. split. reflexivity.
            exact Hϕinfmp.
        }
        {
            eapply FM.
            { apply Hi. }
            { apply Hj. }
        }
    }
Qed.


Ltac _ensure_fm :=
    lazymatch goal with
    | [ FM : FreshnessManager ?ps ?evs ?svs |- _] => idtac
    | _ => _fm_new
    end
.


Tactic Notation "mlFreshEvar" "as" ident(X) :=
    _ensure_fm;
    lazymatch goal with
    | [ FM : FreshnessManager ?ps ?evs ?svs |- _] =>
        apply FreshMan_fresh_evar in FM;
        destruct FM as [X FM]
    end
.


Tactic Notation "mlFreshSvar" "as" ident(X) :=
    _ensure_fm;
    lazymatch goal with
    | [ FM : FreshnessManager ?ps ?evs ?svs |- _] =>
        apply FreshMan_fresh_svar in FM;
        destruct FM as [X FM]
    end
.

Ltac2 rec index_of (x: constr) (l : constr) : constr
:=
    lazy_match! l with
    | (?y)::(?ys) => 
        (if Constr.equal x y then constr:(0) else
            let idx := index_of x ys in
            constr:(S $idx)
        )
    | _ => Control.backtrack_tactic_failure "Not found"
    end
.

Ltac2 fm_solve () :=
    unfold evar_is_fresh_in;
    unfold svar_is_fresh_in;
    match! goal with
    | [ fm : (FreshnessManager ?ps ?evs ?svs), x : evar, y : evar |- (?x <> ?y)] =>
        let i := (index_of x evs) in
        let j := (index_of y evs) in
        let fmt := (Control.hyp fm) in
        let pf := constr:(fm_evars_nodup $ps $evs $svs $fmt $i $j $x $y) in
        apply $pf > [reflexivity|reflexivity|ltac1:(lia)]
    | [ fm : (FreshnessManager ?ps ?evs ?svs), x : svar, y : svar |- (?x <> ?y)] =>
        let i := (index_of x svs) in
        let j := (index_of y svs) in
        let fmt := (Control.hyp fm) in
        let pf := constr:(fm_svars_nodup $ps $evs $svs $fmt $i $j $x $y) in
        apply $pf > [reflexivity|reflexivity|ltac1:(lia)]
    | [ fm : (FreshnessManager ?ps ?evs ?svs), x : evar |- (?x ∉ ?phi)] =>
        let i := (index_of x evs) in
        Message.print (Message.of_constr i );
        ()
    end
.

Ltac fm_solve := ltac2:(fm_solve ()).

#[local]
Example freshman_usage_1
    {Σ : Signature}
    (ϕ₁ ϕ₂ : Pattern) : True.
Proof.
    mlFreshEvar as x.
    mlFreshEvar as y.
    mlFreshEvar as z.
    assert (x <> z).
    {
        fm_solve.
    }

    mlFreshSvar as X.
    mlFreshSvar as Y.
    mlFreshSvar as Z.
    assert (Y <> Z).
    {
        fm_solve.
    }
Abort.
