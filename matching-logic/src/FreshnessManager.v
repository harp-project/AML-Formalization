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
    Syntax
    IndexManipulation
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

(* Maybe it is better to show everything, for debugging reasons *)
(* Notation "FreshMan()" := (@FreshnessManager _ _ _ _ _ _) : ml_scope. *)

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

Ltac2 _is_evar_hyp (i, value, type) : bool :=
    lazy_match! type with
    | @evar _ => true
    | _ => false 
    end
.

Ltac2 _gather_evars_from_context () : constr list :=
    let hs := (Control.hyps ())in
    let phs := List.filter _is_evar_hyp hs in
    let names := List.map _project_name phs in
    let filtered := names in
    (List.map Control.hyp filtered)
.

Ltac2 rec _evars_to_list (ps : constr list) : constr :=
    match ps with
    | [] => constr:(@nil (@evar _))
    | x::xs =>
        let r := (_evars_to_list xs) in
        let rs := constr:($x::$r) in
        rs
    end
.


Ltac2 _is_svar_hyp (i, value, type) : bool :=
    lazy_match! type with
    | @svar _ => true
    | _ => false 
    end
.

Ltac2 _gather_svars_from_context () : constr list :=
    let hs := (Control.hyps ())in
    let phs := List.filter _is_svar_hyp hs in
    let names := List.map _project_name phs in
    let filtered := names in
    (List.map Control.hyp filtered)
.

Ltac2 rec _svars_to_list (ps : constr list) : constr :=
    match ps with
    | [] => constr:(@nil (@svar _))
    | x::xs =>
        let r := (_svars_to_list xs) in
        let rs := constr:($x::$r) in
        rs
    end
.

Ltac2 _fm_new () :=
    let ps := _patterns_to_list (_gather_patterns_from_context ()) in
    let aevs := _evars_to_list (_gather_evars_from_context ()) in
    let asvs := _svars_to_list (_gather_svars_from_context ()) in
    let fm := constr:(@EmptyFreshMan _ $ps $aevs $asvs) in
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
    (aevs : list evar)
    (asvs : list svar)
    (fm_evars : list evar)
    (fm_svars : list svar)
    (FM : FreshnessManager avoided_patterns aevs asvs fm_evars fm_svars)
    :
    { X : svar & (FreshnessManager avoided_patterns aevs asvs fm_evars (X::fm_svars))}
.
Proof.
    remember (free_svars <$> avoided_patterns) as lsvs.
    remember ((@elements svar SVarSet _) <$> lsvs) as llsvs.
    remember (mjoin llsvs) as svs.
    remember (svar_fresh (fm_svars ++ asvs ++ svs)) as X.


    assert (He0: forall (Y : svar), Y ∈ asvs -> X <> Y).
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
            eapply fm_avoids_svar0.
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
    | [ FM : FreshnessManager ?ps ?aevs ?asvs ?evs ?svs |- _] => idtac
    | _ => _fm_new
    end
.


Tactic Notation "mlFreshEvar" "as" ident(X) :=
    _ensure_fm;
    lazymatch goal with
    | [ FM : FreshnessManager ?ps ?aevs ?asvs ?evs ?svs |- _] =>
        apply FreshMan_fresh_evar in FM;
        destruct FM as [X FM]
    end
.


Tactic Notation "mlFreshSvar" "as" ident(X) :=
    _ensure_fm;
    lazymatch goal with
    | [ FM : FreshnessManager ?ps ?aevs ?asvs ?evs ?svs |- _] =>
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
    | _ => 
        Message.print (Message.of_constr x);
        Control.backtrack_tactic_failure "Not found"
    end
.
(*
Ltac2 _is_subterm_of (x : constr) (y : constr) : bool
:=
    match! y with
    | context [ ?z ] =>
        (if (Constr.equal x z) then () else Message.print (Message.of_string "failing"); fail);
        Message.print (Message.of_constr x);
        Message.print (Message.of_constr z);
        true
    | _ => false
    end
.
*)

Lemma FreshMan_export_vars_inclusion
    {Σ : Signature}
    (ap : Pattern)
    (avoided_patterns : list Pattern)
    (aevs : list evar)
    (asvs : list svar)
    (fm_evars : list evar)
    (fm_svars : list svar)
    (FM : FreshnessManager (ap::avoided_patterns) aevs asvs fm_evars fm_svars)
    :
    (fm_evars ## elements (free_evars ap)) /\
    (fm_svars ## elements (free_svars ap)) /\
    FreshnessManager avoided_patterns aevs asvs fm_evars fm_svars
.
Proof.
    split.
    {
        rewrite elem_of_disjoint.
        intros x Hx HContra.
        rewrite elem_of_list_lookup in Hx.
        destruct Hx as [i Hx].
        destruct FM.
        assert (H : evar_is_fresh_in x ap).
        {
            eapply fm_evars_fresh0 with (j := 0).
            { apply Hx. }
            cbn. reflexivity.
        }
        clear -H HContra.
        unfold evar_is_fresh_in in H.
        set_solver.
    }
    split.
    {
        rewrite elem_of_disjoint.
        intros x Hx HContra.
        rewrite elem_of_list_lookup in Hx.
        destruct Hx as [i Hx].
        destruct FM.
        assert (H : svar_is_fresh_in x ap).
        {
            eapply fm_svars_fresh0 with (j := 0).
            { apply Hx. }
            cbn. reflexivity.
        }
        clear -H HContra.
        unfold svar_is_fresh_in in H.
        set_solver.
    }
    {
        destruct FM.
        constructor.
        {
            intros.
            eapply fm_avoids_evar0; eassumption.
        }
        {
            intros.
            eapply fm_avoids_svar0; eassumption.
        }
        
        {
            intros.
            eapply fm_evars_nodup0; eassumption.
        }
        {
            intros.
            eapply fm_svars_nodup0; eassumption.
        }
        {
            intros.
            eapply fm_evars_fresh0 with (j := S j); try eassumption.
        }
        {
            intros.
            eapply fm_svars_fresh0 with (j := S j); try eassumption.
        }
    }
Qed.

Lemma FreshMan_export_evars_nodup
    {Σ : Signature}
    (x : evar)
    (avoided_patterns : list Pattern)
    (aevs : list evar)
    (asvs : list svar)
    (fm_evars : list evar)
    (fm_svars : list svar)
    (FM : FreshnessManager avoided_patterns aevs asvs (x::fm_evars) fm_svars)
    :
    x ∉ fm_evars /\
    x ∉ aevs /\
    FreshnessManager avoided_patterns aevs asvs fm_evars fm_svars
.
Proof.
  split.
  {
    pose proof (fm_evars_nodup _ _ _ _ _ FM).
    clear-H.
    intro.
    apply elem_of_list_lookup_1 in H0 as [i H0].
    by specialize (H 0 (S i) x x eq_refl H0 ltac:(lia)).
  }
  split.
  {
    pose proof (fm_avoids_evar _ _ _ _ _ FM).
    clear -H.
    intro.
    apply elem_of_list_lookup_1 in H0 as [i H0].
    by specialize (H i 0 x x H0 eq_refl).
  }
  {
    destruct FM.
    constructor.
    {
        intros.
        eapply (fm_avoids_evar0 i (S j)); eassumption.
    }
    {
        intros.
        eapply fm_avoids_svar0; eassumption.
    }
    {
        intros.
        eapply (fm_evars_nodup0 (S i) (S j)); try eassumption. lia.
    }
    {
        intros.
        eapply fm_svars_nodup0; eassumption.
    }
    {
        intros.
        eapply fm_evars_fresh0 with (j := j) (i := S i); try eassumption.
    }
    {
        intros.
        eapply fm_svars_fresh0 with (j := j); try eassumption.
    }
  }
Qed.


Lemma FreshMan_export_svars_nodup
    {Σ : Signature}
    (X : svar)
    (avoided_patterns : list Pattern)
    (aevs : list evar)
    (asvs : list svar)
    (fm_evars : list evar)
    (fm_svars : list svar)
    (FM : FreshnessManager avoided_patterns aevs asvs fm_evars (X::fm_svars))    :
    X ∉ fm_svars /\
    X ∉ asvs /\
    FreshnessManager avoided_patterns aevs asvs fm_evars fm_svars
.
Proof.
  split.
  {
    pose proof (fm_svars_nodup _ _ _ _ _ FM).
    clear-H.
    intro.
    apply elem_of_list_lookup_1 in H0 as [i H0].
    by specialize (H 0 (S i) X X eq_refl H0 ltac:(lia)).
  }
  split.
  {
    pose proof (fm_avoids_svar _ _ _ _ _ FM).
    clear -H.
    intro.
    apply elem_of_list_lookup_1 in H0 as [i H0].
    by specialize (H i 0 X X H0 eq_refl).
  }
  {
    destruct FM.
    constructor.
    {
        intros.
        eapply (fm_avoids_evar0 i j); eassumption.
    }
    {
        intros.
        eapply (fm_avoids_svar0 i (S j)); eassumption.
    }
    {
        intros.
        eapply (fm_evars_nodup0 i j); try eassumption.
    }
    {
        intros.
        eapply (fm_svars_nodup0 (S i) (S j)); try eassumption. lia.
    }
    {
        intros.
        eapply fm_evars_fresh0 with (j := j) (i := i); try eassumption.
    }
    {
        intros.
        eapply fm_svars_fresh0 with (j := j) (i := S i); try eassumption.
    }
  }
Qed.

Ltac2 rec _fm_export_everything () :=
    lazy_match! goal with
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- _]
        =>
        clear -$fm
    end;
    repeat (
    lazy_match! goal with
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- _]
        =>
        apply FreshMan_export_vars_inclusion in $fm;
        let h := Control.hyp fm in
        destruct $h as [? [? fm]]
    end
    );
    repeat (
    lazy_match! goal with
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- _]
        =>
        apply FreshMan_export_evars_nodup in $fm;
        let h := Control.hyp fm in
        destruct $h as [? [? fm]]
    end
    );
    repeat (
    lazy_match! goal with
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- _]
        =>
        apply FreshMan_export_svars_nodup in $fm;
        let h := Control.hyp fm in
        destruct $h as [? [? fm]]
    end
    );
    lazy_match! goal with
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- _]
        =>
        clear fm
    end
.


Lemma free_evars_of_list_unfold
    {Σ : Signature}
    (ϕ : Pattern)
    (ϕs : list Pattern)
    (x : evar)
    :
    x ∉ free_evars ϕ /\ x ∉ free_evars_of_list ϕs ->
    x ∉ free_evars_of_list (ϕ::ϕs)
.
Proof.
    cbn.
    intros [H1 H2] HContra.
    rewrite elem_of_union in HContra.
    destruct HContra as [HContra|HContra].
    {
        apply H1. exact HContra.
    }
    {
        unfold free_evars_of_list in H2.
        apply H2. exact HContra.
    }
Qed.

Ltac2 fm_solve () :=
    unfold evar_is_fresh_in;
    unfold svar_is_fresh_in;
    (* we cannot do lazy_match because we need to try the variant for avoided variables as well as the variant for fresh variables,
       and we do not have a way how to decide in advance. Although, maybe we could try finding the evar in the avoided variables,
       and branch on whether it succeeds or not. This is an idea for later refactoring :)*)
    match! goal with
    (* evar, x == avoided, y == fresh *)
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- (not (@eq evar ?x ?y))] =>
        let i := (index_of x aevs) in
        let j := (index_of y evs) in
        let fmt := (Control.hyp fm) in
        let pf := constr:(fm_avoids_evar $ps $aevs $asvs $evs $svs $fmt $i $j $x $y) in
        apply $pf > [reflexivity|reflexivity]
    (* evar, x == fresh, y == avoided *)
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- (not (@eq evar ?x ?y))] =>
        let i := (index_of x evs) in
        let j := (index_of y aevs) in
        let fmt := (Control.hyp fm) in
        let pf := constr:(fm_avoids_evar $ps $aevs $asvs $evs $svs $fmt $j $i $y $x) in
        apply nesym;
        apply $pf > [reflexivity|reflexivity]
    (* evar, x == fresh, y == fresh *)
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- (not (@eq evar ?x ?y))] =>
        let i := (index_of x evs) in
        let j := (index_of y evs) in
        let fmt := (Control.hyp fm) in
        let pf := constr:(fm_evars_nodup $ps $aevs $asvs $evs $svs $fmt $i $j $x $y) in
        apply $pf > [reflexivity|reflexivity|ltac1:(lia)]
    (* svar, x == avoided, y == fresh *)
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- (not (@eq svar ?x ?y))] =>
        let i := (index_of x asvs) in
        let j := (index_of y svs) in
        let fmt := (Control.hyp fm) in
        let pf := constr:(fm_avoids_svar $ps $aevs $asvs $evs $svs $fmt $i $j $x $y) in
        apply $pf > [reflexivity|reflexivity]
    (* svar, x == fresh, y == avoided *)
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- (not (@eq svar ?x ?y))] =>
        let i := (index_of x svs) in
        let j := (index_of y asvs) in
        let fmt := (Control.hyp fm) in
        let pf := constr:(fm_avoids_svar $ps $aevs $asvs $evs $svs $fmt $j $i $y $x) in
        apply nesym;
        apply $pf > [reflexivity|reflexivity]
    (* x == fresh, y == fresh *)        
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- (not (@eq svar ?x ?y))] =>
        let i := (index_of x svs) in
        let j := (index_of y svs) in
        let fmt := (Control.hyp fm) in
        let pf := constr:(fm_svars_nodup $ps $aevs $asvs $evs $svs $fmt $i $j $x $y) in
        apply $pf > [reflexivity|reflexivity|ltac1:(lia)]
    | [ fm : (FreshnessManager ?ps ?aevs ?asvs ?evs ?svs) |- _ (* (not (@elem_of _ _ _ ?x _)) *) ] =>
        (* This might not be the most scalable approach, but it works for now. *)
        _fm_export_everything ();
        cbn;
        unfold evar_open;
        unfold svar_open;
        (* Message.print (Message.of_string "trying default strategy"); *)
        (* TODO: rework this logic into solve_fresh *)
        ltac1:(pose proof (free_evars_bevar_subst);
               pose proof (free_svars_bsvar_subst);
               pose proof (free_evars_evar_open);
               pose proof free_evars_free_evar_subst;
               pose proof free_evars_nest_ex;
               subst; (solve_fresh + set_solver))
    | [ _ : _ |- _] => Message.print (Message.of_string "fm_solve() failed")
    end
.

Ltac fm_solve := ltac2:(fm_solve ()).


#[local]
Example freshman_usage_1
    {Σ : Signature}
    (x0 y0 : evar)
    (X0 Y0 : svar)
    (ϕ₁ ϕ₂ ϕq ϕw ϕe ϕr ϕt ϕy ϕu ϕi ϕo ϕp : Pattern) (* Just a bunch of patterns to test scalability*)
    : True.
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
    assert (x ∉ free_evars (patt_imp ϕ₁ ϕ₂)).
    {
        fm_solve.
    }
    assert (Y ∉ free_svars (patt_imp ϕ₁ ϕ₂)).
    {
        fm_solve.
    }
    assert (y ∉ free_evars_of_list [(patt_imp ϕ₁ ϕ₂); (patt_imp ϕ₂ ϕ₁)]).
    {
        fm_solve.
    }
    assert (y ∉ free_evars_of_list []).
    {
        fm_solve.
    }

    assert (x0 <> y).
    {
        fm_solve.
    }

    assert (y <> x0).
    {
        fm_solve.
    }

    assert (X0 <> Y).
    {
        fm_solve.
    }

    assert (Y <> X0).
    {
        fm_solve.
    }

    assert (x ∉ free_evars (patt_imp ϕ₁ (patt_free_evar y))). {
      fm_solve.
    }
    assert (x ∉ free_evars (patt_imp ϕ₁ (patt_free_evar x0))). {
      fm_solve.
    }
    assert (X ∉ free_svars (patt_imp ϕ₁ (patt_free_svar Y))). {
      fm_solve.
    }
    assert (X ∉ free_svars (patt_imp ϕ₁ (patt_free_svar X0))). {
      fm_solve.
    }
    assert (x ∉ free_evars (evar_open x0 0 ϕ₁)). {
      fm_solve.
    }
    assert (x ∉ free_evars (nest_ex ϕ₁)). {
      fm_solve.
    }
    exact I.
Qed.


Import MatchingLogic.Substitution.Notations
       MatchingLogic.Syntax.Notations.
Open Scope ml_scope.

#[local]
Example freshman_usage_2
    {Σ : Signature}
    (x0 y0 : evar)
    (X0 Y0 : svar)
    (ϕ₁ ϕ₂ : Pattern)
    (Hwf1 : well_formed ϕ₁)
    (Hwf2 : well_formed (patt_exists ϕ₂))
    : exists x, x ∉ free_evars (ϕ₂^[evar: 0 ↦ ϕ₁]).
Proof.
  mlFreshEvar as x. exists x.
  ltac2:(_fm_export_everything ()).
  pose proof (free_evars_bevar_subst).
  set_solver.
Qed.

Close Scope ml_scope.
