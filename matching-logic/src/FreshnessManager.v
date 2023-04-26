From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base gmap list.

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
    fm_evars_nodup : NoDup fm_evars ;
    fm_svars_nodup : NoDup fm_svars ;
}.


Notation "FreshMan()" := (@FreshnessManager _ _ _ _) : ml_scope.

Program Definition EmptyFreshMan {Σ : Signature} : FreshnessManager [] [] []
:= @mkFreshnessManager Σ [] [] [] _ _.
Next Obligation.
    intros. apply NoDup_nil. exact I.
Qed.
Next Obligation.
    intros. apply NoDup_nil. exact I.
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

Qed.
