From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2 Control.

From stdpp Require Import list tactics fin_sets coGset gmap sets.


Set Default Proof Mode "Classic".

(* Language With Propositional connectives *)
Class LWP := {
    lwp_formula : Type ;

    lwp_formula_eqdec :: EqDecision lwp_formula ;

    lwp_formula_countable :: Countable lwp_formula ;

    lwp_imp : lwp_formula -> lwp_formula -> lwp_formula ;
    lwp_bot : lwp_formula ;

    lwp_and : lwp_formula -> lwp_formula -> lwp_formula ;
    lwp_or  : lwp_formula -> lwp_formula -> lwp_formula ;
    lwp_not : lwp_formula -> lwp_formula ;

    (* Maybe, if we want, we can later relax these to equiprovability instead of equality *)
    lwp_not_correct :
        forall phi,
            lwp_not phi = lwp_imp phi lwp_bot
    ;
    lwp_or_correct :
        forall phi1 phi2,
            lwp_or phi1 phi2 = lwp_imp (lwp_not phi1) phi2
    ;

    lwp_and_correct :
        forall phi1 phi2,
        lwp_and phi1 phi2 = lwp_not (lwp_or (lwp_not phi1) (lwp_not phi2))
    ;
}.

Definition lwp_Theory {lwp : LWP} := gset lwp_formula.

Class LwpProvability {lwp : LWP} := {
    lwp_pf : lwp_Theory -> lwp_formula -> Type ;

    lwp_p1 : forall G phi1 phi2,
        lwp_pf G (lwp_imp phi1 (lwp_imp phi2 phi1))
    ;
    lwp_p2 : forall G phi1 phi2 phi3,
        lwp_pf G (lwp_imp (lwp_imp phi1 (lwp_imp phi2 phi3)) (lwp_imp (lwp_imp phi1 phi2) (lwp_imp phi1 phi3)))
    ;
    lwp_p3 : forall G phi1,
        lwp_pf G (lwp_imp (lwp_not (lwp_not phi1)) phi1)
    ;

    lwp_mp : forall G phi1 phi2,
        lwp_pf G phi1 ->
        lwp_pf G (lwp_imp phi1 phi2) ->
        lwp_pf G phi2
    ;
}.

Arguments lwp_mp {lwp LwpProvability G phi1 phi2} pf1 pf2.


Declare Scope lwp_scope.
Open Scope lwp_scope.

Module Notations.

    Notation "A ---> B" := (lwp_imp A B) (at level 75, right associativity) : lwp_scope.

End Notations.


Section with_LWP_and_theory.
    Import Notations.

    Context
        {lwp : LWP}
        {lwpP : LwpProvability}
        (Γ : lwp_Theory)
    .

    Lemma A_impl_A  (A : lwp_formula)  :
        lwp_pf Γ (A ---> A)
    .
    Proof. 
        pose proof (_1 := lwp_p2 Γ A (A ---> A) A).
        pose proof (_2 := lwp_p1 Γ A (A ---> A)).
        pose proof (_3 := lwp_mp _2 _1).
        pose proof (_4 := lwp_p1 Γ A A ).
        pose proof (_5 := lwp_mp _4 _3).
        exact _5.
    Defined.

End with_LWP_and_theory.