From MatchingLogic.Theories Require Import Definedness_Semantics
                                           Sorts_Syntax
                                           Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Lemma membership_var {Σ : Signature} {syntax : Syntax} :
  forall x y Γ,
  theory ⊆ Γ ->
  Γ ⊢ patt_free_evar y ∈ml patt_free_evar x ---> patt_free_evar y =ml patt_free_evar x.
Proof.
  intros x y Γ HΓ.
  
  remember (patt_free_evar x) as pX. assert (well_formed pX) by (rewrite HeqpX;auto).
  remember (patt_free_evar y) as pY. assert (well_formed pY) by (rewrite HeqpY;auto).
  toMLGoal. wf_auto2.
  unfold patt_equal, patt_iff.
  pose proof (patt_total_and Γ (pY ---> pX) (pX ---> pY) HΓ 
                        ltac:(wf_auto2) ltac:(wf_auto2)) as H1.
  use AnyReasoning in H1.
  mlRewrite H1 at 1.
  mlIntro "H0".
  mlIntro "H1".
  mlDestructOr "H1" as "H1'" "H1'".
  * mlApply "H1'".
    mlClear "H1'".
    mlIntro "H2".
    pose proof (MH := nimpl_eq_and Γ pY pX
                  ltac:(wf_auto2) ltac:(wf_auto2)).
    use AnyReasoning in MH.
    mlRevertLast.
    mlRewrite MH at 1.
    (* TODO: it is increadibly inconvienient to define concrete contexts *)
    unshelve (epose proof (MH1 := @Singleton_ctx _ Γ 
           (⌈_⌉ $ᵣ □)
           (⌈_⌉ $ᵣ □) pX y ltac:(wf_auto2))). 1-2: wf_auto2.
    rewrite -HeqpY in MH1.
    use AnyReasoning in MH1. simpl in MH1.
    (* TODO: having mlExactMeta would help here *)
    mlIntro "H2".
    mlApplyMeta MH1.
    mlSplitAnd.
    ** mlExact "H0".
    ** mlExact "H2".
  * mlApply "H1'".
    mlClear "H1'".
    mlIntro "H2".
    pose proof (MH := nimpl_eq_and Γ pX pY
                  ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRevertLast. use AnyReasoning in MH. mlRewrite MH at 1.
    pose proof (MH1 := @patt_and_comm _ Γ pY pX ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRevertLast. use AnyReasoning in MH1.
    unfold patt_in.
    mlRewrite MH1 at 1.
    unshelve (epose proof (@Singleton_ctx _ Γ 
           (⌈_⌉ $ᵣ □)
           (⌈_⌉ $ᵣ □) pY x ltac:(wf_auto2)) as MH2). 1-2: wf_auto2.
    rewrite -HeqpX in MH2.
    use AnyReasoning in MH2.
    mlIntro "H1". mlIntro "H2".
    mlApplyMeta MH2. simpl. mlSplitAnd. mlExact "H1". mlExact "H2".
Defined.
