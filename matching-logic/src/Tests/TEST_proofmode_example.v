From Coq Require Import ssreflect ssrfun ssrbool.

From Ltac2 Require Import Ltac2.

Require Import Equations.Prop.Equations.

From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.

From MatchingLogic Require Import Syntax NamedAxioms DerivedOperators_Syntax ProofSystem ProofMode IndexManipulation Substitution ApplicationContext.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.

Require Import MatchingLogic.wftactics.

From stdpp Require Import base fin_sets sets propset proof_irrel option list coGset finite infinite gmap.

Import MatchingLogic.Syntax.Notations
       MatchingLogic.DerivedOperators_Syntax.Notations
       MatchingLogic.Syntax.BoundVarSugar
       MatchingLogic.ProofSystem.Notations
       MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.ApplicationContext.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Import Notations.
Open Scope ml_scope.
Open Scope string_scope.

Lemma overlapping_variables_equal {Σ : Signature} {syntax : Syntax} :
  forall x y Γ,
  theory ⊆ Γ ->
  Γ ⊢ overlaps_with (patt_free_evar y) (patt_free_evar x) ---> patt_free_evar y =ml patt_free_evar x.
Proof.
  intros x y Γ HΓ.
  
  remember (patt_free_evar x) as pX. assert (well_formed pX) by (rewrite HeqpX;auto).
  remember (patt_free_evar y) as pY. assert (well_formed pY) by (rewrite HeqpY;auto).
  unfold overlaps_with.
  toMLGoal. wf_auto2.
  unfold patt_equal, patt_iff.
  mlRewrite (useAnyReasoning (patt_total_and Γ
                                (pY ---> pX)
                                (pX ---> pY) HΓ
                                ltac:(wf_auto2) ltac:(wf_auto2))) at 1.
  fold AnyReasoning.
  mlIntro "H0".
  mlIntro "H1".
  mlDestructOr "H1" as "H1'" "H1'".
  * mlApply "H1'".
    mlClear "H1'".
    mlIntro "H2".
    pose proof (MH := @ProofMode_propositional.nimpl_eq_and _ Γ pY pX
                  ltac:(wf_auto2) ltac:(wf_auto2)).
    apply useAnyReasoning in MH.
    mlRevertLast.
    mlRewrite MH at 1. fold AnyReasoning.
    (* TODO: it is increadibly inconvienient to define concrete contexts *)
    unshelve (epose proof (MH1 := @Singleton_ctx _ Γ 
           (⌈_⌉ $ᵣ □)
           (⌈_⌉ $ᵣ □) pX y ltac:(wf_auto2))). 1-2: wf_auto2.
    rewrite -HeqpY in MH1.
    apply useAnyReasoning in MH1. simpl in MH1.
    (* TODO: having mlExactMeta would help here *)
    mlIntro "H2".
    mlApplyMeta MH1.
    mlSplitAnd.
    ** mlExact "H0".
    ** mlExact "H2".
  * mlApply "H1'".
    mlClear "H1'".
    mlIntro "H2".
    pose proof (MH := @ProofMode_propositional.nimpl_eq_and _ Γ pX pY
                  ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRevertLast. apply useAnyReasoning in MH. mlRewrite MH at 1.
    pose proof (MH1 := @patt_and_comm _ Γ pY pX ltac:(wf_auto2) ltac:(wf_auto2)).
    mlRevertLast. apply useAnyReasoning in MH1. mlRewrite MH1 at 1.
    unshelve (epose proof (@Singleton_ctx _ Γ 
           (⌈_⌉ $ᵣ □)
           (⌈_⌉ $ᵣ □) pY x ltac:(wf_auto2)) as MH2). 1-2: wf_auto2.
    rewrite -HeqpX in MH2.
    apply useAnyReasoning in MH2.
    mlIntro "H1". mlIntro "H2".
    mlApplyMeta MH2. simpl. mlSplitAnd. mlExact "H1". mlExact "H2".
Defined.

Close Scope ml_scope.
Close Scope string_scope.