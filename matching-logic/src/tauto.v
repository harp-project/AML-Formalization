From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Ltac2 Require Import Ltac2.

From Coq Require Import Ensembles Bool.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.

From Equations Require Import Equations.

From MatchingLogic Require Import Syntax Semantics DerivedOperators ProofSystem ProofMode MLTauto.

From stdpp Require Import list tactics fin_sets.

From MatchingLogic.Utils Require Import stdpp_ext.

Import extralibrary.

Import
  MatchingLogic.Syntax.Notations
  MatchingLogic.DerivedOperators.Notations
  MatchingLogic.ProofSystem.Notations
.

Set Default Proof Mode "Classic".

Open Scope ml_scope.

Section mgTauto.

  Context {Σ : Signature}.


  Lemma MyGoal_revert (Γ : Theory) (l : list Pattern) (x g : Pattern):
    @mkMyGoal Σ Γ l (x ---> g) ->
    @mkMyGoal Σ Γ (l ++ [x]) g.
  Proof.
    intros H.
    unfold of_MyGoal in H. simpl in H.
    unfold of_MyGoal. simpl. intros wfxig wfl.

    feed specialize H.
    {
      abstract (
          apply wfapp_proj_2 in wfl;
          unfold wf in wfl;
          simpl in wfl;
          rewrite andbT in wfl;
          wf_auto2
        ).
    }
    {
      abstract (apply wfapp_proj_1 in wfl; exact wfl).
    }

    eapply cast_proof.
    { rewrite foldr_app. simpl. reflexivity. }
    exact H.
  Defined.

  Ltac mgRevert :=
    match goal with
    | |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g)
      => eapply cast_proof_mg_hyps;
         [(rewrite -[l](take_drop (length l - 1)); rewrite [take _ _]/=; rewrite [drop _ _]/=; reflexivity)|];
         apply MyGoal_revert
    end.

  Lemma impl_eq_or Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢( (a ---> b) <---> ((! a) or b) ).
  Proof.
    intros wfa wfb.
    toMyGoal.
    { wf_auto2. }
    repeat mgIntro.
    mgDestructOr 0.
    - mgApply 0. mgIntro. mgClear 0. mgIntro.
      mgApplyMeta (@not_not_elim _ _ _ _) in 1.
      mgApply 0. mgAssumption.
    - mgApply 0. mgIntro. mgClear 0. mgIntro.
      mgDestructOr 0.
      + mgApplyMeta (@false_implies_everything _ _ _ _).
        mgApply 0. mgAssumption.
      + mgAssumption.
    Unshelve. all: auto.
  Qed.

  Lemma nimpl_eq_and Γ a b:
    well_formed a ->
    well_formed b ->
    Γ ⊢( ! (a ---> b) <---> (a and !b) ).
  Proof.
    intros wfa wfb.
    toMyGoal.
    { wf_auto2. }
    repeat mgIntro.
    mgDestructOr 0.
    - mgApply 0. repeat mgIntro.
      mgApply 1. mgIntro.
      mgDestructOr 2.
      + mgApplyMeta (false_implies_everything _ _).
        mgApply 2. mgAssumption.
      + mgApplyMeta (@not_not_elim _ _ _ _) in 2.
        mgAssumption.
    - mgApply 0. repeat mgIntro.
      mgDestructAnd 1. mgApply 2. mgApply 3.
      mgAssumption.
    Unshelve. all: auto.
  Qed.

  Lemma deMorgan_nand Γ a b:
      well_formed a ->
      well_formed b ->
      Γ ⊢ ( !(a and b) <---> (!a or !b) ).
    Proof.
      intros wfa wfb.
      toMyGoal.
      { wf_auto2. }
      repeat mgIntro.
      mgDestructOr 0.
      - mgRevert. mgApplyMeta (@not_not_intro _ _ _ _). repeat mgIntro.
        mgApplyMeta (@not_not_elim _ _ _ _) in 1.
        mgApply 0. mgIntro.
        mgDestructOr 3.
        all: mgApply 3; mgAssumption.
      - mgRevert. mgApplyMeta (@not_not_intro _ _ _ _). repeat mgIntro.
        mgDestructAnd 1.
        mgDestructOr 0.
        all: mgApply 0; mgAssumption.
      Unshelve. all: auto.
    Qed.

  Lemma deMorgan_nor Γ a b:
      well_formed a ->
      well_formed b ->
      Γ ⊢ ( !(a or b) <---> (!a and !b)).
    Proof.
      intros wfa wfb.
      toMyGoal.
      { wf_auto2. }
      repeat mgIntro.
      mgDestructOr 0.
      - mgRevert. mgApplyMeta (@not_not_intro _ _ _ _). repeat mgIntro.
        mgApply 0.
        mgDestructOr 1.
        + mgApplyMeta (@not_not_elim _ _ _ _) in 1.
          mgLeft. mgAssumption.
        + mgApplyMeta (@not_not_elim _ _ _ _) in 1.
          mgRight. mgAssumption.
      - mgRevert. mgApplyMeta (@not_not_intro _ _ _ _). repeat mgIntro.
        mgDestructAnd 0.
        mgDestructOr 2.
        + mgApply 0. mgAssumption.
        + mgApply 1. mgAssumption.
      Unshelve. all: auto.
    Qed.

  Lemma not_not_eq (Γ : Theory) (a : Pattern) :
    well_formed a ->
    Γ ⊢ (!(!a) <---> a).
  Proof.
    intros wfa.
    toMyGoal.
    { wf_auto2. }
    mgIntro.
    mgDestructOr 0.
    - mgApply 0. mgIntro.
      mgApplyMeta (@not_not_elim _ _ _ _) in 1.
      mgAssumption.
    - unfold patt_not. mgApply 0. repeat mgIntro.
      mgApply 2. mgAssumption.
    Unshelve.
    all: auto.
  Defined.

  Ltac convertToNNF_rewrite_pat Ctx p :=
    idtac p;
    lazymatch p with
      | (! ! ?x) =>
          idtac "Not not";
          let H' := fresh "H" in
          epose proof (@not_not_eq Ctx x _) as H';
          repeat (mgRewrite H' at 1);
          clear H';
          convertToNNF_rewrite_pat Ctx x
      | patt_not (patt_and ?x ?y) =>
          idtac "Not and";
          let H' := fresh "H" in
          epose proof (@deMorgan_nand Ctx x y _ _) as H';
          repeat (mgRewrite H' at 1);
          clear H';
          convertToNNF_rewrite_pat Ctx (!x or !y)
      | patt_not (patt_or ?x ?y) =>
          idtac "Not or";
          let H' := fresh "H" in
          epose proof (@deMorgan_nor Ctx x y _ _) as H';
          repeat (mgRewrite H' at 1);
          clear H';
          convertToNNF_rewrite_pat Ctx (!x and !y)
      | patt_not (?x ---> ?y) =>
          idtac "Not implication";
          let H' := fresh "H" in
          epose proof (@nimpl_eq_and Ctx x y _ _) as H';
          repeat (mgRewrite H' at 1);
          clear H';
          convertToNNF_rewrite_pat Ctx (x and !y)
      | (?x ---> ?y) =>
          idtac "Implication";
          let H' := fresh "H" in
          epose proof (@impl_eq_or Ctx x y _ _) as H';
          repeat (mgRewrite H' at 1);
          clear H';
          convertToNNF_rewrite_pat Ctx (!x or y)
      | patt_and ?x ?y => idtac "And"; convertToNNF_rewrite_pat Ctx x; convertToNNF_rewrite_pat Ctx y
      | patt_or ?x ?y => idtac "Or"; convertToNNF_rewrite_pat Ctx x; convertToNNF_rewrite_pat Ctx y
      | _ => idtac p
    end.

  Ltac toNNF := 
    repeat mgRevert;
    match goal with
      | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?ll ?g) ] 
        =>
          mgApplyMeta (@not_not_elim _ _ _ _);
          convertToNNF_rewrite_pat Ctx (!g)
    end.

  Ltac rfindContradictionTo a ll k n:=
    match ll with
      | ((! a) :: ?m) =>
          mgApply n; mgExactn k
      | (?b :: ?m) => 
          let nn := eval compute in ( n + 1 ) in
           (rfindContradictionTo a m k nn)
      | _ => fail
    end.

  Ltac findContradiction l k:=
      match l with
         | (?a :: ?m) => 
               match goal with
                  | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?ll ?g) ] 
                    =>
                       try rfindContradictionTo a ll k 0;
                       let kk := eval compute in ( k + 1 ) in
                       (findContradiction m kk)
               end
         | _ => fail
      end.

  Ltac findContradiction_start :=
    match goal with
      | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) ] 
        =>
          match goal with
            | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) ] 
              =>
                idtac l;
                findContradiction l 0
          end
    end.

  Ltac breakHyps l n:=
    let nn := eval compute in ( n + 1)
    in
    (
      match l with
      | ((?x and ?y) :: ?m) => 
          mgDestructAnd n
      | ((?x or ?y) :: ?m) => 
          mgDestructOr n
      | (?x :: ?m)  =>
          breakHyps m nn
      end
    )
  .

  Ltac mgTauto :=
    try (
    toNNF;
    idtac "NFF ready";
    repeat mgIntro;
    repeat match goal with
      | [ |- @of_MyGoal ?Sgm (@mkMyGoal ?Sgm ?Ctx ?l ?g) ] 
        =>
          lazymatch g with
            | (⊥) =>
                    breakHyps l 0
            | _ => mgApplyMeta (@false_implies_everything _ _ g _)
                    (*idtac "Goal is not correct form"*)
          end
    end;
    findContradiction_start)
  .

    Lemma conj_right Γ a b:
      well_formed a ->
      well_formed b ->
      Γ ⊢ ( (b and (a or b) and !b and ( a or a) and a) ---> ⊥).
    Proof.
      intros wfa wfb.
      toMyGoal.
      { wf_auto2. }
      mgTauto.
      Unshelve. all: wf_auto2.
    Qed.

    Lemma condtradict_taut_2 Γ a b:
      well_formed a ->
      well_formed b ->
      Γ ⊢( a ---> ((! a) ---> b)).
    Proof.
      intros wfa wfb.
      toMyGoal.
      { wf_auto2. }
      mgTauto.
      Unshelve. all: wf_auto2.
    Qed.

    Lemma taut Γ a b c:
      well_formed a ->
      well_formed b ->
      well_formed c ->
      Γ ⊢ ((a ---> b) ---> ((b ---> c) ---> ((a or b)---> c))).
    Proof.
      intros wfa wfb wfc.
      toMyGoal.
      { wf_auto2. }
      mgTauto.
      Unshelve. all: wf_auto2.
    Qed.

    Lemma condtradict_taut_1 Γ a:
      well_formed a ->
      Γ ⊢ !(a and !a).
    Proof.
      intros wfa.
      toMyGoal.
      { wf_auto2. }
      mgTauto.
      Unshelve. all: wf_auto2.
    Qed.

    Lemma notnot_taut_1 Γ a:
      well_formed a ->
      Γ ⊢ (! ! a ---> a).
    Proof.
      intros wfa.
      toMyGoal.
      { wf_auto2. }
      mgTauto.
      Unshelve. all: wf_auto2.
    Qed.

    Lemma Peirce_taut Γ a b:
      well_formed a ->
      well_formed b ->
      Γ ⊢ ((((a ---> b) ---> a) ---> a)).
    Proof.
      intros wfa wfb.
      toMyGoal.
      { wf_auto2. }
      mgTauto.
      Unshelve. all: wf_auto2.
    Qed.

End mgTauto.
