From MatchingLogic.Theories Require Export FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Section TacticsNotations.
  Context {Σ : Signature} {syntax : Syntax}.

  Definition WFPattern := sig well_formed.
  Definition mkWFWrapper (f : Pattern -> Pattern -> Pattern) (wfp : forall a b, well_formed a -> well_formed b -> well_formed (f a b)) : WFPattern -> WFPattern -> WFPattern.
  Proof.
    intros * [a wfa] [b wfb].
    exists (f a b). exact (wfp a b wfa wfb).
  Defined.
  Definition WFPatt_imp := mkWFWrapper patt_imp well_formed_imp.
  Definition WFPatt_and := mkWFWrapper patt_and well_formed_and.
  Definition WFPatt_iff := mkWFWrapper patt_iff well_formed_iff.
  Definition WFPatt_equal := mkWFWrapper patt_equal well_formed_equal.
  Definition WFFree_evar_subst (x : evar) := mkWFWrapper (flip free_evar_subst x) (fun a b => well_formed_free_evar_subst x b a).
  Definition WFDerives (Γ : Theory) (p : WFPattern) : Set := derives Γ (proj1_sig p).
  Definition WFPatt_app := mkWFWrapper patt_app well_formed_app.
  Lemma well_formed_free_evar : forall e, well_formed (patt_free_evar e).
  Proof.
    exact (const eq_refl).
  Defined.

  Lemma lift_derives : forall Γ p, derives Γ (proj1_sig p) -> WFDerives Γ p.
  Proof.
    intros. auto.
  Defined.

  Lemma unwrap_wfwrapper : forall f wff a b, proj1_sig (mkWFWrapper f wff a b) = f (`a) (`b).
  Proof.
    now intros ? ? [a wfa] [b wfb].
  Defined.

  Lemma wfWFPattern : forall (p : WFPattern), well_formed (proj1_sig p).
  Proof.
    intros [p wfp]. exact wfp.
  Defined.

  Lemma WFPattern_eq_dec : EqDecision (WFPattern * WFPattern).
  Proof.
    apply @prod_eq_dec.
    all: apply sig_eq_dec.
    1, 3: intros; apply eq_pi; apply decide_rel; apply bool_eq_dec.
    1, 2: apply Pattern_eqdec.
  Defined.

End TacticsNotations.

Notation "a wf---> b"  := (WFPatt_imp a b) (at level 75, right associativity) : ml_scope.
Notation "a 'wfand' b" := (WFPatt_and   a b) (at level 72, left associativity) : ml_scope.
Notation "a wf<---> b" := (WFPatt_iff a b) (at level 74, no associativity) : ml_scope.
Notation "p wf=ml q" := (WFPatt_equal p q) (at level 67) : ml_scope.
Notation "e ^wf[[ 'evar:' x ↦ e' ]]" := (WFFree_evar_subst x e' e) (at level 2, e' at level 200, left associativity, format "e ^wf[[ 'evar:' x ↦ e' ]]" ) : ml_scope.
Notation "Γ ⊢wf ϕ" := (WFDerives Γ ϕ) (at level 95, no associativity).
Notation "a wf⋅ b" := (WFPatt_app a b) (at level 66, left associativity) : ml_scope.

Tactic Notation "mlDeductHypo" constr(name) :=
  match goal with
  | [ |- context[ mkNH _ name (⌊ ?p ⌋) ] ] => 
      match goal with
      | [ |- context[ mkMLGoal _ ?t _ _ _ ] ] =>
          mlDeduct name;
          let i := fresh "i" in remember (ExGen := _, SVSubst := _, KT:= _, AKT := _) as i;
          let H := fresh "H" in opose proof (hypothesis (t ∪ {[p]}) p _ ltac:(set_solver)) as H;
          last first;
          [use i in H |]
      end
  end.

Tactic Notation "mlDestructBotDocVer" := match goal with [ |- context [mkNH _ ?x patt_bott] ] => mlDestructBot x end.

Tactic Notation "refine_wf" := repeat first [
  apply well_formed_imp |
  apply well_formed_and |
  apply well_formed_equal |
  apply well_formed_free_evar_subst |
  apply well_formed_top |
  apply well_formed_free_evar
  ].

Tactic Notation "mlDecomposeAll" := do !
  match goal with
  | [ |- context[(mkMLGoal _ _ _ (patt_imp _ _) _)] ] => mlIntro
  | [ |- context[mkNH _ ?x (patt_and _ _)] ] => mlDestructAnd x
  end.

Tactic Notation "inside" tactic(inside) "outside" tactic(outside) :=
  match goal with
  | [ |- of_MLGoal _ ] => inside
  | _ => outside
  end.

Tactic Notation "mlConjFast" constr(a) constr(b) "as" constr(c) "wfby" tactic(d) := match goal with | [ |- context[mkNH _ a ?x] ] => match goal with | [ |- context[mkNH _ b ?y] ] => mlAssert (c : (x and y)); [d | mlSplitAnd; [mlExact a | mlExact b] |] end end.

Tactic Notation "mlConjFast" constr(a) constr(b) "as" constr(c) := mlConjFast a b as c wfby idtac.

