From MatchingLogic.Theories Require Export FOEquality_ProofSystem.
Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.

Set Default Proof Mode "Classic".

Close Scope equations_scope. (* Because of [!] *)

Section TacticsNotations.
  Context {Σ : Signature} {syntax : Syntax}.

  Record WFMFPattern := mkWFMF {
    wfmfPattern :> Pattern;
    wfmfWF : well_formed wfmfPattern;
    wfmfMF : mu_free wfmfPattern;
  }.

  Record TermPattern := mkTP {
    tpPattern :> WFMFPattern;
    tpFP : forall Γ, Γ ⊢ is_functional tpPattern;
  }.

  Record WFMFBinary := mkWFMFB {
    wfmfbF : Pattern -> Pattern -> Pattern;
    wfmfbWF : ∀ φ1 φ2, well_formed φ1 -> well_formed φ2 -> well_formed (wfmfbF φ1 φ2);
    wfmfbMF : ∀ φ1 φ2, mu_free φ1 -> mu_free φ2 -> mu_free (wfmfbF φ1 φ2);
    wfmfbWrapper :> WFMFPattern -> WFMFPattern -> WFMFPattern :=
      λ '(mkWFMF a wfa mfa) '(mkWFMF b wfb mfb), mkWFMF
        (wfmfbF a b)
        (wfmfbWF a b wfa wfb)
        (wfmfbMF a b mfa mfb)
    ;
  }.

  Lemma unwrap_wfmfbWrapper f a b : wfmfPattern (wfmfbWrapper f a b) = wfmfbF f (wfmfPattern a) (wfmfPattern b).
  Proof.
    destruct f, a, b. reflexivity.
  Defined.

  (**
     Low-level mu-free solver to avoid huge proof terms later on.
   *)
  Tactic Notation "solve_mf" :=
    simpl; unfold is_true; intros;
    repeat match goal with
           | [ |- _ && true = true ] => refine (eq_trans (andb_true_r _) _)
           | [ |- _ && _ = true ] => refine (andb_true_intro (conj _ _))
           | [ mf : mu_free ?φ = true |- mu_free ?φ = true ] => exact mf
           end.

  Definition WFMF_imp := mkWFMFB
    patt_imp
    well_formed_imp
    ltac:(solve_mf)
  .

  Definition WFMF_and := mkWFMFB
    patt_and
    well_formed_and
    ltac:(solve_mf)
  .

  Definition WFMF_iff := mkWFMFB
    patt_iff
    well_formed_iff
    ltac:(solve_mf)
  .

  Definition WFMF_equal := mkWFMFB
    patt_equal
    well_formed_equal
    ltac:(solve_mf)
  .

  Definition WFMF_app := mkWFMFB
    patt_app
    well_formed_app
    ltac:(solve_mf)
  .

  Definition WFMF_fevar_subst x := mkWFMFB
    (free_evar_subst ^~ x)
    (λ a b, well_formed_free_evar_subst x b a)
    (λ a b H H', mu_free_free_evar_subst b a x H' H)
  .
  
  (**
     With the coercions, it should be a lot easier to write things like
     this. WFDerives probably won't even be needed.
   *)
  Check λ (x y : TermPattern), WFMF_and x y.
  Check λ (x : TermPattern) (y : WFMFPattern) Γ, Γ ⊢ WFMF_and x y.

  (*
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
   *)
  Lemma well_formed_free_evar : forall e, well_formed (patt_free_evar e).
  Proof.
    exact (const eq_refl).
  Defined.

  Instance WFMFPattern_eq_dec : EqDecision WFMFPattern.
  Proof.
    unfold EqDecision, Decision.
    intros [φ1 wf1 mf1] [φ2 wf2 mf2].
    destruct (decide (φ1 = φ2)) as [-> |]; [left | right; congruence].
    rewrite (Classical_Prop.EqdepTheory.UIP _ _ _ wf1 wf2)
            (Classical_Prop.EqdepTheory.UIP _ _ _ mf1 mf2).
    reflexivity.
  Defined.

  Instance TermPattern_eq_dec : EqDecision TermPattern.
  Proof.
    unfold EqDecision, Decision.
    intros [wfmf1 fp1] [wfmf2 fp2].
    destruct (decide (wfmf1 = wfmf2)) as [-> |]; [left | right; congruence].
    f_equal.
    apply functional_extensionality_dep_good. intros Γ.
    (**
       There are two options here:
       1. These proofs should be irrelevant, which they would be if our
          proof system was in Prop.
       2. The differences in the proofs matter, and they should be
          compared like the patterns.
       I don't know which is the right move here, but I found no way to
       do either.
     *)
  Admitted.

  (*
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
   *)

End TacticsNotations.

Notation "a wf---> b"  := (WFMF_imp a b) (at level 75, right associativity) : ml_scope.
Notation "a 'wfand' b" := (WFMF_and   a b) (at level 72, left associativity) : ml_scope.
Notation "a wf<---> b" := (WFMF_iff a b) (at level 74, no associativity) : ml_scope.
Notation "p wf=ml q" := (WFMF_equal p q) (at level 67) : ml_scope.
Notation "e ^wf[[ 'evar:' x ↦ e' ]]" := (WFMF_fevar_subst x e' e) (at level 2, e' at level 200, left associativity, format "e ^wf[[ 'evar:' x ↦ e' ]]" ) : ml_scope.
(* Notation "Γ ⊢wf ϕ" := (WFDerives Γ ϕ) (at level 95, no associativity). *)
Notation "a wf⋅ b" := (WFMF_app a b) (at level 66, left associativity) : ml_scope.

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

