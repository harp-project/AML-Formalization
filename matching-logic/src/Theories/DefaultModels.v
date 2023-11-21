 From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.
From Equations Require Import Equations.

From MatchingLogic Require Import Logic.
Import MatchingLogic.Logic.Notations.
From MatchingLogic.Utils Require Import Lattice stdpp_ext extralibrary.

From stdpp Require Import base fin_sets sets propset proof_irrel option list finite.

Import extralibrary.

From MatchingLogic.Theories Require Import Definedness_Syntax
                                           Sorts_Syntax
                                           Bool_Syntax
                                           Definedness_Semantics
                                           Sorts_Semantics
                                           Bool_Semantics
.
Import Definedness_Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.


Open Scope ml_scope.

Section Definedness.

  Context {Σ : Signature} {M : Model}
          {string_vars : variables = StringMLVariables}.

  Instance definedness_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols (@symbols (@ml_symbols Σ) + Definedness_Syntax.Symbols) _ _;
  }.
  Instance definedness_syntax : Definedness_Syntax.Syntax := {
     inj := inr;
  }.

  Definition definedness_carrier : Type := Domain M + unit.
  Definition definedness_sym_interp (m : @symbols (@ml_symbols Σ) + Definedness_Syntax.Symbols)
    : propset definedness_carrier :=
  match m with
  | inl x => inl <$> (sym_interp M x)
  | inr x => {[ inr () ]}
  end.

  Definition definedness_app_interp (m1 m2 : definedness_carrier)
    : propset definedness_carrier :=
  match m1 with
  | inr () => ⊤
  | inl x1 =>
     match m2 with
     | inl x2 => inl <$> app_interp M x1 x2
     | inr () => ∅
     end
  end.

  Definition DefinednessModel : Model := {|
    Domain := definedness_carrier;
    app_interp := definedness_app_interp;
    sym_interp := definedness_sym_interp;
  |}.

  Theorem DefinednessModel_satisfies_theory :
    DefinednessModel ⊨ᵀ Definedness_Syntax.theory.
  Proof.
    unfold Definedness_Syntax.theory. unfold Definedness_Syntax.named_axioms.
    unfold theory_of_NamedAxioms. simpl.
    unfold satisfies_theory. intros.
    rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
    cbn. unfold satisfies_model. intros.
    unfold patt_defined. unfold p_x, ev_x. simp eval.
    unfold sym_interp, app_ext. simpl.
    eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ DefinednessModel).
    apply set_equiv. intros. split; intros.
    * rewrite elem_of_PropSet in H. destruct H as [le [re [Hle [Hre Hx] ] ] ].
      destruct Hle. destruct Hre. by simpl in Hx.
    * rewrite elem_of_PropSet. exists (inr ()), (evar_valuation ρ (evar_fresh [])).
      set_solver.
  Qed.

End Definedness.

(* This is independent of ModelExtension.v, but it is very similar to it *)
Section Sorts.
  Context {Σ : Signature} {M : Model}
          {string_vars : variables = StringMLVariables}
          {sort_interp : Domain M -> propset M}.

  Instance sorts_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols (@symbols (@ml_symbols (definedness_Σ)) + Sorts_Syntax.Symbols) _ _;
  }.

  (* TODO: can we avoid Program? *)
  Program Instance sorts_syntax : @Sorts_Syntax.Syntax sorts_Σ := {
     inj := inr;
     imported_definedness := _;
  }.
  Next Obligation.
    constructor.
    intros x. destruct x.
    apply inl. apply inr. apply definedness.
  Defined.

  Definition sorts_carrier : Type := Domain (@DefinednessModel Σ M) + unit.
  Definition sorts_sym_interp (m : @symbols (@ml_symbols (@definedness_Σ Σ)) + Sorts_Syntax.Symbols)
    : propset sorts_carrier :=
  match m with
  | inl x => inl <$> (sym_interp (@DefinednessModel Σ M) x)
  | inr x => {[ inr () ]}
  end.

  Definition sorts_app_interp (m1 m2 : sorts_carrier)
    : propset sorts_carrier :=
  match m1, m2 with
  | inr (), inr ()       => ∅ (* inh $ inh *)
  | inr (), inl (inr ()) => ∅ (* inh $ def *)
  | inr (), inl (inl x)  =>   (* inh $ x *)
        (inl ∘ inl) <$> (sort_interp x)
  | inl (inr _), inr _   => ⊤ (* ⌈ ⌉ $ inh <- Notion of definedness has to be extended *)
  | inl (inr _), inl _   => ⊤ (* ⌈ ⌉ $ x <- Notion of definedness has to be extended *)
  | inl (inl _), inr _   => ∅ (* x $ inh *)
  | inl x1, inl x2       =>   (* x $ y*)
        inl <$> app_interp DefinednessModel x1 x2
  end.

  Definition SortsModel : Model := {|
    Domain := sorts_carrier;
    app_interp := sorts_app_interp;
    sym_interp := sorts_sym_interp;
  |}.

  Theorem SortsModel_satisfies_theory :
    SortsModel ⊨ᵀ Definedness_Syntax.theory.
  Proof.
    unfold Definedness_Syntax.theory. unfold Definedness_Syntax.named_axioms.
    unfold theory_of_NamedAxioms. simpl.
    unfold satisfies_theory. intros.
    rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
    cbn. unfold satisfies_model. intros.
    unfold patt_defined. unfold p_x, ev_x. simp eval.
    unfold sym_interp, app_ext. simpl.
    eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ SortsModel).
    apply set_equiv. intros. split; intros.
    * rewrite elem_of_PropSet in H. destruct H as [le [re [Hle [Hre Hx] ] ] ].
      destruct Hle. destruct Hre. by simpl in Hx.
    * rewrite elem_of_PropSet.
      exists (inl (inr ())), (evar_valuation ρ (evar_fresh [])).
      cbn. case_match; set_solver.
  Qed.
End Sorts.

Section Bool.
  (* TODO: Bool syntax should use bools as core symbols too to avoid boiler-plate
           PartialAnd is needed to represent partial application of &&ml
   *)
  Inductive bool_carrier :=
  | coreBoolSym (s : Bool_Syntax.Symbols)
  | partialAnd (b : bool)
  | defBool
  | inhBool
  .

  #[global]
  Instance bool_carrier_EqDec : EqDecision bool_carrier.
  Proof.
    solve_decision.
  Defined.

  #[global]
  Program Instance bool_carrier_finite : finite.Finite bool_carrier.
  Next Obligation.
    exact (fmap coreBoolSym [sBool; sTrue; sFalse; sAnd; sNeg] ++ 
           [partialAnd true; partialAnd false; defBool; inhBool]).
  Defined.
  Next Obligation.
    compute_done.
  Defined.
  Next Obligation.
    destruct x; try destruct s; try destruct b; compute_done.
  Defined.

  Global Instance bool_carrier_countable : countable.Countable bool_carrier.
  Proof. apply finite.finite_countable. Defined.

  Instance bools_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols bool_carrier _ _;
  }.

  Program Instance bool_syntax : @Bool_Syntax.Syntax bools_Σ := {
    inj := coreBoolSym;
    imported_sorts := {|
      Sorts_Syntax.inj := fun x => inhBool;
      imported_definedness := {|
        Definedness_Syntax.inj := fun x => defBool;
      |};
    |};
  }.

  Definition bool_sym_interp (m : symbols)
    : propset bool_carrier := {[ m ]}.

  Definition bool_app_interp (m1 m2 : bool_carrier)
    : propset bool_carrier :=
  match m1 with
   | coreBoolSym sAnd =>
     match m2 with
     | coreBoolSym sTrue => {[ partialAnd true ]}
     | coreBoolSym sFalse => {[ partialAnd false ]}
     | _ => ∅
     end
   | coreBoolSym sNeg =>
     match m2 with
     | coreBoolSym sTrue => {[ coreBoolSym sFalse ]}
     | coreBoolSym sFalse => {[ coreBoolSym sTrue ]}
     | _ => ∅
     end
   | coreBoolSym _ => ∅
   | partialAnd false =>
     match m2 with
     | coreBoolSym sTrue => {[ coreBoolSym sFalse ]}
     | coreBoolSym sFalse => {[ coreBoolSym sFalse ]}
     | _ => ∅
     end
   | partialAnd true =>
     match m2 with
     | coreBoolSym sTrue => {[ coreBoolSym sTrue ]}
     | coreBoolSym sFalse => {[ coreBoolSym sFalse ]}
     | _ => ∅
     end
   | defBool => ⊤
   | inhBool =>
     match m2 with
     | coreBoolSym sBool => {[ coreBoolSym sFalse; coreBoolSym sTrue ]}
     | _ => ∅
     end
  end.

  Global Instance bool_carrier_inhabited : Inhabited bool_carrier.
  Proof.
    constructor. exact defBool.
  Defined.

  Program Definition BoolModel : Model := {|
    Domain := bool_carrier;
    app_interp := bool_app_interp;
    sym_interp := bool_sym_interp;
  |}.

  Theorem BoolModel_satisfies_theory :
    BoolModel ⊨ᵀ Bool_Syntax.theory.
  Proof.
    unfold Bool_Syntax.theory, Definedness_Syntax.theory.
    unfold theory_of_NamedAxioms. simpl.
    unfold satisfies_theory. intros.
    rewrite elem_of_union in H. destruct H as [H | H].
    * rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
      cbn. unfold satisfies_model. intros.
      unfold patt_defined. unfold p_x, ev_x. simp eval.
      unfold sym_interp, app_ext. simpl.
      eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ BoolModel).
      apply set_equiv. intros. split; intros; set_solver.
    * rewrite elem_of_PropSet in H. destruct H.
      destruct x;subst;cbn; unfold satisfies_model; intros.
      - (* TODO: simplification tactic for eval is needed! Potentially we could base this
           on typeclasses too. *)
      -
      -
      -
      -
      -
      -
      -
      -
      -
      -
      -
  Defined.

End Bool.

