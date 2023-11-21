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

Section Sorts.
  Context {Σ : Signature} {M : Model}
          {string_vars : variables = StringMLVariables}
          {sort_interp : Domain M -> propset M}.

  Instance sorts_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols (@symbols (@ml_symbols (definedness_Σ)) + Sorts_Syntax.Symbols) _ _;
  }.

  (* TODO: can we avoid Program? *)
  Program Instance sorts_syntax : Sorts_Syntax.Syntax := {
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

