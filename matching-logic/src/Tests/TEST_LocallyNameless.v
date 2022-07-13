From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import String Ensembles.
Require Import Coq.Logic.Classical_Prop.

From stdpp Require Import base fin_sets sets propset finite.

From MatchingLogic Require Import Syntax Semantics DerivedOperators_Syntax DerivedOperators_Semantics StringSignature ProofSystem ProofMode.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_Semantics Sorts_Syntax Sorts_Semantics Definedness_ProofSystem.
From MatchingLogic.Utils Require Import stdpp_ext.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.ProofSystem.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.IndexManipulation.

(* In this module we show how to define a signature and build patterns *)
Module test_1.
  (* We have three symbols *)
  Inductive Symbols := ctor| p | f .


  #[local]
  Instance Symbols_eqdec : EqDecision Symbols.
  Proof. solve_decision. Defined.

  #[local]
  Program Instance Symbols_fin : Finite Symbols :=
  {|
    enum := [ctor;p;f]
  |}.
  Next Obligation.
    repeat constructor; set_solver.
  Qed.
  Next Obligation.
    destruct x; set_solver.
  Qed.


  #[local]
  Instance signature : Signature :=
    {| variables := StringMLVariables ;
       symbols := Symbols ;
    |}.
    
  (* Example patterns *)
  
  Definition a_symbol : Pattern := patt_sym ctor.

  Open Scope string_scope.

  Definition A : Pattern := (patt_free_svar "A").
  Definition B : Pattern := (patt_free_svar "B").
  Definition C : Pattern := (patt_free_svar "C").
  Definition D : Pattern := (patt_free_svar "D").

  Definition a : Pattern := (patt_free_evar "a").
  Definition b : Pattern := (patt_free_evar "b").
  Definition c : Pattern := (patt_free_evar "c").
  Definition d : Pattern := (patt_free_evar "d").
  
  Definition more : Pattern := A or ! A.

  Example e1 X: evar_open 0 X more = more.
  Proof. unfold more. unfold evar_open. simpl_bevar_subst. reflexivity. Qed.
  
  Definition complex : Pattern :=
    a ---> (b ---> !C) $ ex , D $ Bot and Top.

  Definition custom_constructor := patt_sym ctor.

  (* p x1 x2 *)
  Definition predicate : Pattern := patt_sym (ctor) $ (patt_free_evar "x1") $ (patt_free_evar "x2").
  
  (* f x (mu y . y) *)
  Definition function :=
    (patt_sym f) $ (patt_free_evar "x") $ (mu , (patt_bound_svar 0)).

  (* forall x, x /\ y *)
  Definition free_and_bound :=
    all , (patt_bound_evar 0) and (patt_free_evar "y").
  (* End of examples. *)

End test_1.


(* Here we show how to use the Definedness module. *)
Module test_2.
  Section test_2.
    Import Definedness_Syntax.

    (* We must include all the symbols from the Definedness module into our signature.
       We do this by defining a constructor `sym_import_definedness : Definedness.Symbols -> Symbols`.
       And we also define a bunch of other symbols.
     *)
    Inductive Symbols :=
    | sym_import_definedness (d : Definedness_Syntax.Symbols)
    | sym_import_sorts (s : Sorts_Syntax.Symbols)
    | sym_SortNat
    | sym_zero | sym_succ (* constructors for Nats *)
    | sym_c (* some constant that we make functional *)
    .

    Instance Symbols_eqdec : EqDecision Symbols.
    Proof. solve_decision. Defined.

    #[local]
    Program Instance Symbols_fin : Finite Symbols :=
    {|
      enum := [sym_c; sym_zero; sym_succ; sym_SortNat;
        sym_import_sorts Sorts_Syntax.inhabitant;
        sym_import_definedness Definedness_Syntax.definedness] ;
    |}.
    Next Obligation.
      repeat constructor; set_solver.
    Qed.
    Next Obligation.
      destruct x; try set_solver.
      destruct d; set_solver.
      destruct s; set_solver.
    Qed.

    Instance signature : Signature :=
      {| variables := StringMLVariables ;
         symbols := Symbols ;
      |}.

    Instance definedness_syntax : Definedness_Syntax.Syntax :=
      {|
         Definedness_Syntax.inj := sym_import_definedness;
      |}.

    Instance sorts_syntax : Sorts_Syntax.Syntax :=
      {|
      Sorts_Syntax.inj := sym_import_sorts;
      Sorts_Syntax.imported_definedness := definedness_syntax;
      |}.
    
    Example test_pattern_0 : Pattern := patt_sym sym_c.
    Example test_pattern_1 : Pattern := @patt_defined signature definedness_syntax (patt_sym sym_c).
    Example test_pattern_2 : Pattern := patt_defined (patt_sym sym_c).
    Example test_pattern_3 s : Pattern := patt_equal (patt_sym s) (patt_sym s).
    Example test_pattern_4 : Pattern := patt_defined (patt_sym sym_c).
    Example test_pattern_5 : Pattern := patt_equal (patt_inhabitant_set (patt_sym sym_SortNat)) (patt_sym sym_zero).

    Example test_pattern_3_open s x : evar_open 0 x (test_pattern_3 s) = (test_pattern_3 s).
    Proof. unfold test_pattern_3. unfold evar_open. simpl_bevar_subst. reflexivity. Qed.

    Inductive CustomElements :=
    | m_def (* interprets the definedness symbol *)
    | m_succ (* the successor function on nats *)
    | m_some_element (* just some element so that things do not get boring *)
    .

    Instance CustomElements_eqdec : EqDecision CustomElements.
    Proof. solve_decision. Defined.
    
    Inductive domain : Set :=
    | dom_nat (n:nat)
    | dom_custom (c:CustomElements)
    .    

    Instance domain_inhabited : Inhabited domain := populate (dom_nat 0).
    
    Instance domain_eqdec : EqDecision domain.
    Proof. solve_decision. Defined.

    Definition my_sym_interp(s: Symbols) : propset domain :=
      match s with
      | sym_import_definedness s_def => {[ (dom_custom m_def) ]}
      | sym_zero => {[ (dom_nat 0) ]}
      | sym_succ => {[ (dom_custom m_succ) ]}
      | _ => ∅
      end.

    Definition my_app_interp(m1 m2 : domain) : propset domain :=
      match m1, m1 with
      | dom_custom m_def, _ => ⊤ (* definedness *)
      | dom_custom m_succ, dom_nat n => {[ (dom_nat (n+1)) ]}
      | _, _ => ∅
      end.
    
    Definition M1 : Model :=
      {| Domain := domain;
         sym_interp := my_sym_interp;
         app_interp := my_app_interp;
      |}.

    (* FIXME: Otherwise, when I do [simpl], Coq replaces [Domain M1] with [domain]
       and that breaks typeclass search; namely, simple apply propset_leibniz_equiv.
     *)
    Arguments Domain : simpl never.

    (* TODO a tactic that solves this, or a parameterized lemma. *)
    
    Lemma M1_satisfies_definedness1 : @satisfies_model signature M1 (Definedness_Syntax.axiom Definedness_Syntax.AxDefinedness).
    Proof.
      apply single_element_definedness_impl_satisfies_definedness.
      exists (dom_custom m_def).
      simpl.
      split.
      {
        reflexivity.
      }
      {
        auto.
      }
    Qed.
    
  End test_2.
End test_2.

Module test_3.
  Section test_3.
    Import Definedness_Syntax.

    Inductive Symbols :=
    | sym_import_definedness (d : Definedness_Syntax.Symbols)
    | Zero | Succ (* constructors for Nats *)
    | TT | FF
    | even
    .

    Instance Symbols_eqdec : EqDecision Symbols.
    Proof. solve_decision. Defined.

    #[local]
    Program Instance Symbols_fin : Finite Symbols :=
    {|
      enum := [Zero; Succ; TT ; FF; even;
        sym_import_definedness Definedness_Syntax.definedness] ;
    |}.
    Next Obligation.
      repeat constructor; set_solver.
    Qed.
    Next Obligation.
      destruct x; try set_solver.
      destruct d; set_solver.
    Qed.

    Instance signature : Signature :=
      {| variables := StringMLVariables ;
         symbols := Symbols ;
      |}.

    Instance definedness_syntax : Definedness_Syntax.Syntax :=
      {|
         Definedness_Syntax.inj := sym_import_definedness;
      |}.

    Open Scope string_scope.
    Let X0 := patt_free_evar "X0".
    Let X := patt_free_evar "X".
    Let sym_even := patt_sym even.
    Let sym_succ := patt_sym Succ.
    Let sym_zero := patt_sym Zero.
    Let sym_tt := patt_sym TT.
    Let sym_ff := patt_sym FF.
    (* axioms *)
    Definition defined : Pattern := Definedness_Syntax.axiom AxDefinedness.
    Definition ruleA : Pattern :=
      X0 ∈ml sym_succ $ sym_succ $ X --->
        sym_even $ X0 =ml patt_sym even $ X.
    Definition ruleB : Pattern :=
       X0 ∈ml sym_succ $ sym_zero --->
        sym_even $ X0 =ml sym_ff.
    Definition ruleC : Pattern :=
      X0 ∈ml sym_zero --->
        sym_even $ X0 =ml sym_tt.

    Let Γₙₐₜ : Theory := {[ defined; ruleA; ruleB; ruleC ]}.
    Theorem def_theory : theory ⊆ Γₙₐₜ.
    Proof.
      unfold Γₙₐₜ, theory, named_axioms, NamedAxioms.theory_of_NamedAxioms; cbn.
      admit.
    Abort.

    Theorem example:
      Γₙₐₜ ⊢i sym_tt ∈ml sym_even $ sym_succ $ sym_succ $ sym_succ $ sym_succ $ sym_zero using AnyReasoning.
    Proof.
      assert (Γₙₐₜ ⊢i ruleA using AnyReasoning) as RA.
      { gapply hypothesis; auto. apply pile_any. set_solver. }
      assert (Γₙₐₜ ⊢i ruleC using AnyReasoning) as RC.
      { gapply hypothesis; auto. apply pile_any. set_solver. }
      apply universal_generalization with (x := "X") in RA as RA1. (* revert Meta *)
      2: apply pile_any. 2: auto.
      assert (Γₙₐₜ
       ⊢i all ,
           (X0 ∈ml sym_succ $ sym_succ $ b0 --->
            sym_even $ X0 =ml patt_sym even $ b0) using AnyReasoning) as RA1' by auto.
      clear RA1.
      assert (Γₙₐₜ ⊢i ex , (sym_succ $ sym_succ $ sym_zero =ml b0) using AnyReasoning) as S2WF.
      { admit. }
      assert (Γₙₐₜ ⊢i ex , (sym_succ $ sym_succ $ sym_succ $ sym_succ $ sym_zero =ml b0) using AnyReasoning) as S4WF.
      { admit. }
      mgSpecMeta RA1' with (sym_succ $ sym_succ $ sym_zero).
      repeat rewrite simpl_bevar_subst'  in RA1'; wf_auto2. 2: admit. (* apply def_theory. *)
      simpl in RA1'.
      apply universal_generalization with (x := "X0") in RA1' as RA2. (* revert Meta *)
      2: apply pile_any. 2: auto.
      assert (Γₙₐₜ
       ⊢i all ,
           (b0 ∈ml sym_succ $ sym_succ $ sym_succ $ sym_succ $ sym_zero --->
            sym_even $ b0 =ml patt_sym even $ sym_succ $ sym_succ $ sym_zero) using AnyReasoning) as RA2' by auto.
      clear RA2 RA1'.
      mgSpecMeta RA2' with (sym_succ $ sym_succ $ sym_succ $ sym_succ $ sym_zero).
      repeat rewrite simpl_bevar_subst'  in RA2'; wf_auto2. 2: admit. (* apply def_theory. *)
      simpl in RA2'.
      Search patt_exists ML_proof_system.
    Abort.
  End test_3.
End test_3.

