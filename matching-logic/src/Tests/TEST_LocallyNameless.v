From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import String Ensembles.
Require Import Coq.Logic.Classical_Prop.

From stdpp Require Import base fin_sets sets propset.

From MatchingLogic Require Import Syntax Semantics DerivedOperators_Syntax DerivedOperators_Semantics SignatureHelper.
From MatchingLogic.Theories Require Import Definedness_Syntax Definedness_Semantics Sorts_Syntax Sorts_Semantics.
From MatchingLogic.Utils Require Import stdpp_ext.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.DerivedOperators_Syntax.Notations.
Import MatchingLogic.IndexManipulation.

(* In this module we show how to define a signature and build patterns *)
Module test_1.
  (* We have three symbols *)
  Inductive Symbols := ctor| p | f .


  Instance Symbols_eqdec : EqDecision Symbols.
  Proof. solve_decision. Defined.

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
    
    Inductive domain : Type :=
    | dom_nat (n:nat)
    | dom_custom (c:CustomElements)
    .    

    Instance domain_inhabited : Inhabited domain := populate (dom_nat 0).
    
    Instance domain_eqdec : EqDecision domain.
    Proof. solve_decision. Defined.

    Definition my_sym_interp(s: Symbols) : Power domain :=
      match s with
      | sym_import_definedness s_def => {[ (dom_custom m_def) ]}
      | sym_zero => {[ (dom_nat 0) ]}
      | sym_succ => {[ (dom_custom m_succ) ]}
      | _ => ∅
      end.

    Definition my_app_interp(m1 m2 : domain) : Power domain :=
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
    Lemma M1_satisfies_definedness1 : satisfies_model M1 (Definedness_Syntax.axiom Definedness_Syntax.AxDefinedness).
    Proof.
      unfold satisfies_model. intros.
      unfold axiom.
      unfold patt_defined.
      rewrite -> pattern_interpretation_app_simpl.
      rewrite -> pattern_interpretation_sym_simpl.
      simpl.
      rewrite -> set_eq_subseteq.
      split.
      { apply top_subseteq. }
      rewrite -> elem_of_subseteq.
      intros x _.
      unfold app_ext.
      exists (dom_custom m_def).
      unfold p_x.
      rewrite -> pattern_interpretation_free_evar_simpl.
      eexists. firstorder.
    Qed.
    
  End test_2.
End test_2.
