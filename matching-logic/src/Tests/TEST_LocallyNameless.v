From Coq Require Import String Ensembles.
Require Import Coq.Logic.Classical_Prop.

From stdpp Require Import base fin_sets sets propset.

From MatchingLogic Require Import Syntax Semantics SignatureHelper.
From MatchingLogic.Theories Require Import Definedness Sorts.
From MatchingLogic.Utils Require Import stdpp_ext.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.DerivedOperators.Notations.

(* In this module we show how to define a signature and build patterns *)
Module test_1.
  (* We have three symbols *)
  Inductive Symbols := ctor| p | f .


  Instance Symbols_eqdec : EqDecision Symbols.
  Proof.
    intros s1 s2. unfold Decision. decide equality.
  Defined.

  Instance Symbols_h : SymbolsH Symbols := Build_SymbolsH Symbols Symbols_eqdec.
  
  Instance signature : Signature := @SignatureFromSymbols Symbols _.
    
  (* Example patterns *)
  
  Definition a_symbol : Pattern := sym ctor.
  
  Definition more : Pattern := svar ("A") or ¬ (svar ("A") ). (* A \/ ~A *)

  Example e1 X: evar_open 0 X more = more.
  Proof. unfold more. autorewrite with ml_db. reflexivity. Qed.

  (* A -> (B -> ~C) (exists x. D (bot /\ top)) *)

  Definition complex :=
    evar ("A") ---> (evar("B") ---> ¬(svar("C"))) $
         ex , svar ("D") $ Bot and Top.

  Definition custom_constructor := sym ctor.

  (* p x1 x2 *)
  Definition predicate := sym (ctor) $ evar ("x1") $ evar ("x2").
  (* f x (mu y . y) *)

  Definition function :=
    sym (f) $ (evar ("x")) $ (mu , (patt_bound_svar 0)).

  (* forall x, x /\ y *)
  Definition free_and_bound :=
    all , (patt_bound_evar 0) and evar ("y").
  (* End of examples. *)

End test_1.


(* Here we show how to use the Definedness module. *)
Module test_2.
  Section test_2.
    Import Definedness.

    (* We must include all the symbols from the Definedness module into our signature.
       We do this by defining a constructor `sym_import_definedness : Definedness.Symbols -> Symbols`.
       And we also define a bunch of other symbols.
     *)
    Inductive Symbols :=
    | sym_import_definedness (d : Definedness.Symbols)
    | sym_import_sorts (s : Sorts.Symbols)
    | sym_SortNat
    | sym_zero | sym_succ (* constructors for Nats *)
    | sym_c (* some constant that we make functional *)
    .

    (* If symbols are created as a sum type of various sets, we may want to have a tactic that does
       'decide equality' recursively.
     *)
    Lemma Symbols_eqdec : EqDecision Symbols.
    Proof.
      intros x y. unfold Decision.
      decide equality.
      * decide equality.
      * decide equality.
    Qed.

    Instance symbols_H : SymbolsH Symbols := {| SHSymbols_eqdec := Symbols_eqdec; |}.
    Instance signature : Signature := @SignatureFromSymbols Symbols symbols_H.
    (* https://stackoverflow.com/a/44769124/6209703 *)
    (*Hint Extern 4 => unfold signature : core.*)
    

    Instance definedness_syntax : Definedness.Syntax :=
      {|
         Definedness.inj := sym_import_definedness;
      |}.

    Instance sorts_syntax : Sorts.Syntax :=
      {|
      Sorts.inj := sym_import_sorts;
      Sorts.imported_definedness := definedness_syntax;
      |}.
    
    Example test_pattern_0 : Pattern := sym sym_c.
    Example test_pattern_1 := @patt_defined signature definedness_syntax (sym sym_c).
    Example test_pattern_2 := patt_defined (sym sym_c).
    Example test_pattern_3 s : Pattern := patt_equal (sym s) (sym s).
    Example test_pattern_4 := patt_defined (patt_sym sym_c).
    Example test_pattern_5 := patt_equal (patt_inhabitant_set (sym sym_SortNat)) (sym sym_zero).

    Example test_pattern_3_open s x : evar_open 0 x (test_pattern_3 s) = (test_pattern_3 s).
    Proof. unfold test_pattern_3. autorewrite with ml_db. reflexivity. Qed.

    Inductive CustomElements :=
    | m_def (* interprets the definedness symbol *)
    | m_succ (* the successor function on nats *)
    | m_some_element (* just some element so that things do not get boring *)
    .

    Inductive domain : Type :=
    | dom_nat (n:nat)
    | dom_custom (c:CustomElements)
    .    
    
    Instance domain_dec : EqDecision domain.
    Proof.
      unfold EqDecision. intros. unfold Decision.
      decide equality.
      * decide equality.
      * decide equality.
    Qed.

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
         nonempty_witness := dom_nat 0;
         Domain_eq_dec := domain_dec;
         (* for some reason, just using 'my_sym_interp' here results in a type error *)
         sym_interp := fun s : symbols => my_sym_interp s;
         (* But this works. interesting. *)
         app_interp := my_app_interp;
      |}.

    (* FIXME: Otherwise, when I do [simpl], Coq replaces [Domain M1] with [domain]
       and that breaks typeclass search; namely, simple apply propset_leibniz_equiv.
     *)
    Arguments Domain : simpl never.
    Existing Instance  propset_leibniz_equiv.
    (* TODO a tactic that solves this, or a parameterized lemma. *)
    Lemma M1_satisfies_definedness1 : satisfies_model M1 (Definedness.axiom Definedness.AxDefinedness).
    Proof.
      unfold satisfies_model. intros.
      unfold axiom.
      unfold sym.
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


  
