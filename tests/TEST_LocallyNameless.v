Require Import locally_nameless.
Require Import ML.Signature.
Require Import ML.DefaultVariables.
Require Import Coq.Logic.Classical_Prop.
Require Import Theories.Definedness.
Require Import Theories.Sorts.
Import MLNotations.

(* In this module we show how to define a signature and build patterns *)
Module test_1.
  (* We have three symbols *)
  Inductive Symbols := ctor| p | f .

  Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
  Proof.
    decide equality.
  Qed. (* We may need Defined here *)

  #[canonical]
  Let signature :=
    {| symbols := Symbols;
       sym_eq := Symbols_dec;
       variables := DefaultMLVariables;
    |}.

  (* Helpers. *)
  Definition sym (s : Symbols) : @Pattern signature :=
    @patt_sym signature s.
  Definition evar (sname : string) : @Pattern signature :=
    @patt_free_evar signature (find_fresh_evar_name (@evar_c sname) nil).
  Definition svar (sname : string) : @Pattern signature :=
    @patt_free_svar signature (find_fresh_svar_name (@svar_c sname) nil).

  (* Example patterns *)

  Definition more := svar ("A") or ¬ (svar ("A") ). (* A \/ ~A *)

  (* A -> (B -> ~C) (exists x. D (bot /\ top)) *)

  Definition complex :=
    evar ("A") --> (evar("B") --> ¬(svar("C"))) $
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
    Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
    Proof.
      decide equality.
      * decide equality.
      * decide equality.
    Qed.

    Let signature : Signature :=
      {| symbols := Symbols;
         sym_eq := Symbols_dec;
         variables := DefaultMLVariables;
      |}.

    #[local]
    Canonical Structure signature.

    Instance definedness_syntax : Definedness.Syntax :=
      {|
         Definedness.inj := sym_import_definedness;
      |}.

    Instance sorts_syntax : Sorts.Syntax :=
      {|
      Sorts.inj := sym_import_sorts;
      Sorts.imported_definedness := definedness_syntax;
      |}.
    
    (* The same helpers as in the previous case. Maybe we can abstract it somehow?*)
    (* But it does not make sense to have them visible globally - use 'Let' instead of 'Definition' *)
    Let sym (s : Symbols) : @Pattern signature :=
      @patt_sym signature s.
    Let evar (sname : string) : @Pattern signature :=
      @patt_free_evar signature (find_fresh_evar_name (@evar_c sname) nil).
    Let svar (sname : string) : @Pattern signature :=
      @patt_free_svar signature (find_fresh_svar_name (@svar_c sname) nil)
    .

    Example test_pattern_0 : Pattern := sym sym_c.
    Example test_pattern_1 := @patt_defined signature definedness_syntax (sym sym_c).
    Example test_pattern_2 := patt_defined (sym sym_c).
    Example test_pattern_3 : Pattern := patt_equal (sym sym_c) (sym sym_c).
    Example test_pattern_4 := patt_defined (patt_sym sym_c).
    Example test_pattern_5 := patt_equal (inhabitant_set (sym sym_SortNat)) (sym sym_zero).
    

    Inductive CustomElements :=
    | m_def (* interprets the definedness symbol *)
    | m_succ (* the successor function on nats *)
    | m_some_element (* just some element so that things do not get boring *)
    .

    Inductive domain : Type :=
    | dom_nat (n:nat)
    | dom_custom (c:CustomElements)
    .    
    
    Lemma domain_dec : forall (m1 m2 : domain), {m1 = m2} + {m1 <> m2}.
    Proof.
      decide equality.
      * decide equality.
      * decide equality.
    Qed.

    Definition my_sym_interp(s: Symbols) : Power domain :=
      match s with
      | sym_import_definedness s_def => Singleton domain (dom_custom m_def)
      | sym_zero => Singleton domain (dom_nat 0)
      | sym_succ => Singleton domain (dom_custom m_succ)
      | _ => Empty_set domain
      end.

    Definition my_app_interp(m1 m2 : domain) : Power domain :=
      match m1, m1 with
      | dom_custom m_def, _ => Full_set domain (* definedness *)
      | dom_custom m_succ, dom_nat n => Singleton domain (dom_nat (n+1))
      | _, _ => Empty_set domain
      end.
    
    Let M1 : @Model signature :=
      {| Domain := domain;
         nonempty_witness := dom_nat 0;
         Domain_eq_dec := domain_dec;
         (* for some reason, just using 'my_sym_interp' here results in a type error *)
         sym_interp := fun s : @symbols signature => my_sym_interp s;
         (* But this works. interesting. *)
         app_interp := my_app_interp;
      |}.

    Lemma M1_satisfies_definedness1 : satisfies_model M1 (Definedness.axiom Definedness.AxDefinedness).
    Proof.
      unfold satisfies_model. intros.
      unfold axiom.
      unfold sym.
      unfold patt_defined.
      rewrite -> ext_valuation_app_simpl.
      rewrite -> ext_valuation_sym_simpl.
      simpl.
      apply Same_set_symmetric. apply Same_set_Full_set.
      unfold Included. intros.
      clear H. (* useless *)
      intros.
      unfold In.
      unfold pointwise_ext.
      exists (dom_custom m_def).
      unfold evar.
      rewrite -> ext_valuation_free_evar_simpl.
      exists (evar_val (find_fresh_evar_name {| id_ev := "x" |} nil)).
      firstorder. (* some magic to get rid of the first two conjuncts *)
      simpl. constructor.
    Qed.
    
  End test_2.
End test_2.

Module LTL.
  Import Theories.Definedness.
  Import Theories.Sorts.

  Record LTLSignature :=
    { AP : Set;
      AP_dec : forall (a1 a2 : AP), {a1 = a2} + {a1 <> a2};
    }.
  
  
  Section LTL.
    (* We are parametrized with a set of atomic proposition. *)
    Context {ltlsig : LTLSignature}.

    Inductive Symbols :=
    | sym_import_definedness (d : Definedness.Symbols)
    | sym_import_sorts (s : Sorts.Symbols)
    | sym_SortInitialState
    | sym_SortState
    | sym_next
    | sym_prev
    | sym_a (ap : AP ltlsig)
    .

    Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
    Proof.
      decide equality.
      * decide equality.
      * decide equality.
      * apply (AP_dec ltlsig).
    Qed.

    
    Let signature : Signature :=
      {| symbols := Symbols;
         sym_eq := Symbols_dec;
         variables := DefaultMLVariables;
      |}.
    #[local]
     Canonical Structure signature.
    
    Inductive AxiomName :=
    | AxImportedDefinedness (* should import axioms from the Definedness module *)
    | AxPrev
    | AxInitialState (* Trace *)
    | AxState (* TraceSuffix *)
    | AxInf
    | AxNextOut
    | AxNextPFun
    | AxNextInj
    | AxAtomicProp (ap : AP ltlsig) (* defines a potentially infinite class of axioms *)
    .

    Definition axiom(name : AxiomName) : @Pattern signature :=
      match name with
      | _ => patt_bott
      end.


    Definition satisfies_axioms (M : Model) := forall (ax_name : AxiomName),    
        satisfies_model M (axiom ax_name).
    
    
  End LTL.

End LTL.

  
