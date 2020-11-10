Require Import locally_nameless.
Require Import ML.Signature.
Require Import ML.DefaultVariables.
Import MLNotations.

(* In this module we show how to define a signature and build patterns *)
Module test_1.
  (* We have three symbols *)
  Inductive Symbols := ctor| p | f .

  Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
  Proof.
    decide equality.
  Qed.

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

(* In this module we define the definedness symbol and use it to build derived notions
   like totality and equality. The definitions are reusable from other modules,
   as is demonstrated in the module `test_Definedness` (TODO).
   TODO: include the axiom for definedness and prove some theorems about it.
 *)
Module Definedness.
  Import ML.Signature.

  (* We have only one symbol *)
  Inductive Symbols := definedness.

  Record Syntax :=
    { sig: Signature;
      (* 'Symbols' are a 'subset' of all the symbols from the signature *)
      inj: Symbols -> symbols sig;
      (* for convenience *)
    }.  
  
  Section syntax.
    Context {self : Syntax}.

    Let Pattern : Type := @locally_nameless.Pattern (sig self).

    Definition patt_defined (phi : Pattern) : Pattern :=
      patt_sym (inj self definedness) $ phi.
    
    Definition patt_total (phi: Pattern) : Pattern :=
      patt_not (patt_defined (patt_not phi)).

    Definition patt_equal (phi1 phi2 : Pattern) : Pattern :=
      patt_total (phi1 <--> phi2).

    Let sym (s : Symbols) : Pattern :=
      @patt_sym (sig self) (inj self s).
    
    Let evar (name : string) : Pattern :=
      @patt_free_evar (sig self) (nevar (variables (sig self)) name).

    Definition definedness_axiom := patt_defined (evar "x").

    (* I know this section is about syntax, but maybe we can merge the two sections *)

    Lemma definedness_model_application :
      forall (M : @Model (sig self)) (evar_val : @EVarVal (sig self) M) (svar_val : @SVarVal (sig self) M),
        satisfies_model M definedness_axiom ->
        forall (m: Domain M),
          Same_set (Domain M)
                   (Full_set (Domain M))
                   (pointwise_ext (ext_valuation evar_val svar_val (sym definedness)) (Singleton (Domain M) m)).
    Proof.
      intros.
      unfold pointwise_ext.
      apply Same_set_Full_set.
      unfold Included. unfold In. intros. clear H0.

      unfold satisfies_model in H. unfold definedness_axiom in H.
      remember (update_evar_val (nevar (variables (sig self)) "x") m evar_val) as evar_val'.
      specialize (H evar_val' svar_val).
      unfold Same_set in H. destruct H as [_ H].
      unfold Included in H.
      specialize (H x).
      pose proof (H' := Full_intro (Domain M) x).
      specialize (H H'). clear H'.
      unfold patt_defined in H.
      rewrite -> ext_valuation_app_simpl in H.
      rewrite -> ext_valuation_sym_simpl in H.
      unfold sym.
      unfold evar in H.
      rewrite -> ext_valuation_free_evar_simpl in H.
      rewrite -> Heqevar_val' in H.
      unfold update_evar_val in H. simpl in H.
      unfold locally_nameless.eq_evar_name in H.
      destruct (evar_eq (variables (sig self)) (nevar (variables (sig self)) "x") (nevar (variables (sig self)) "x") ).
      2: { contradiction. }
      unfold pointwise_ext in H. unfold In in H.
      destruct H as [m1 [m2 Hm1m2]].
      destruct Hm1m2. destruct H0.
      inversion H0. clear H0. subst.
      exists m1. exists m2. split. 2: { split. 2: { apply H1. } constructor. }
      rewrite -> ext_valuation_sym_simpl. apply H.
    Qed.
    


    Lemma definedness_not_empty : forall (M : @Model (sig self)),
        satisfies_model M definedness_axiom ->
        forall (phi : Pattern) (evar_val : @EVarVal (sig self) M) (svar_val : @SVarVal (sig self) M),
          ~ Same_set (Domain M)
            (@ext_valuation (sig self) M evar_val svar_val phi)
            (Empty_set (Domain M)) ->
          Same_set (Domain M)
                   (@ext_valuation (sig self) M evar_val svar_val (patt_defined phi))
                   (Full_set (Domain M)).
    Proof.
      intros.
      pose (H' := Not_Empty_Contains_Elements (ext_valuation evar_val svar_val phi) H0).
      destruct H'.
      unfold patt_defined.
      rewrite -> ext_valuation_app_simpl.
      
      pose proof (H'' := definedness_model_application M evar_val svar_val H x).
      unfold sym in H''.
      apply Same_set_symmetric.
      apply Same_set_Full_set.
      unfold Same_set in H''.
      destruct H'' as [H'' _].
      assert (Hincl: Included (Domain M) (Singleton (Domain M) x) (ext_valuation evar_val svar_val phi) ).
      { unfold Included. intros. unfold In in *. inversion H2. subst. assumption.  }
      
      pose proof (Hincl' := pointwise_ext_monotonic_r
                              M
                              (ext_valuation evar_val svar_val (patt_sym (inj self definedness)))
                              (Singleton (Domain M) x)
                              (ext_valuation evar_val svar_val phi)
                              Hincl
                 ).
      apply Included_transitive with (S2 := pointwise_ext (ext_valuation evar_val svar_val (patt_sym (inj self definedness))) (Singleton (Domain M) x)). assumption. assumption.

    Qed.


    Lemma totality_not_full : forall (M : @Model (sig self)),
        satisfies_model M definedness_axiom ->
        forall (phi : Pattern) (evar_val : @EVarVal (sig self) M) (svar_val : @SVarVal (sig self) M),
          ~ Same_set (Domain M)
            (@ext_valuation (sig self) M evar_val svar_val phi)
            (Full_set (Domain M)) ->
          Same_set (Domain M)
                   (@ext_valuation (sig self) M evar_val svar_val (patt_total phi))
                   (Empty_set (Domain M)).
    Proof.
      intros.
      assert (Hnonempty : ~ Same_set (Domain M) (ext_valuation evar_val svar_val (patt_not phi)) (Empty_set (Domain M))).
      { unfold not. unfold not in H0. intros. rewrite -> ext_valuation_not_simpl in H1.
        (* TODO extract these three (or two?) steps into a separate lemmma: swap_compl *)
        apply Same_set_Compl in H1.
        rewrite -> (Same_set_to_eq (Compl_Compl_Ensembles (Domain M) (ext_valuation evar_val svar_val phi))) in H1.
        rewrite -> (Same_set_to_eq (@Complement_Empty_is_Full (Domain M) )) in H1.
        apply H0. apply H1.
      }
      unfold patt_total. rewrite -> ext_valuation_not_simpl.
      apply Same_set_Compl.
      rewrite -> (Same_set_to_eq (Compl_Compl_Ensembles (Domain M) (ext_valuation evar_val svar_val
                                                                                  (patt_defined (patt_not phi))))).
      rewrite -> (Same_set_to_eq (@Complement_Empty_is_Full (Domain M))).
      apply definedness_not_empty. apply H. apply Hnonempty.
    Qed.
  End syntax.

  
  Section semantics.
    (* TODO lemmas *)

  End semantics.
  
End Definedness.


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
    Qed.

    Let signature : Signature :=
      {| symbols := Symbols;
         sym_eq := Symbols_dec;
         variables := DefaultMLVariables;
      |}.

    Let definedness_syntax : Definedness.Syntax :=
      {| sig := signature;
         inj := sym_import_definedness;
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


    (* This works *)
    Definition test_pattern_1 := @patt_defined definedness_syntax (sym sym_c).

    (* This fails *)
    Fail Definition test_pattern_2 := patt_defined (sym sym_c).
    (* But with this magic it works *)
    Local Canonical Structure definedness_syntax.
    Definition test_pattern_2 := patt_defined (sym sym_c).
    Definition test_pattern_3 : Pattern := patt_equal (sym sym_c) (sym sym_c).

    (* But this still fails *)
    Fail Definition test_pattern_4 := patt_defined (patt_sym sym_c).
    (* We need another canonical structure *)
    #[local]
     Canonical Structure signature.
    Definition test_pattern_4 := patt_defined (patt_sym sym_c).
    

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

    
    Definition definedness_axiom_1 := patt_defined (evar "x").

    Lemma M1_satisfies_definedness1 : satisfies_model M1 definedness_axiom_1.
    Proof.
      unfold satisfies_model. intros.
      unfold definedness_axiom_1.
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
