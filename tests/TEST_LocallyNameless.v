Require Import locally_nameless.
Require Import ML.Signature.
Require Import ML.DefaultVariables.
Import MLNotations.


Section test_1.
Inductive Symbols : Type :=
| ctor
| p
| f
.

Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Qed.

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


Print patt_forall.
(* forall x, x /\ y *)
Definition free_and_bound :=
  all , (patt_bound_evar 0) and evar ("y").
(* End of examples. *)

End test_1.

Module test_2.
  Section test_2.

    Inductive DefinednessSymbols : Set := s_def.
    
    Inductive Symbols :=
    | sym_import_definedness (d : DefinednessSymbols)
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

    Let signature :=
      {| symbols := Symbols;
         sym_eq := Symbols_dec;
         variables := DefaultMLVariables;
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


    Definition definedness_axiom_1 := (sym (sym_import_definedness s_def)) $ (evar "x").

    Lemma M1_satisfies_definedness1 : satisfies_model M1 definedness_axiom_1.
    Proof.
      unfold satisfies_model. intros.
      unfold definedness_axiom_1.
      unfold sym.
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

    (* Maybe we can have a section parametrized with a signature,
       and with a symbol, and with a model and a proof that the model satisfies
       a definedness-like axiom (or theorem) with the given symbol,
       and inside the section would be a bunch of lemmas regarding the definedness.
       Or we can put all the assumptions to a record (or typeclass?).
       Or we can make the assumptions 'model-free' and talk about a consequence of a theory?
     *)

    Lemma definedness_correct : forall (M : @Model signature),
        satisfies_model M definedness_axiom_1 ->
        forall (phi : @Pattern signature) (evar_val : @EVarVal signature M) (svar_val : @SVarVal signature M),
          True.
      Proof. Admitted.
          
    
  End test_2.
End test_2.
