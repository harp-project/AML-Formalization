From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Setoid.
From Coq Require Import Unicode.Utf8.
From Coq.Logic Require Import Classical_Prop FunctionalExtensionality.
From Coq.Classes Require Import Morphisms_Prop.

From stdpp Require Import base sets vector.

From MatchingLogic Require Import Logic.
Import MatchingLogic.Logic.Notations.
Require Import MatchingLogic.Theories.Sorts_Syntax.

Import MatchingLogic.Theories.Definedness_Syntax.Notations
       MatchingLogic.Theories.Sorts_Syntax.Notations.
Import BoundVarSugar.

Inductive Symbols := sym_Sort.

Section MSA_syntax.
  Open Scope ml_scope.
  Context {Σ : Signature}
          {Sorts : Set}
          {Funs : Set}
          {arity : Funs -> list Sorts * Sorts}.

  Class Syntax :=
    { inj_sorts : Sorts -> symbols;
      inj_funs : Funs -> symbols;
      inj_sort_sym : Symbols -> symbols;
      imported_definedness : Definedness_Syntax.Syntax;
      imported_inhabitant : Sorts_Syntax.Syntax;
    }.

  #[global] Existing Instance imported_definedness.
  #[global] Existing Instance imported_inhabitant.

  Context {self : Syntax}.

  (* Definition patt_app_nary (f : Funs) (ps : vec Pattern (length (fst (arity f)))) :=
    foldl patt_app (patt_sym (inj_funs f)) ps.

  Notation "f '$[' p1 ; p2 ; .. ; pn ']$'" := (patt_app_nary f (vcons p1 (vcons p2 .. (vcons pn vnil) .. ))) (at level 30). *)

  Definition patt_app_nary (f : Funs) (ps : list Pattern) :=
    foldl patt_app (patt_sym (inj_funs f)) ps.

  Notation "f '$[' p1 ; p2 ; .. ; pn ']$'" := (patt_app_nary f (cons p1 (cons p2 .. (cons pn nil) .. ))) (at level 30).
  Definition well_formed_nary (f : Funs) (ps : list Pattern) :=
    length ps = length (fst (arity f)).
  (*
  test:
  Local Axiom f : Funs.

  Check f $[ patt_bott ; patt_bott ]$ . *)

  Inductive AxiomName :=
  | Sort (s : Sorts)
  | NonEmpty (s : Sorts)
  | Function (f : Funs).

  (* TODO: This part should go to Sorts_Syntax.v *)
  Definition patt_sorted (p : Pattern) s := (ex s, p =ml b0).

  (* END TODO *)

  Definition names_from {A : Set} (l : list A) : list Pattern :=
    imap (fun n _ => patt_bound_evar n) l.

  Definition axiom (name : AxiomName) : Pattern :=
    match name with
    | Sort s     =>
      patt_sorted (patt_sym (inj_sorts s)) (patt_sym (inj_sort_sym sym_Sort))
    | NonEmpty s =>
      patt_not (〚patt_sym (inj_sorts s)〛 =ml patt_bott)
    | Function f =>
      let (sorts, sort) := arity f in
        let base := patt_sorted (patt_app_nary f (names_from sorts)) (patt_sym (inj_sorts sort)) in
          foldr (fun s acc => all patt_sym (inj_sorts s), acc) base sorts
    end.

  Program Definition named_axioms : NamedAxioms :=
    {| NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; wf_auto2.
    1-3: destruct (arity f); remember (patt_sym (inj_sorts s)) as base.
    1-3: assert (well_formed (patt_sym (inj_sorts s))) by wf_auto2; clear Heqbase.
    {
      revert base.
      induction l; intros.
      * wf_auto2. admit.
      * cbn in *. rewrite IHl.
    }
  Admitted.

  Definition theory := theory_of_NamedAxioms named_axioms.

End MSA_syntax.

