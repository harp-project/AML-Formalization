From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Unicode.Utf8.
Require Import Coq.Logic.Classical_Prop.

From MatchingLogic Require Import Syntax Semantics.
Require Import MatchingLogic.Theories.Definedness.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Syntax.BoundVarSugar.
Import MatchingLogic.Semantics.Notations.

Section sorts.

  Inductive Symbols := inhabitant.

  Context {sig : Signature}.

  Class Syntax :=
    { inj: Symbols -> symbols;
      imported_definedness: @Definedness.Syntax sig;
    }.

  Context {self : Syntax}.

  Existing Instance imported_definedness.

  Local Definition sym (s : Symbols) : @Pattern sig :=
    @patt_sym sig (inj s).
  
  Example test_pattern_1 := patt_equal (sym inhabitant) (sym inhabitant).
  Definition inhabitant_set(phi : Pattern) : Pattern := sym inhabitant $ phi.

  Definition patt_forall_of_sort (sort phi : Pattern) : Pattern :=
    patt_forall ((patt_in (patt_bound_evar 0) (inhabitant_set sort)) ---> phi).

  Definition patt_exists_of_sort (sort phi : Pattern) : Pattern :=
    patt_exists ((patt_in (patt_bound_evar 0) (inhabitant_set sort)) and phi).

  (* TODO patt_forall_of_sort and patt_exists_of_sorts are duals - a lemma *)

  (* TODO a lemma about patt_forall_of_sort *)
  
  Definition patt_total_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort to (patt_equal (patt_app phi b1) b0)).

  Definition patt_partial_function(phi from to : Pattern) : Pattern :=
    patt_forall_of_sort from (patt_exists_of_sort to (patt_subseteq (patt_app phi b1) b0)).

  Section with_model.
    Context {M : Model}.
    Hypothesis M_satisfies_theory : M ⊨ᵀ Definedness.theory.

    Definition Minhabitant_set m := app_ext (sym_interp (inj inhabitant)) (Ensembles.Singleton (Domain M) m).

    (* ϕ is expected to be a sort pattern *)
    Definition Minterp_inhabitant ϕ ρₑ ρₛ := @pattern_interpretation sig M ρₑ ρₛ (patt_app (sym inhabitant) ϕ).

    (*Search pattern_interpretation patt_forall.*)
    
    Lemma interp_total_function f s₁ s₂ ρₑ ρₛ :
      @pattern_interpretation sig M ρₑ ρₛ (patt_total_function f s₁ s₂) = Full ->
      ∀ (m₁ : Domain M),
        Minterp_inhabitant s₁ ρₑ ρₛ m₁ ->                 
        ∃ (m₂ : Domain M),
          Minterp_inhabitant s₂ ρₑ ρₛ m₂ ->
          app_ext (@pattern_interpretation sig M ρₑ ρₛ f) (Ensembles.Singleton (Domain M) m₁)
          = Ensembles.Singleton (Domain M) m₂.
    Proof.
      intros Hfun m₁ H1.
      unfold patt_total_function in Hfun.
    Abort.

  End with_model.
    
End sorts.
