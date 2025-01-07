From MatchingLogic Require Export ProofMode.MLPM
                                  FOEquality_ProofSystem
                                  Sorts_ProofSystem.
From MatchingLogic.Theories Require Export Nat_Syntax.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Sorts_Syntax.Notations.
Import MatchingLogic.Theories.Nat_Syntax.Notations.

Set Default Proof Mode "Classic".
Inductive Symbols := kore_next_symbol | kore_dv_symbol | kore_inj_symbol.

#[global]
Instance Symbols_eqdec: EqDecision Symbols.
Proof.
    solve_decision.
Defined.

#[global]
Program Instance Symbols_finite: Finite Symbols :=
{|
  enum := [
kore_next_symbol;kore_dv_symbol;kore_inj_symbol
]
|}.
Next Obligation.
    compute_done.
Qed.
Next Obligation.
    destruct x; compute_done.
Qed.

#[global]
Instance Symbols_countable : countable.Countable Symbols.
Proof. apply finite.finite_countable. Defined.

Section derived_operations.
  Context {Σ : Signature}.

  Class Syntax :=
    { sym_inj : Symbols -> symbols;
      imported_sorts : Sorts_Syntax.Syntax; (* TODO: this might change based on the formalisation of built-ins! *)
    }.

  #[global] Existing Instance imported_definedness.
  #[global] Existing Instance imported_sorts.

  Context {self : Syntax}.
  Definition kore_sym (s : Symbols) : Pattern := patt_sym (sym_inj s).

  Definition kore_exists (ph0: Pattern) (ph1: Pattern) (x: evar) (ph2: Pattern)  :=  ( patt_and ( patt_exists_of_sort x ph0 ph2 ) ( patt_inhabitant_set ph1 ) ).
  Definition kore_forall_sort (s0: evar) (ph0: Pattern)  :=  ( patt_forall_of_sort s0 ph0 ).
  Definition kore_valid (ph0: Pattern) (ph1: Pattern)  :=  ( eq ph1 ( kore_top ph0 ) ).
  Definition kore_bottom (ph0: Pattern)  :=  patt_bott.
  Definition kore_top (ph0: Pattern)  :=  ( patt_inhabitant_set ph0 ).
  Definition kore_not (ph0: Pattern) (ph1: Pattern)  :=  ( patt_and ( patt_not ph1 ) ( kore_top ph0 ) ).
  Definition kore_and (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( patt_and ph1 ph2 ).
  Definition kore_or (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( patt_or ph1 ph2 ).
  Definition kore_implies (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_or ph0 ( kore_not ph0 ph1 ) ph2 ).
  Definition kore_iff (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_and ph0 ( kore_implies ph0 ph1 ph2 ) ( kore_implies ph0 ph2 ph1 ) ).
  Definition kore_ceil (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( patt_and ( patt_defined ph2 ) ( kore_top ph1 ) ).
  Definition kore_floor (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_not ph1 ( kore_ceil ph0 ph1 ( kore_not ph0 ph2 ) ) ).
  Definition kore_equals (ph0: Pattern) (ph1: Pattern) (ph2: Pattern) (ph3: Pattern)  :=  ( kore_floor ph0 ph1 ( kore_iff ph0 ph2 ph3 ) ).
  Definition kore_in (ph0: Pattern) (ph1: Pattern) (ph2: Pattern) (ph3: Pattern)  :=  ( kore_floor ph0 ph1 ( kore_implies ph0 ph2 ph3 ) ).
  Definition kore_next (ph0: Pattern) (ph1: Pattern)  :=  ( patt_app (kore_sym kore_next_symbol) ph1 ).
  Definition kore_mu (ph0: Pattern) (X: svar) (ph1: Pattern)  :=  ( patt_and ( patt_mu X ph1 ) ( patt_inhabitant_set ph0 ) ).
  Definition kore_nu (ph0: Pattern) (X: svar) (ph1: Pattern)  :=  let ph2 := ph1 ( kore_not ph0 X ) X in ( kore_not ph0 ( kore_mu ph0 X ( kore_not ph0 ph2 ) ) ).
  Definition kore_all_path_next (ph0: Pattern) (ph1: Pattern)  :=  ( kore_not ph0 ( kore_next ph0 ( kore_not ph0 ph1 ) ) ).
  Definition kore_eventually (ph0: Pattern) (ph1: Pattern)  :=  ( kore_mu ph0 X ( kore_or ph0 ph1 ( kore_next ph0 X ) ) ).
  Definition kore_weak_eventually (ph0: Pattern) (ph1: Pattern)  :=  ( kore_not ph0 ( kore_mu ph0 X ( kore_not ph0 ( kore_or ph0 ph1 ( kore_next ph0 ( kore_not ph0 X ) ) ) ) ) ).
  Definition kore_always (ph0: Pattern) (ph1: Pattern)  :=  ( kore_not ph0 ( kore_mu ph0 X ( kore_not ph0 ( kore_and ph0 ph1 ( kore_all_path_next ph0 ( kore_not ph0 X ) ) ) ) ) ).
  Definition kore_well_founded (ph0: Pattern)  :=  ( kore_mu ph0 X ( kore_all_path_next ph0 X ) ).
  Definition kore_well_founded_alt (ph0: Pattern)  :=  ( kore_mu ph0 X ( kore_all_path_next ph0 ( kore_always ph0 X ) ) ).
  Definition kore_rewrites (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_implies ph0 ph1 ( kore_next ph0 ph2 ) ).
  Definition kore_rewrites_star (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_implies ph0 ph1 ( kore_eventually ph0 ph2 ) ).
  Definition kore_rewrites_plus (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_implies ph0 ph1 ( kore_next ph0 ( kore_eventually ph0 ph2 ) ) ).
  Definition kore_one_path_reaches_star (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_implies ph0 ph1 ( kore_weak_eventually ph0 ph2 ) ).
  Definition kore_one_path_reaches_plus (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_implies ph0 ph1 ( kore_next ph0 ( kore_weak_eventually ph0 ph2 ) ) ).
  Definition kore_circularity (ph0: Pattern) (ph1: Pattern)  :=  ( kore_all_path_next ph0 ( kore_always ph0 ph1 ) ).
  Definition kore_non_terminating (ph0: Pattern)  :=  ( kore_next ph0 ( kore_top ph0 ) ).
  Definition kore_all_path_next_nt (ph0: Pattern) (ph1: Pattern)  :=  ( kore_and ph0 ( kore_all_path_next ph0 ph1 ) ( kore_non_terminating ph0 ) ).
  Definition kore_all_path_eventually (ph0: Pattern) (ph1: Pattern)  :=  ( kore_mu ph0 X ( kore_or ph0 ph1 ( kore_all_path_next_nt ph0 X ) ) ).
  Definition kore_all_path_rewrites (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_implies ph0 ph1 ( kore_all_path_next_nt ph0 ph2 ) ).
  Definition kore_all_path_rewrites_star (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_implies ph0 ph1 ( kore_all_path_eventually ph0 ph2 ) ).
  Definition kore_all_path_rewrites_plus (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( kore_implies ph0 ph1 ( kore_all_path_next_nt ph0 ( kore_all_path_eventually ph0 ph2 ) ) ).
  Definition kore_dv (ph0: Pattern) (ph1: Pattern)  :=  ( patt_app ( patt_app (kore_sym kore_dv_symbol) ph0 ) ph1 ).
  Definition kore_is_sort (ph0: Pattern)  :=  ( exists_sort s0 ( eq s0 ph0 ) ).
  Definition kore_forall (ph0: Pattern) (ph1: Pattern) (x: evar) (ph2: Pattern)  :=  ( kore_not ph1 ( kore_exists ph0 ph1 x ( kore_not ph1 ph2 ) ) ).
  Definition kore_inj (ph0: Pattern) (ph1: Pattern) (ph2: Pattern)  :=  ( patt_app ( patt_app ( patt_app (kore_sym kore_inj_symbol) ph0 ) ph1 ) ph2 ).
  Definition kore_is_predicate (ph0: Pattern) (ph1: Pattern)  :=  ( patt_or ( kore_valid ph0 ph1 ) ( is_bot ph1 ) ).
  Definition kore_is_nonempty_sort (ph0: Pattern)  :=  ( patt_defined ( patt_inhabitant_set ph0 ) ).