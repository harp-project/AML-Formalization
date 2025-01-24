From MatchingLogic Require Export ProofMode.MLPM
                                  FOEquality_ProofSystem
                                  Sorts_ProofSystem.
From MatchingLogic.Theories Require Export Nat_Syntax.

Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Theories.Definedness_Syntax.Notations.
Import MatchingLogic.Theories.Sorts_Syntax.Notations.
Import MatchingLogic.Theories.Nat_Syntax.Notations.

Set Default Proof Mode "Classic".

(* For the well-formedness tactics, we forbid simplifications *)
Arguments well_formed_positive : simpl never.
Arguments well_formed_closed_mu_aux : simpl never.
Arguments well_formed_closed_ex_aux : simpl never.

Inductive Symbols := kore_next_symbol | kore_dv_symbol | kore_inj_symbol.

#[global]
Instance Symbols_eqdec: EqDecision Symbols.
Proof.
    solve_decision.
Defined.

#[global]
Program Instance Symbols_finite: Finite Symbols :=
{|
  enum := [kore_next_symbol;kore_dv_symbol;kore_inj_symbol]
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

  (* TODO: check if s is needed! *)
  Definition kore_bottom (s : Pattern) := patt_bott.
  #[global]
  Program Instance kore_bottom_Nullary s : Nullary (kore_bottom s).
  Next Obligation.
    intros. rewrite pm_correctness. simpl. reflexivity.
  Defined.
  Solve Obligations of kore_bottom_Nullary with intros;wf_auto2.
  Fail Next Obligation.

  Definition kore_top (s : Pattern) := patt_inhabitant_set s.
  #[global]
  Program Instance kore_top_Unary : Unary kore_top.
  Next Obligation.
    intros. rewrite pm_correctness. simpl.
    rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_top_Unary with intros;wf_auto2.
  Fail Next Obligation.

  Definition kore_cast (s p : Pattern) :=
    patt_and p (kore_top s).
  #[global]
  Program Instance kore_cast_Binary : Binary kore_cast.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_cast_Binary with intros; unfold kore_cast; wf_auto2.
  Fail Next Obligation.

  Definition kore_valid (s : Pattern) (ph1 : Pattern) :=
    patt_equal ph1 (kore_top s).
  #[global]
  Program Instance kore_top_Binary : Binary kore_valid.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_top_Binary with intros; unfold kore_valid; wf_auto2.
  Fail Next Obligation.

  Definition kore_not (s : Pattern) (ph1 : Pattern) :=
    kore_cast s (patt_not ph1).
  #[global]
  Program Instance kore_not_Binary : Binary kore_not.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_not_Binary with intros; unfold kore_not; wf_auto2.
  Fail Next Obligation.

  (* NOTE: this is changed wrt MM *)
  Definition kore_and (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_cast s (patt_and ph1 ph2).
  #[global]
  Program Instance kore_and_Ternary : Ternary kore_and.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_and_Ternary with intros; unfold kore_and; wf_auto2.
  Fail Next Obligation.

  Local Goal forall φ1 s, well_formed φ1 -> well_formed s -> well_formed (kore_and s φ1 ⊥).
  Proof.
    intros. wf_auto2.
  Qed.

  (* NOTE: this is changed wrt MM *)
  Definition kore_or (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_cast s (patt_or ph1 ph2).
  #[global]
  Program Instance kore_or_Ternary : Ternary kore_or.
  Next Obligation.
    intros. rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_or_Ternary with intros; unfold kore_or; wf_auto2.
  Fail Next Obligation.

  Local Goal forall φ1 s, well_formed φ1 -> well_formed s -> well_formed (kore_or s φ1 ⊥).
  Proof.
    intros. wf_auto2.
  Qed.


  Definition kore_implies (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_or s (kore_not s ph1) ph2.
  #[global]
  Program Instance kore_implies_Ternary : Ternary kore_implies.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_implies_Ternary with intros; unfold kore_implies; wf_auto2.
  Fail Next Obligation.

  Local Goal forall φ1, well_formed φ1 -> well_formed (kore_implies (p_x) φ1 ⊥).
  Proof.
    intros. wf_auto2.
  Qed.

  Definition kore_iff (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_and s (kore_implies s ph1 ph2) (kore_implies s ph2 ph1).
  #[global]
  Program Instance kore_iff_Ternary : Ternary kore_iff.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_iff_Ternary with intros; unfold kore_iff; wf_auto2.
  Fail Next Obligation.

  Local Goal forall φ1, well_formed φ1 -> well_formed (kore_iff (p_x) φ1 ⊥).
  Proof.
    intros. wf_auto2.
  Qed.

  (* TODO: check if s1 is needed!
     TODO: this seems to be wrong. s1 is not used for ph2!
  *)
  Definition kore_ceil (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) := 
    kore_cast s2 (patt_defined (kore_cast s1 ph2)).
  #[global]
  Program Instance kore_ceil_Ternary : Ternary kore_ceil.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_ceil_Ternary with intros; unfold kore_ceil; wf_auto2.
  Fail Next Obligation.
  Local Goal forall s1 s2 φ1, well_formed φ1 -> well_formed s1 -> well_formed s2 -> well_formed (kore_ceil s1 s2 φ1).
  Proof.
    intros. wf_auto2.
  Qed.


  Definition kore_floor (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) := 
    kore_not s2 (kore_ceil s1 s2 (kore_not s1 ph2)).
  #[global]
  Program Instance kore_floor_Ternary : Ternary kore_floor.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_floor_Ternary with intros; unfold kore_floor; wf_auto2.
  Fail Next Obligation.

  Local Goal forall s2 φ1, well_formed φ1 -> well_formed s2 -> well_formed (kore_floor ⊥ s2 φ1).
  Proof.
    intros. wf_auto2.
  Qed.

  Definition kore_equals (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) (ph3: Pattern) := 
    kore_floor s1 s2 (kore_iff s1 ph2 ph3).
  #[global]
  Program Instance kore_equals_Quaternary : Quaternary kore_equals.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_equals_Quaternary with intros; unfold kore_equals; wf_auto2.
  Fail Next Obligation.

  Local Goal forall s2 φ1 φ2,
    well_formed φ1 ->
    well_formed s2 ->
    well_formed φ2 -> well_formed (kore_equals s2 Top φ1 φ2).
  Proof.
    intros. wf_auto2.
  Qed.

  (* Q: why not kore_ceil and conjunction? *)
  (* A: because this is not kore-in, but rather kore-subseteq *)
  Definition kore_in (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) (ph3: Pattern) := 
    kore_floor s1 s2 (kore_implies s1 ph2 ph3).
  #[global]
  Program Instance kore_in_Quaternary : Quaternary kore_in.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_in_Quaternary with intros; unfold kore_in; wf_auto2.
  Fail Next Obligation.

  Local Goal forall s2 φ1 φ2,
    well_formed φ1 ->
    well_formed s2 ->
    well_formed φ2 -> well_formed (kore_in s2 Top φ1 φ2).
  Proof.
    intros. wf_auto2.
  Qed.

  (*
    TODO:
    the following constructs do not match into the
    class scheme described in SyntacticConstruct.v!
  *)

  Definition kore_exists (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) :=
    kore_cast s2 (patt_sorted_exists s1 ph2).
  Definition kore_forall (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) :=
    kore_not s2 (kore_exists s1 s2 (kore_not s2 ph2)).
(*   Definition kore_forall_sort (s : Pattern) :=
    patt_forall_sort s. *)
  Definition kore_is_sort (s : Pattern) := patt_exists_sort (patt_equal b0 (nest_ex s)).
  (* #[global]
  Program Instance kore_is_sort_Unary : Unary kore_is_sort.
  Next Obligation.
    intros. unfold kore_is_sort.
    rewrite ebinder_morphism.
    rewrite binary_morphism.
    f_equal. f_equal.
    rewrite pm_correctness. simpl. by rewrite pm_ezero_increase.
    Search nest_ex increase_ex.
  Defined.
  Solve Obligations of kore_top_Unary with intros;wf_auto2.
  Fail Next Obligation. *)


  Definition kore_is_predicate (s : Pattern) (ph1 : Pattern) :=
    patt_or (kore_valid s ph1) (patt_equal ph1 patt_bott).
  Definition kore_is_nonempty_sort (s : Pattern) :=
    patt_defined (kore_top s).

  (* These are just ml primitives *)
  Definition kore_mu := patt_mu.
  Definition kore_nu := patt_nu.

  Definition kore_next (s : Pattern) (ph1 : Pattern) :=
    patt_app (kore_sym kore_next_symbol) ph1.
  Definition kore_all_path_next (s : Pattern) (ph1 : Pattern) :=
    kore_not s (kore_next s (kore_not s ph1)).
  Definition kore_eventually (s : Pattern) (ph1 : Pattern) :=
    kore_mu (kore_or (nest_mu s) (nest_mu ph1) (kore_next (nest_mu s) B0)).
  (* TODO: check. not well_founded and eventually is equivalent to this: *)
  Definition kore_weak_eventually (s : Pattern) (ph1 : Pattern) :=
    kore_not s (kore_mu (kore_not (nest_mu s)
                             (kore_or (nest_mu s)
                                      (nest_mu ph1)
                                      (kore_next (nest_mu s)
                                        (kore_not (nest_mu s) B0))))).
  Definition kore_always (s : Pattern) (ph1 : Pattern) := 
    kore_not s (kore_mu (kore_not (nest_mu s)
       (kore_and (nest_mu s) (nest_mu ph1)
         (kore_all_path_next (nest_mu s) (kore_not (nest_mu s) B0))))).
  Definition kore_well_founded (s : Pattern) :=
    kore_mu (kore_all_path_next (nest_mu s) B0).
  Definition kore_well_founded_alt (s : Pattern) :=
    kore_mu (kore_all_path_next (nest_mu s) (kore_always (nest_mu s) B0)).
  Definition kore_rewrites (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_implies s ph1 (kore_next s ph2).
  Definition kore_rewrites_star (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_implies s ph1 (kore_eventually s ph2).
  Definition kore_rewrites_plus (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_implies s ph1 (kore_next s (kore_eventually s ph2)).


  Definition kore_one_path_reaches_star (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_implies s ph1 (kore_weak_eventually s ph2).
  Definition kore_one_path_reaches_plus (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_implies s ph1 (kore_next s (kore_weak_eventually s ph2)).
  Definition kore_circularity (s : Pattern) (ph1 : Pattern) :=
    kore_all_path_next s (kore_always s ph1).
  Definition kore_non_terminating (s : Pattern) := kore_next s (kore_top s).

  Definition kore_all_path_next_nt (s : Pattern) (ph1 : Pattern) :=
    kore_and s (kore_all_path_next s ph1) (kore_non_terminating s).
  Definition kore_all_path_eventually (s : Pattern) (ph1 : Pattern) :=
    kore_mu (kore_or (nest_mu s) (nest_mu ph1) (kore_all_path_next_nt (nest_mu s) B0)).
  Definition kore_all_path_rewrites (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_implies s ph1 (kore_all_path_next_nt s ph2).
  Definition kore_all_path_rewrites_star (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_implies s ph1 (kore_all_path_eventually s ph2).
  Definition kore_all_path_rewrites_plus (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    kore_implies s ph1 (kore_all_path_next_nt s (kore_all_path_eventually s ph2)).

  Definition kore_dv (ph0 : Pattern) (ph1 : Pattern) :=
    patt_app (patt_app (kore_sym kore_dv_symbol) ph0) ph1.


  Definition kore_inj (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) :=
    patt_app (patt_app (patt_app (kore_sym kore_inj_symbol) s1) s2) ph2.

  (**
    Things to consider:
    - From where can we omit the sorts?
    - Related to that: Which constructs can be expressed in a more simple form with more
      primitive ML constructs? That would significantly improve the usability of Kore without
      proving additional derived properties.
    - kore_well_founded <---> kore_well_founded_alt?
  *)

(*   Next Obligation.
  admit.
  Admitted.
  Next Obligation.
  admit.
  Admitted.
Next Obligation.
  admit.
  Admitted.
  Next Obligation.
  admit.
  Admitted. *)



End derived_operations.

Module Notations.

  (* NOTE: format attribute is needed to avoid unnecessary whitespaces *)
  Notation "'⊥(' s ')'" := (kore_bottom s) (format "'⊥(' s ')'") : ml_scope.
  Check ⊥(Nat).
  Notation "'Top(' s ')'" := (kore_top s) (format "'Top(' s ')'") : ml_scope.
  Check Top(Nat).
  Notation "p ∷ s" := (kore_cast s p) (at level 65, format "p  ∷  s", right associativity).
  Check Zero ∷ Nat.
  Notation "'⊢(' s ')' p" := (kore_valid s p) (at level 80, format "'⊢(' s ')'  p").
  Check ⊢(Nat) ⊥.
  Notation "'!(' s ')' p" := (kore_not s p) (at level 71, format "'!(' s ')'  p") : ml_scope.
  Check !(Nat) ⊥.
  Notation "p1 'and(' s ')' p2" := (kore_and s p1 p2) (at level 72, format "p1  'and(' s ')'  p2", left associativity) : ml_scope.
  Check ⊥ and(Nat) Top.
  Notation "p1 'or(' s ')' p2" := (kore_or s p1 p2) (at level 73, format "p1  'or(' s ')'  p2", left associativity) : ml_scope.
  Check ⊥ or(Nat) Top.
  Notation "p1 '-(' s ')->' p2" := (kore_implies s p1 p2) (at level 75, format "p1  '-(' s ')->'  p2", right associativity) : ml_scope.
  Check ⊥ -(Nat)-> Top.
  Notation "p1 '<-(' s ')->' p2" := (kore_iff s p1 p2) (at level 74, format "p1  '<-(' s ')->'  p2") : ml_scope.
  Check ⊥ <-(Nat)-> Top.

  Notation "'⌈(' s1 , s2 ')' p ⌉" := (kore_ceil s1 s2 p) (format "'⌈(' s1 ',' s2 ')'  p ⌉") : ml_scope.
  Check ⌈(Nat, Nat) ⊥⌉.
  Notation "'⌊(' s1 , s2 ')' p ⌋" := (kore_floor s1 s2 p) (format "'⌊(' s1 ',' s2 ')'  p ⌋") : ml_scope.
  Check ⌊(Nat, Nat) ⊥⌋.
  Notation "p1 '=ml(' s1 ',' s2 ')' p2" := (kore_equals s1 s2 p1 p2) (at level 68, format "p1  '=ml(' s1 ',' s2 ')'  p2", left associativity) : ml_scope.
  Check ⊥ =ml(Nat, Nat) Top.
  Notation "p1 '⊆ml(' s1 ',' s2 ')' p2" := (kore_in s1 s2 p1 p2) (at level 68, format "p1  '⊆ml(' s1 ',' s2 ')'  p2", left associativity) : ml_scope.
  Check ⊥ ⊆ml(Nat, Nat) Top.

  Notation "'ex' s1 ',' p 'as' s2" := (kore_exists s1 s2 p) (at level 80, s2 at level 65, format "'ex'  s1 ','  p  'as'  s2") : ml_scope.
  Check ex Nat , ⊥ as Nat.
  Notation "'all' s1 ',' p 'as' s2" := (kore_forall s1 s2 p) (at level 80, s2 at level 65, format "'all'  s1 ','  p  'as'  s2") : ml_scope.
  Goal forall {Σ : Signature} {s1 : Syntax} {s2 : Nat_Syntax.Syntax},
    ~ (all Nat , ⊥ as Nat ⋅ Nat) = (all Nat , ⊥ as (Nat ⋅ Nat)).
  Proof. intros. intro. inversion H. Qed.

(*   Notation "''" := (kore_is_sort s).
  Notation := (kore_is_predicate s p).
  Notation := (kore_is_nonempty_sort s). *)

  (* Notation "'mu' s , p" := (kore_mu s p) (at level 80).
  Check mu Nat, ⊥.
  Notation "'nu' s , p" := (kore_nu s p) (at level 80).
  Check nu Nat, ⊥. *)

  Notation "'•(' s ')' p"    := (kore_next s p) (at level 30, format "'•(' s ')'  p") : ml_scope.
  Check •(Nat) ⊥.
  Notation "'○(' s ')' p"    := (kore_all_path_next s p) (at level 71, format "'○(' s ')'  p") : ml_scope.
  Check ○(Nat) ⊥.
  Notation "'⋄(' s ')' p"    := (kore_eventually s p) (at level 71, format "'⋄(' s ')'  p") : ml_scope.
  Check ⋄(Nat) ⊥.
  Notation "'⋄ʷ(' s ')' p"   := (kore_weak_eventually s p) (at level 71, format "'⋄ʷ(' s ')'  p") : ml_scope.
  Check ⋄ʷ(Nat) ⊥.
(*   Notation "s"       := (kore_well_founded s) (at level 71) : ml_scope. *)
(*   Notation ""       := (kore_well_founded_alt s) (at level 71) : ml_scope. *)
  Notation "'⊞(' s ')' p"    := (kore_always s p) (at level 71, format "'⊞(' s ')'  p") : ml_scope. (* □ is taken by application contexts *)
  Check ⊞(Nat) ⊥.
  Notation "p '=(' s ')=>' q"  := (kore_rewrites s p q) (at level 81, format "p  '=(' s ')=>'  q") : ml_scope.
  Check ⊥ =(Nat)=> Top.
  Notation "p '=(' s ')=>*' q" := (kore_rewrites_star s p q) (at level 81, format "p  '=(' s ')=>*'  q") : ml_scope.
  Check ⊥ =(Nat)=>* Top.
  Notation "p '=(' s ')=>⁺' q" := (kore_rewrites_plus s p q) (at level 81, format "p  '=(' s ')=>⁺'  q") : ml_scope.
  Check ⊥ =(Nat)=>⁺ Top.

(* These probably don't need notations:
  Notation "" := (kore_one_path_reaches_star s p1 p2).
  Notation := (kore_one_path_reaches_plus s p1 p2). *)
  Notation "'↺(' s ')' p" := (kore_circularity s p) (at level 71, format "'↺(' s ')'  p").
  Check ↺(Nat) ⊥.
  Notation "s ⇑" := (kore_non_terminating s) (at level 90).
  Check ⊥ ⋅ ⊥ ⇑.

  (* Notation := (kore_all_path_next_nt s p).
  Notation := (kore_all_path_eventually s p).
  Notation := (kore_all_path_rewrites s p1 p2).
  Notation := (kore_all_path_rewrites_star s p1 p2).
  Notation := (kore_all_path_rewrites_plus s p1 p2).

  Notation := (kore_dv p1 p2).
  Notation := (kore_inj s1 s2 p). *)

End Notations.

Section KoreTheory.

  Import Notations.
  Context
    {Σ : Signature}
    {syntax : Syntax}
  .

 (*  Inductive AxiomName : Set :=
  | InjId
  | SortNext
  | SortDv.

  Print kore_dv. *)
  (* REMARK: all of these three axioms from Metamath seem to be too strong. Quantification is
     missing! *)
(*   Definition axiom (name : AxiomName) : Pattern :=
  match name with
  (* kore-inj-id $a |- ( \eq ( \kore-inj ph0 ph1 ph2 ) ph2 ) $. *)
  | InjId => allₛ, allₛ, all b1, kore_inj b2 b1 b0 =ml b0
  (* kore-next-sorting $a |- ( \imp ( \in-sort ph1 ph0 ) ( \in-sort ( \kore-next ph0 ph1 ) ph0 ) ) $. *)
  | SortNext => allₛ, all b0, b0 ⊆ml ⟦b1⟧ ---> •(b1) b0 ⊆ml ⟦b1⟧
  (* kore-dv-sorting $a |- ( \in-sort ( \kore-dv ph0 ph1 ) ph0 ) $. *)
  | SortDv => allₛ, all b0, kore_dv b1 b0 ⊆ml ⟦b1⟧
  (*
    ∀s : Sorts, ∀x : s, kore_dv x s ∈ ⟦s⟧
    kore-dv ph0 ph1 ⊆ ⟦ph0⟧
  *)
  end.
  Eval simpl in axiom InjId.
  Eval simpl in axiom SortNext.
  Eval simpl in axiom SortDv. *)

  Inductive AxiomName : Set :=
  | InjId φ1 φ2 φ3 : well_formed φ1 -> well_formed φ2 -> well_formed φ3 -> AxiomName
  | SortNext φ1 φ2 : well_formed φ1 -> well_formed φ2 -> AxiomName
  | SortDv φ1 φ2 : well_formed φ1 -> well_formed φ2 -> AxiomName.

  Definition axiom (name : AxiomName) : Pattern :=
  match name with
  (* kore-inj-id $a |- ( \eq ( \kore-inj ph0 ph1 ph2 ) ph2 ) $. *)
  | InjId φ0 φ1 φ2 _ _ _ => kore_inj φ0 φ1 φ2 =ml φ2
  (* kore-next-sorting $a |- ( \imp ( \in-sort ph1 ph0 ) ( \in-sort ( \kore-next ph0 ph1 ) ph0 ) ) $. *)
  | SortNext φ0 φ1 _ _ => φ1 ⊆ml ⟦φ0⟧ ---> •(φ0) φ1 ⊆ml ⟦φ0⟧
  (* kore-dv-sorting $a |- ( \in-sort ( \kore-dv ph0 ph1 ) ph0 ) $. *)
  | SortDv φ0 φ1 _ _ => kore_dv φ0 φ1 ⊆ml ⟦φ0⟧
  (*
    ∀s : Sorts, ∀x : s, kore_dv x s ∈ ⟦s⟧
    kore-dv ph0 ph1 ⊆ ⟦ph0⟧
  *)
  end.
  Eval simpl in axiom (InjId ⊥ ⊥ ⊥ ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2)).
  Eval simpl in axiom (SortNext ⊥ ⊥ ltac:(wf_auto2) ltac:(wf_auto2)).
  Eval simpl in axiom (SortDv ⊥ ⊥ ltac:(wf_auto2) ltac:(wf_auto2)).

  Program Definition named_axioms : NamedAxioms :=
    {|
      NAName := AxiomName;
      NAAxiom := axiom;
    |}.
  Next Obligation.
    destruct name; simpl; unfold kore_inj, kore_dv; wf_auto2.
  Defined.

  Definition KoreTheory := Definedness_Syntax.theory ∪
                           theory_of_NamedAxioms named_axioms.

  Local Goal KoreTheory ⊢ kore_dv ⊥ Top ⊆ml ⟦⊥⟧.
  Proof.
    gapply hypothesis. 2: wf_auto2. try_solve_pile.
    unfold KoreTheory.
    unfold theory_of_NamedAxioms.
    apply elem_of_union_r.
    exists (SortDv ⊥ Top ltac:(wf_auto2) ltac:(wf_auto2)). set_solver.
  Qed.

End KoreTheory.

Section Lemmas.

(*   Require Import wftacticsoriginal. *)
(* Arguments well_formed_positive /.
Arguments well_formed_closed_mu_aux /.
Arguments well_formed_closed_ex_aux /. *)
  Import Notations.
  Context
    {Σ : Signature}
    {syntax : Syntax}
    (Γ : Theory)
    (HΓ : KoreTheory ⊆ Γ)
  .

  Lemma implies_equiv_1 :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (φ -(s)-> ψ) ---> (φ ---> ψ) ∷ s.
  Proof.
    intros. mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd. 2: mlAssumption.
    mlIntro "H3".
    mlDestructOr "H1" as "H" "H". 2: mlAssumption.
    mlDestructAnd "H" as "H0" "H1".
    mlApply "H0" in "H3". mlDestructBot "H3".
  Defined.

  Lemma implies_equiv_2 :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (φ ---> ψ) ∷ s ---> (φ -(s)-> ψ).
  Proof.
    intros.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd. 2: mlAssumption.
    mlIntro "H3".
    mlApplyMeta deMorgan_nand_1 in "H3".
    mlDestructOr "H3" as "H" "H".
    * mlApply "H1". mlApplyMeta not_not_elim in "H".
      mlAssumption.
    * mlExFalso. mlApply "H". mlAssumption.
  Defined.

  Theorem implies_equiv :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (φ -(s)-> ψ) <---> (φ ---> ψ) ∷ s.
  Proof.
    intros.
    mlSplitAnd.
    * mlIntro. mlApplyMeta implies_equiv_1. mlAssumption.
    * mlIntro. mlApplyMeta implies_equiv_2. mlAssumption.
  Defined.

  Lemma iff_equiv_1 :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (φ <-(s)-> ψ) ---> ((φ <---> ψ) ∷ s).
  Proof.
    intros. unfold kore_iff.
    pose proof implies_equiv s φ ψ H H0 H1 as HH.
    pose proof implies_equiv s ψ φ H H1 H0 as FF.
    mlRewrite HH at 1.
    mlRewrite FF at 1.
    unfold kore_and.
    mlIntro "H"; mlDestructAnd "H".
    all: mlSplitAnd; try mlAssumption.
    mlDestructAnd "0". mlDestructAnd "2".
    mlDestructAnd "3". mlSplitAnd; mlAssumption.
  Defined.

  Lemma iff_equiv_2 :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (φ <---> ψ) ∷ s ---> (φ <-(s)-> ψ).
  Proof.
    intros. unfold kore_iff.
    pose proof implies_equiv s φ ψ H H0 H1 as HH.
    pose proof implies_equiv s ψ φ H H1 H0 as FF.
    mlRewrite HH at 1.
    mlRewrite FF at 1.
    unfold kore_and.
    mlIntro "H". mlDestructAnd "H" as "H1" "H2".
    mlDestructAnd "H1".
    repeat mlSplitAnd; try mlAssumption.
  Defined.

  Theorem iff_equiv :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (φ <-(s)-> ψ) <---> (φ <---> ψ) ∷ s.
  Proof.
    intros.
    mlSplitAnd.
    * mlIntro. mlApplyMeta iff_equiv_1. mlAssumption.
    * mlIntro. mlApplyMeta iff_equiv_2. mlAssumption.
  Defined.

  Lemma valid_equiv_1 :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (⊢(s) φ <-(s)-> ψ) ---> (φ ∷ s =ml ψ ∷ s).
  Proof.
    intros. unfold kore_valid.
    pose proof (iff_equiv s φ ψ H H0 H1).
    mlRewrite H2 at 1.
    mlIntro "H".
    mlApplyMeta patt_total_and_2.
    2: unfold KoreTheory in HΓ; set_solver.
    mlSplitAnd.
    * mlApplyMeta floor_monotonic. mlExact "H".
      2: wf_auto2.
      2: unfold KoreTheory in HΓ; set_solver.
      clear hasserted.
      instantiate (1 := AnyReasoning).
      mlIntro "H".
      mlIntro "H0".
      mlDestructAnd "H0" as "H0_1" "H0_2".
      mlSplitAnd. 2: mlAssumption.
      mlDestructAnd "H" as "H_1" "H_2".
      mlApply "H_2" in "H0_2".
      mlDestructAnd "H0_2" as "H3" "H4".
      mlDestructAnd "H3" as "H5" "H6".
      mlApply "H5".
      mlAssumption.
    * mlApplyMeta floor_monotonic. mlExact "H".
      2: wf_auto2.
      2: unfold KoreTheory in HΓ; set_solver.
      clear hasserted.
      instantiate (1 := AnyReasoning).
      mlIntro "H".
      mlIntro "H0".
      mlDestructAnd "H0" as "H0_1" "H0_2".
      mlSplitAnd. 2: mlAssumption.
      mlDestructAnd "H" as "H_1" "H_2".
      mlApply "H_2" in "H0_2".
      mlDestructAnd "H0_2" as "H3" "H4".
      mlDestructAnd "H3" as "H5" "H6".
      mlApply "H6".
      mlAssumption.
  Defined.

  Lemma valid_equiv_2 :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (φ ∷ s =ml ψ ∷ s) ---> (⊢(s) φ <-(s)-> ψ).
  Proof.
    intros. unfold kore_valid.
    pose proof (iff_equiv s φ ψ H H0 H1).
    mlRewrite H2 at 1.
    mlIntro "H".
    mlApplyMeta patt_total_and_2.
    2: unfold KoreTheory in HΓ; set_solver.
    mlSplitAnd.
    * mlApplyMeta floor_monotonic. mlExact "H".
      2: wf_auto2.
      2: unfold KoreTheory in HΓ; set_solver.
      clear hasserted.
      instantiate (1 := AnyReasoning).
      mlIntro "H".
      mlIntro "H0".
      mlDestructAnd "H0" as "H0_1" "H0_2".
      mlAssumption.
    * mlApplyMeta floor_monotonic. mlExact "H".
      2: wf_auto2.
      2: unfold KoreTheory in HΓ; set_solver.
      clear hasserted.
      instantiate (1 := AnyReasoning).
      mlIntro "H".
      mlIntro "H0".
      mlDestructAnd "H" as "H_1" "H_2".
      mlSplitAnd. 2: mlAssumption.
      mlSplitAnd.
      - mlIntro "H".
        mlConj "H" "H0" as "H2".
        fold (φ ∷ s).
        mlApply "H_1" in "H2".
        mlDestructAnd "H2".
        mlAssumption.
      - mlIntro "H".
        mlConj "H" "H0" as "H2".
        fold (ψ ∷ s).
        mlApply "H_2" in "H2".
        mlDestructAnd "H2".
        mlAssumption.
  Defined.

  Theorem valid_equiv :
    forall s φ ψ,
      well_formed s ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ (⊢(s) φ <-(s)-> ψ) <---> (φ ∷ s =ml ψ ∷ s).
  Proof.
    intros.
    mlSplitAnd.
    * mlIntro. mlApplyMeta valid_equiv_1. mlAssumption.
    * mlIntro. mlApplyMeta valid_equiv_2. mlAssumption.
  Defined.

  Lemma floor_equiv_1 :
    forall s1 s2 φ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      Γ ⊢ ⌊(s1, s2) φ⌋ ---> ⌊φ or !Top(s1)⌋ ∷ s2.
  Proof.
    intros.
    unfold kore_floor, kore_ceil, kore_not.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd. 2: mlAssumption.
    unfold patt_total.
    mlApplyMeta deMorgan_nand_1 in "H1".
    mlDestructOr "H1" as "H" "H".
    2: { mlApply "H" in "H2". mlDestructBot "H2". }
    mlClear "H2".
    mlIntro "H0".
    mlApply "H". mlClear "H".
    mlApplyMeta ceil_monotonic. mlAssumption.
    2: wf_auto2.
    2: unfold KoreTheory in HΓ; set_solver.
    instantiate (1 := AnyReasoning).
    mlIntro "H".
    mlApplyMeta deMorgan_nor_1 in "H".
    mlDestructAnd "H" as "H1" "H2".
    mlApplyMeta not_not_elim in "H2".
    repeat mlSplitAnd; mlAssumption.
  Defined.

  Lemma floor_equiv_2 :
    forall s1 s2 φ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      Γ ⊢ ⌊φ or !Top(s1)⌋ ∷ s2 ---> ⌊(s1, s2) φ⌋.
  Proof.
    intros.
    unfold kore_floor, kore_ceil, kore_not.
    mlIntro "H".
    mlDestructAnd "H" as "H1" "H2".
    mlSplitAnd. 2: mlAssumption.
    mlIntro "H". mlDestructAnd "H" as "H0" "H3".
    mlApply "H1".
    mlApplyMeta ceil_monotonic. mlExact "H0".
    2: wf_auto2.
    2: unfold KoreTheory in HΓ; set_solver.
    instantiate (1 := AnyReasoning).
    mlIntro "H".
    mlIntro "H0".
    mlDestructAnd "H" as "H1" "H2".
    mlDestructAnd "H1" as "H3" "H4".
    mlDestructOr "H0" as "H5" "H5".
    * mlApply "H3". mlAssumption.
    * mlApply "H5". mlAssumption.
  Defined.

  Theorem floor_equiv :
    forall s1 s2 φ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      Γ ⊢ ⌊(s1, s2) φ⌋ <---> ⌊φ or !Top(s1)⌋ ∷ s2.
  Proof.
    intros.
    mlSplitAnd.
    * mlIntro. mlApplyMeta floor_equiv_1. mlAssumption.
    * mlIntro. mlApplyMeta floor_equiv_2. mlAssumption.
  Defined.

  Lemma equals_equiv_1 :
    forall s1 s2 φ ψ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ φ =ml(s1,s2) ψ ---> ((φ ∷ s1) =ml (ψ ∷ s1)) ∷ s2.
  Proof.
    intros.
    unfold kore_equals.
    mlIntro "H".
    mlApplyMeta floor_equiv_1 in "H".
    mlDestructAnd "H" as "H0" "H1".
    mlSplitAnd. 2: mlAssumption.
    mlClear "H1".
    mlApplyMeta floor_monotonic. mlExact "H0".
    2: wf_auto2.
    2: unfold KoreTheory in HΓ; set_solver.
    instantiate (1 := AnyReasoning).
    mlIntro "H".
    mlSplitAnd; mlIntro "H0";
      mlDestructAnd "H0" as "H0_1" "H0_2";
      mlDestructOr "H" as "H1" "H1".
    * mlApplyMeta iff_equiv_1 in "H1".
      mlDestructAnd "H1" as "H2" "H3".
      mlDestructAnd "H2" as "H4" "H5".
      mlApply "H4" in "H0_1".
      mlSplitAnd; mlAssumption.
    * mlApply "H1" in "H0_2".
      mlDestructBot "H0_2".
    * mlApplyMeta iff_equiv_1 in "H1".
      mlDestructAnd "H1" as "H2" "H3".
      mlDestructAnd "H2" as "H4" "H5".
      mlApply "H5" in "H0_1".
      mlSplitAnd; mlAssumption.
    * mlApply "H1" in "H0_2".
      mlDestructBot "H0_2".
  Defined.

  Lemma equals_equiv_2 :
    forall s1 s2 φ ψ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ ((φ ∷ s1) =ml (ψ ∷ s1)) ∷ s2 ---> φ =ml(s1,s2) ψ.
  Proof.
    intros.
    mlIntro "H".
    mlApplyMeta floor_equiv_2.
    mlDestructAnd "H" as "H0" "H1".
    mlSplitAnd. 2: mlAssumption.
    mlApplyMeta floor_monotonic. mlExact "H0".
    2: wf_auto2.
    2: unfold KoreTheory in HΓ; set_solver.
    instantiate (1 := AnyReasoning).
    mlIntro "H".
    mlDestructAnd "H" as "H0" "H1".
    mlIntro "H". mlIntro "H2".
    mlApply "H".
    mlApplyMeta iff_equiv_2.
    mlSplitAnd. 2: mlAssumption.
    mlSplitAnd; mlIntro "H3"; mlConj "H3" "H2" as "D".
    * fold (φ ∷ s1).
      mlApply "H0" in "D". mlDestructAnd "D". mlAssumption.
    * fold (ψ ∷ s1).
      mlApply "H1" in "D". mlDestructAnd "D". mlAssumption.
  Defined.

  Theorem equals_equiv :
    forall s1 s2 φ ψ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ φ =ml(s1,s2) ψ <--->
          ((φ ∷ s1) =ml (ψ ∷ s1)) ∷ s2.
  Proof.
    intros.
    mlSplitAnd.
    * mlIntro. mlApplyMeta equals_equiv_1. mlAssumption.
    * mlIntro. mlApplyMeta equals_equiv_2. mlAssumption.
  Defined.

  Lemma in_equiv_1 :
    forall s1 s2 φ ψ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ φ ⊆ml(s1,s2) ψ ---> ((φ ∷ s1) ⊆ml (ψ ∷ s1)) ∷ s2.
  Proof.
    intros.
    unfold kore_equals.
    mlIntro "H".
    mlApplyMeta floor_equiv_1 in "H".
    mlDestructAnd "H" as "H0" "H1".
    mlSplitAnd. 2: mlAssumption.
    mlClear "H1".
    mlApplyMeta floor_monotonic. mlExact "H0".
    2: wf_auto2.
    2: unfold KoreTheory in HΓ; set_solver.
    instantiate (1 := AnyReasoning).
    mlIntro "H".
    mlIntro "H0".
    mlDestructAnd "H0" as "H1" "H2".
    mlDestructOr "H" as "H0" "H0".
    2: { mlApply "H0" in "H2". mlDestructBot "H2". }
    mlApplyMeta implies_equiv_1 in "H0".
    mlDestructAnd "H0" as "H" "H3".
    mlApply "H" in "H1".
    mlSplitAnd; mlAssumption.
  Defined.

  Lemma in_equiv_2 :
    forall s1 s2 φ ψ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ ((φ ∷ s1) ⊆ml (ψ ∷ s1)) ∷ s2 ---> φ ⊆ml(s1,s2) ψ.
  Proof.
    intros.
    mlIntro "H".
    mlApplyMeta floor_equiv_2.
    mlDestructAnd "H" as "H0" "H1".
    mlSplitAnd. 2: mlAssumption.
    mlApplyMeta floor_monotonic. mlExact "H0".
    2: wf_auto2.
    2: unfold KoreTheory in HΓ; set_solver.
    instantiate (1 := AnyReasoning).
    mlIntro "H".
    mlIntro "H0".
    mlIntro "H1".
    mlApply "H0".
    mlApplyMeta implies_equiv_2.
    mlSplitAnd. 2: mlAssumption.
    mlIntro "H2".
    mlConj "H2" "H1" as "D".
    fold (φ ∷ s1).
    mlApply "H" in "D".
    mlDestructAnd "D".
    mlAssumption.
  Defined.

  Theorem in_equiv :
    forall s1 s2 φ ψ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed φ ->
      well_formed ψ ->
      Γ ⊢ φ ⊆ml(s1,s2) ψ <---> ((φ ∷ s1) ⊆ml (ψ ∷ s1)) ∷ s2.
  Proof.
    intros.
    mlSplitAnd.
    * mlIntro. mlApplyMeta in_equiv_1. mlAssumption.
    * mlIntro. mlApplyMeta in_equiv_2. mlAssumption.
  Defined.

  Lemma forall_equiv_1 :
    forall s1 s2 φ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed (ex, φ) ->
      Γ ⊢ all s1, φ as s2 ---> (all s1 , φ) ∷ s2.
  Proof.
    intros.
    unfold kore_forall, kore_not, kore_exists, kore_top.
    toMLGoal. { unfold kore_forall, kore_exists, patt_sorted_forall, patt_sorted_exists. wf_auto2. }
    mlIntro.
    mlDestructAnd "0".
    mlSplitAnd. 2: mlAssumption.
    mlIntroAll x. mlSimpl. cbn.
    setoid_rewrite nest_ex_same.
    mlIntro.
    epose proof deMorgan_nand Γ (ex s1, ! φ and ⟦ s2 ⟧) ⟦ s2 ⟧ _ _.
    use AnyReasoning in H2.
    mlAdd H2 as "H2".
    mlDestructAnd "H2". mlClear "4".
    mlApply "3" in "1". mlClear "3".
    mlDestructOr "1".
    - mlSpecialize "3" with x.
      mlSimpl. simpl.
      setoid_rewrite nest_ex_same.
      rewrite (evar_open_not_occur _ _ s2). wf_auto2.
      mlDestructOr "3".
      + mlApply "1" in "0". mlDestructBot "0".
      + pose proof deMorgan_nand Γ
            (! φ^{evar:0↦x}) ⟦ s2 ⟧
       ltac:(wf_auto2) ltac:(wf_auto2).
       use AnyReasoning in H3.
       mlAdd H3 as "H3".
       mlDestructAnd "H3". mlClear "3".
       mlApply "1" in "4". mlClear "1".
       mlDestructOr "4".
       ** mlApplyMeta Misc.notnot_taut_1 in "1".
          mlAssumption.
       ** mlApply "3" in "2". mlDestructBot "2".
    - mlExFalso. mlApply "4". mlAssumption.
    Unshelve.
      all: unfold patt_sorted_exists in *; wf_auto2.
  Defined.

  Lemma forall_equiv_2 :
    forall s1 s2 φ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed (ex, φ) ->
      Γ ⊢ (all s1 , φ) ∷ s2 --->  all s1 , φ as s2.
  Proof.
    intros.
    toMLGoal. { unfold kore_forall, kore_exists, patt_sorted_forall, patt_sorted_exists. wf_auto2. }
    mlIntro. mlDestructAnd "0" as "H" "Hs".
    mlSplitAnd. 2: mlAssumption.
    mlIntro "E". mlDestructAnd "E" as "E1" "E2".
    mlDestructEx "E1" as x.
    mlSimpl.
    setoid_rewrite nest_ex_same.
    rewrite (evar_open_not_occur _ _ s2). wf_auto2.
    mlDestructAnd "E1" as "E1_1" "E1_2".
    mlDestructAnd "E1_2".
    mlApply "0".
    mlSpecialize "H" with x. mlSimpl. simpl.
    setoid_rewrite nest_ex_same.
    mlApply "H". mlAssumption.
  Defined.

  Theorem forall_equiv :
    forall s1 s2 φ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed (ex, φ) ->
      Γ ⊢ all s1, φ as s2 <---> (all s1 , φ) ∷ s2.
  Proof.
    intros.
    toMLGoal. { unfold kore_forall, kore_exists, patt_sorted_forall, patt_sorted_exists. wf_auto2. }
    mlSplitAnd.
    * mlIntro. mlApplyMeta forall_equiv_1. mlAssumption.
    * mlIntro. mlApplyMeta forall_equiv_2. mlAssumption.
  Defined.

  Theorem kore_equals_elim :
    forall φ ψ (C : PatternCtx) s1 s2,
      well_formed φ ->
      well_formed ψ ->
      well_formed s1 ->
      well_formed s2 ->
      PC_wf C ->
      pattern_kt_well_formed (pcPattern C) ->
      Γ ⊢ φ =ml(s1, s2) ψ --->
          emplace C (φ ∷ s1) --->
          emplace C (ψ ∷ s1) ∷ s2.
  Proof.
    intros.
    unfold PC_wf in H3.
    toMLGoal. wf_auto2.
    mlIntro "H".
    mlApplyMeta equals_equiv_1 in "H".
    mlDestructAnd "H" as "H0" "Hsort".
    mlIntro "HC".
    mlSplitAnd. 2: mlAssumption.
    pose proof (HEQ := equality_elimination Γ (φ ∷ s1) (ψ ∷ s1) C ltac:(unfold KoreTheory in HΓ;set_solver) ltac:(wf_auto2) ltac:(wf_auto2) ltac:(wf_auto2) H4).
    mlApplyMeta HEQ.
    mlSplitAnd; mlAssumption.
  Defined.

End Lemmas.

