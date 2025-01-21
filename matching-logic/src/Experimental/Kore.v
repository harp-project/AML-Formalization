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
    patt_and (patt_not ph1) (kore_top s).
  #[global]
  Program Instance kore_not_Binary : Binary kore_not.
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_not_Binary with intros; unfold kore_not; wf_auto2.
  Fail Next Obligation.

  (* TODO: check if s is needed! *)
  Definition kore_and (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    patt_and ph1 ph2.
  #[global]
  Program Instance kore_and_Binary s : Binary (kore_and s).
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_and_Binary with intros; unfold kore_and; wf_auto2.
  Fail Next Obligation.

  Local Goal forall φ1, well_formed φ1 -> well_formed (kore_and b0 φ1 ⊥).
  Proof.
    intros. wf_auto2.
  Qed.

  (* TODO: check if s is needed! *)
  Definition kore_or (s : Pattern) (ph1 : Pattern) (ph2 : Pattern) :=
    patt_or ph1 ph2.
  #[global]
  Program Instance kore_or_Binary s : Binary (kore_or s).
  Next Obligation.
    intros. rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_or_Binary with intros; unfold kore_or; wf_auto2.
  Fail Next Obligation.

  Local Goal forall φ1, well_formed φ1 -> well_formed (kore_or b0 φ1 ⊥).
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

  (* TODO: check if s1 is needed! *)
  Definition kore_ceil (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) := 
    patt_and (patt_defined ph2) (kore_top s2).
  #[global]
  Program Instance kore_ceil_Binary s : Binary (kore_ceil s).
  Next Obligation.
    intros. repeat rewrite pm_correctness. simpl.
    repeat rewrite pm_correctness. reflexivity.
  Defined.
  Solve Obligations of kore_ceil_Binary with intros; unfold kore_ceil; wf_auto2.
  Fail Next Obligation.
  Local Goal forall s2 φ1, well_formed φ1 -> well_formed s2 -> well_formed (kore_ceil b0 s2 φ1).
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

  Definition kore_exists (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) :=
    patt_and (patt_sorted_exists s1 ph2) (patt_inhabitant_set s2).
  Definition kore_forall (s1 : Pattern) (s2 : Pattern) (ph2 : Pattern) :=
    kore_not s2 (kore_exists s1 s2 (kore_not s2 ph2)).
(*   Definition kore_forall_sort (s : Pattern) :=
    patt_forall_sort s. *)
  Definition kore_is_sort (s : Pattern) := patt_exists_sort (patt_equal b0 s).
  Definition kore_is_predicate (s : Pattern) (ph1 : Pattern) :=
    patt_or (kore_valid s ph1) (patt_equal ph1 patt_bott).
  Definition kore_is_nonempty_sort (s : Pattern) :=
    patt_defined (patt_inhabitant_set s).


  Definition kore_mu (s : Pattern) (ph1 : Pattern) :=
    patt_and (patt_mu ph1) (patt_inhabitant_set s).
  Definition kore_nu (s : Pattern) (ph1 : Pattern) :=
    let ph2 := bsvar_subst (kore_not s B0) 0 ph1 in
      kore_not s (kore_mu s (kore_not s ph2)).


  Definition kore_next (s : Pattern) (ph1 : Pattern) :=
    patt_app (kore_sym kore_next_symbol) ph1.
  Definition kore_all_path_next (s : Pattern) (ph1 : Pattern) :=
    kore_not s (kore_next s (kore_not s ph1)).
  Definition kore_eventually (s : Pattern) (ph1 : Pattern) :=
    kore_mu s (kore_or (nest_mu s) (nest_mu ph1) (kore_next (nest_mu s) B0)).
  (* TODO: check. not well_founded and eventually is equivalent to this: *)
  Definition kore_weak_eventually (s : Pattern) (ph1 : Pattern) :=
    kore_not s (kore_mu s (kore_not (nest_mu s)
                             (kore_or (nest_mu s)
                                      (nest_mu ph1)
                                      (kore_next (nest_mu s)
                                        (kore_not (nest_mu s) B0))))).
  Definition kore_always (s : Pattern) (ph1 : Pattern) := 
    kore_not s (kore_mu s (kore_not (nest_mu s)
       (kore_and (nest_mu s) (nest_mu ph1)
         (kore_all_path_next (nest_mu s) (kore_not (nest_mu s) B0))))).
  Definition kore_well_founded (s : Pattern) :=
    kore_mu s (kore_all_path_next (nest_mu s) B0).
  Definition kore_well_founded_alt (s : Pattern) :=
    kore_mu s (kore_all_path_next (nest_mu s) (kore_always (nest_mu s) B0)).
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
    kore_mu s (kore_or (nest_mu s) (nest_mu ph1) (kore_all_path_next_nt (nest_mu s) B0)).
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

  Next Obligation.
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
  Admitted.



End derived_operations.

Module Notations.

  (* NOTE: format attribute is needed to avoid unnecessary whitespaces *)
  Notation "'⊥(' s ')'" := (kore_bottom s) (format "'⊥(' s ')'") : ml_scope.
  Check ⊥(Nat).
  Notation "'Top(' s ')'" := (kore_top s) (format "'Top(' s ')'") : ml_scope.
  Check Top(Nat).
  (* Notation "" := (kore_valid s p). *)
  Notation "'!(' s ')' p" := (kore_not s p) (at level 71, format "'!(' s ')'  p") : ml_scope.
  Check !(Nat) ⊥.
  Notation "p1 'and(' s ')' p2" := (kore_and s p1 p2) (at level 72, format "p1  'and(' s ')'  p2") : ml_scope.
  Check ⊥ and(Nat) Top.
  Notation "p1 'or(' s ')' p2" := (kore_or s p1 p2) (at level 73, format "p1  'or(' s ')'  p2") : ml_scope.
  Check ⊥ or(Nat) Top.
  Notation "p1 '--(' s ')->' p2" := (kore_implies s p1 p2) (at level 75, format "p1  '--(' s ')->'  p2") : ml_scope.
  Check ⊥ --(Nat)-> Top.
  Notation "p1 '<-(' s ')->' p2" := (kore_iff s p1 p2) (at level 74, format "p1  '<-(' s ')->'  p2") : ml_scope.
  Check ⊥ <-(Nat)-> Top.

  Notation "'⌈(' s1 , s2 ')' p ⌉" := (kore_ceil s1 s2 p) (format "'⌈(' s1 ',' s2 ')'  p ⌉") : ml_scope.
  Check ⌈(Nat, Nat) ⊥⌉.
  Notation "'⌊(' s1 , s2 ')' p ⌋" := (kore_floor s1 s2 p) (format "'⌊(' s1 ',' s2 ')'  p ⌋") : ml_scope.
  Check ⌊(Nat, Nat) ⊥⌋.
  Notation "p1 '=ml(' s1 ',' s2 ')' p2" := (kore_equals s1 s2 p1 p2) (at level 67, format "p1  '=ml(' s1 ',' s2 ')'  p2") : ml_scope.
  Check ⊥ =ml(Nat, Nat) Top.
  Notation "p1 '⊆ml(' s1 ',' s2 ')' p2" := (kore_in s1 s2 p1 p2) (at level 67, format "p1  '⊆ml(' s1 ',' s2 ')'  p2") : ml_scope.
  Check ⊥ ⊆ml(Nat, Nat) Top.

  Notation "'ex' s1 '∷' s2 ',' p" := (kore_exists s1 s2 p) (at level 80, format "'ex'  s1  '∷'  s2 ','  p") : ml_scope.
  Check ex Nat ∷ Nat , ⊥.
  Notation "'all' s1 '∷' s2 ',' p" := (kore_forall s1 s2 p) (at level 80, format "'all'  s1  '∷'  s2 ','  p") : ml_scope.
  Check all Nat ∷ Nat , ⊥.
(*   Notation "''" := (kore_is_sort s).
  Notation := (kore_is_predicate s p).
  Notation := (kore_is_nonempty_sort s). *)

  Notation "'mu' s , p" := (kore_mu s p) (at level 80).
  Check mu Nat, ⊥.
  Notation "'nu' s , p" := (kore_nu s p) (at level 80).
  Check nu Nat, ⊥.

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
    destruct name; simpl; wf_auto2.
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

  Import Notations.
  Context
    {Σ : Signature}
    {syntax : Syntax}
    (Γ : Theory)
    (HΓ : KoreTheory ⊆ Γ)
  .
  Check kore_well_founded.
  Lemma well_founded_alt_1 :
    forall s,
      well_formed s ->
      Γ ⊢ kore_well_founded_alt s ---> kore_well_founded s.
  Proof.
    intros. unfold kore_well_founded, kore_well_founded_alt.
    toMLGoal. { admit. }
    mlIntro "H".
    mlDestructAnd "H" as "H_1" "H_2".
    mlSplitAnd. 2: mlAssumption.
    mlClear "H_2".
    pose proof Pre_fixp as HPF.
    pose proof Knaster_tarski as HKT.
    unfold kore_always, kore_all_path_next.
    assert (nest_mu s = s) as Hs by admit.
    repeat rewrite Hs. unfold nest_mu. simpl.
    unfold kore_mu.

  Abort.

  Local Goal
    forall A B s,
      Γ ⊢ kore_and s A B <---> kore_not s (kore_or s (kore_not s A) (kore_not s B)).
  Proof.
    intros. unfold kore_and, kore_not, kore_or, kore_top.
    toMLGoal. admit.
    mlSplitAnd.
    * mlIntro.
      mlIntro.
      mlDestructAnd "0".
      mlDestructOr "1". admit. admit.
    *
  Abort.

  Local Goal
    forall s1 s2 φ,
      well_formed s1 ->
      well_formed s2 ->
      well_formed (ex, φ) ->
      Γ ⊢ kore_forall s1 s2 φ <---> (all s1 , φ) and ⟦s2⟧.
  Proof.
    intros.
    unfold kore_forall, kore_not, kore_exists, kore_top.
    toMLGoal. { simpl in *. wf_auto2. }
    mlSplitAnd.
    * mlIntro.
      mlDestructAnd "0".
      mlSplitAnd. 2: mlAssumption.
      mlIntroAll x. mlSimpl. cbn.
      setoid_rewrite nest_ex_same.
      mlIntro.
      pose proof deMorgan_nand Γ (ex s1, ! φ and ⟦ s2 ⟧) ⟦ s2 ⟧
         ltac:(wf_auto2) ltac:(wf_auto2).
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
    * mlIntro. mlDestructAnd "0" as "H" "Hs".
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

  Lemma well_founded_alt_1 :
    forall s,
      well_formed s ->
      Γ ⊢ kore_well_founded_alt s ---> kore_well_founded s.
  Proof.
  
  Defined.
End Lemmas.

