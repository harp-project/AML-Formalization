From Coq Require Import ssreflect.
From Coq Require Extraction extraction.ExtrHaskellString.


From Coq Require Import Strings.String.
From Equations Require Import Equations.

From stdpp Require Export base.
From MatchingLogic Require Import Syntax SignatureHelper ProofSystem ProofMode.
From MatchingLogicProver Require Import MMProofExtractor Named.

From stdpp Require Import base finite gmap mapset listset_nodup numbers.

Open Scope ml_scope.
Module MMTest.
  Import
    MatchingLogic.Syntax.Notations
    MatchingLogic.DerivedOperators.Notations
    MatchingLogic.ProofSystem.Notations
  .

  Import MetaMath.

  Inductive Symbol := a | b | c .


  Instance Symbol_eqdec : EqDecision Symbol.
  Proof.
    intros s1 s2. unfold Decision. decide equality.
  Defined.

  Instance Σ : Signature :=
    {| variables := StringMLVariables ;
       symbols := Symbol ;
    |}.

  Instance symbols_countable : Countable symbols.
  Proof.
    eapply finite_countable.
    Unshelve.
    destruct Symbol_eqdec with (x:=a) (y:=b), Symbol_eqdec with (x:=a) (y:=c).
    - econstructor.
      + apply NoDup_cons_2 with (x:=a) (l:=[]).
        apply not_elem_of_nil.
        constructor.
      + intros. destruct x.
        apply elem_of_list_here.
        rewrite e. apply elem_of_list_here.
        rewrite e0. apply elem_of_list_here.
    - econstructor.
      + apply NoDup_cons_2 with (x:=a) (l:=[c]).
        apply not_elem_of_cons. split. auto. apply not_elem_of_nil.
        constructor. apply not_elem_of_nil.
        constructor.
      + intros. destruct x.
        apply elem_of_list_here.
        rewrite e. apply elem_of_list_here.
        apply elem_of_list_further. apply elem_of_list_here.
    - econstructor.
      + apply NoDup_cons_2 with (x:=a) (l:=[b]).
        apply not_elem_of_cons. split. auto. apply not_elem_of_nil.
        constructor. apply not_elem_of_nil.
        constructor.
      + intros. destruct x.
        apply elem_of_list_here.
        apply elem_of_list_further. apply elem_of_list_here.
        rewrite e. apply elem_of_list_here.
    - econstructor.
      + apply NoDup_cons_2 with (x:=a) (l:=[b; c]).
        apply not_elem_of_cons. split. auto.
        apply not_elem_of_cons. split. auto. apply not_elem_of_nil.
        constructor. apply not_elem_of_cons. split. auto. apply not_elem_of_nil.
        constructor. apply not_elem_of_nil.
        constructor.
      + intros. destruct x.
        apply elem_of_list_here.
        apply elem_of_list_further. apply elem_of_list_here.
        apply elem_of_list_further. apply elem_of_list_further. apply elem_of_list_here.
  Qed.

  Definition symbolPrinter (s : Symbol) : string :=
    match s with
    | a => "sym-a"
    | b => "sym-b"
    | c => "sym-c"
    end.

  
  Definition A := patt_sym a.
  Definition B := patt_sym b.
  Definition C := patt_sym c.
  
  Definition ϕ₁ := A ---> (B ---> A).

  Lemma ϕ₁_holds:
    ∅ ⊢ ϕ₁.
  Proof.
    apply P1; auto.
  Defined.

  Definition proof_1 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ₁_holds
    )).

  Definition ϕ₂ := (A ---> (B ---> C)) ---> (A ---> B) ---> (A ---> C).

  Lemma ϕ₂_holds:
    ∅ ⊢ ϕ₂.
  Proof.
    apply P2; auto.
  Defined.

  Definition proof_2 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ₂_holds
    )).
  
  (*Compute proof₂.*)

  Definition ϕ₃ := ! ! A ---> A.
  
  Lemma ϕ₃_holds:
    ∅ ⊢ ϕ₃.
  Proof.
    apply P3; auto.
  Defined.

  Definition proof_3 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ₃_holds
    )).
  
  Definition ϕ₄ := A ---> A.
  
  Lemma ϕ₄_holds:
    ∅ ⊢ ϕ₄.
  Proof.
    apply A_impl_A. auto.
  Defined.

  Definition proof_4 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ₄_holds
    )).
  
  Definition ϕ₅ := (A ---> B) <---> (! A or B).

  Lemma ϕ₅_holds:
    ∅ ⊢ ϕ₅.
  Proof.
    apply impl_iff_notp_or_q; auto.
  Defined.

  Definition proof_5 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ₅_holds
    )).

  Definition ϕ₆ := (A ---> ! ! B) ---> (A ---> B).

  Lemma ϕ₆_holds:
    ∅ ⊢ ϕ₆.
  Proof.
    apply A_impl_not_not_B; auto.
  Defined.

  Definition proof_6 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ₆_holds
    )).


  Definition ϕ₇ := ((B ---> C) ---> ((A ---> B) ---> (A ---> C))).

  Lemma ϕ₇_holds:
    ∅ ⊢ ϕ₇.
  Proof.
    apply prf_weaken_conclusion; auto.
  Defined.

  Definition proof_7 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ₇_holds
    )).

  
  Definition ϕ₈ := (A and B) ---> A.

  Lemma ϕ₈_holds:
    ∅ ⊢ ϕ₈.
  Proof.
    apply pf_conj_elim_l; auto.
  Defined.

  Definition proof_8 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ₈_holds
    )).

  (* Tests that existentials are printed correctly *)
  Definition ϕ9 : Pattern
    := ((patt_exists (patt_bound_evar 0)) ---> (B ---> ((patt_exists (patt_bound_evar 0))))).

  Open Scope string.
  
  Lemma ϕ9_holds:
    ∅ ⊢ ϕ9.
  Proof.
    apply P1; auto.
  Defined.
  
  Definition proof_9 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ9_holds
    )).
  
  Definition ϕ10 := ((patt_exists (patt_bound_evar 0))) or ((patt_exists (patt_bound_evar 0))).

  Lemma ϕ10_holds:
    ∅ ⊢ ϕ10.
  Proof.
    toMyGoal.
    { wf_auto2. }
    unfold ϕ10.
    mgRight.
    fromMyGoal. intros _ _.
    apply Existence.
  Defined.
  
  Compute (dependenciesForPattern symbolPrinter id id (to_NamedPattern2
                                                         ϕ10)).

  Definition proof_10 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕ10_holds
    )).

  Definition ϕ11 := instantiate (ex , patt_bound_evar 0) (patt_free_evar "y") ---> ex , patt_bound_evar 0.
  Lemma ϕ11_holds:
    ∅ ⊢ ϕ11.
  Proof.
    apply Ex_quan.
    { wf_auto2. }
  Qed.

  Definition ϕtest := (A ---> A) ---> (A ---> B) ---> (A ---> B).
  Lemma ϕtest_holds: ∅ ⊢ ϕtest.
  Proof.
    unfold ϕtest.
    replace (A ---> B) with (fold_right patt_imp B ([]++[A])) by reflexivity.
    apply prf_strenghten_premise_iter.
    all: auto.
  Defined.

  Definition proof_test : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          id
          id
          _
          _
          ϕtest_holds
    )).

  
  (*Compute proof_test.*)

  
End MMTest.

Extraction Language Haskell.

Extraction "proof_1_mm.hs" MMTest.proof_1.
Extraction "proof_2_mm.hs" MMTest.proof_2.
Extraction "proof_3_mm.hs" MMTest.proof_3.
Extraction "proof_4_mm.hs" MMTest.proof_4.
Extraction "proof_5_mm.hs" MMTest.proof_5.
Extraction "proof_6_mm.hs" MMTest.proof_6.
Extraction "proof_7_mm.hs" MMTest.proof_7.
Extraction "proof_8_mm.hs" MMTest.proof_8.
Extraction "proof_9_mm.hs" MMTest.proof_9.
(*Extraction "proof_10_mm.hs" MMTest.proof_10.*)
