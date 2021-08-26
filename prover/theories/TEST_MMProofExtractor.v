From Coq Require Extraction extraction.ExtrHaskellString.


From Coq Require Import Strings.String.
From Equations Require Import Equations.

From stdpp Require Export base.
From MatchingLogic Require Import Syntax SignatureHelper ProofSystem Helpers.FOL_helpers.
From MatchingLogicProver Require Import MMProofExtractor.

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

  Instance Symbol_h : SymbolsH Symbol := Build_SymbolsH Symbol Symbol_eqdec.
  
  Instance signature : Signature := @SignatureFromSymbols Symbol _.

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
          _
          _
          ϕ₂_holds
    )).
  
  (*Compute proof₂.*)

  Definition ϕ₃ := ¬ ¬ A ---> A.
  
  Lemma ϕ₃_holds:
    ∅ ⊢ ϕ₃.
  Proof.
    apply P3; auto.
  Defined.

  Definition proof_3 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₃_holds
    )).
  
  (*Compute proof₃.*)

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
          _
          _
          ϕ₄_holds
    )).

  Goal (proof2database symbolPrinter _ _ ϕ₄_holds) = [].
  Proof.
    unfold proof2database. simpl.
    unfold proof2proof.
    unfold ϕ₄_holds. unfold A_impl_A.
    rewrite proof2proof'_equation_6. simpl.
  Abort.
  
  
  (*Compute proof₄.*)

  Definition ϕ₅ := (A ---> B) <---> (¬ A or B).

  Lemma ϕ₅_holds:
    ∅ ⊢ ϕ₅.
  Proof.
    apply impl_iff_notp_or_q; auto.
  Defined.

  (* Takes forever *)
  (*Compute ϕ₅_holds.*)


  Definition proof_5 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₅_holds
    )).

  (* Takes forever *)
  (*
  Compute (proof2database
             symbolPrinter
             _
             _
             ϕ₅_holds).
  *)
  (*
  Print Opaque Dependencies proof₅
  Compute proof₅. (* No longer "Stack overflow", but takes forever *)
   *)
  (* Time Eval compute in proof₅. *) (* Stack overflow *)

  Definition ϕ₆ := (A ---> ¬ ¬ B) ---> (A ---> B).

  Lemma ϕ₆_holds:
    ∅ ⊢ ϕ₆.
  Proof.
    apply A_impl_not_not_B; auto.
  Defined.

  (* Finished transaction in 42.649 secs (42.411u,0.203s) (successful) *)
  (* Time Eval vm_compute in ϕ₆_holds. *)


  Definition proof_6 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
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

  (* Finished transaction in 42.649 secs (42.411u,0.203s) (successful) *)
  (* Time Eval vm_compute in ϕ₆_holds. *)


  Definition proof_7 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
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

  (* Finished transaction in 42.649 secs (42.411u,0.203s) (successful) *)
  (* Time Eval vm_compute in ϕ₆_holds. *)


  Definition proof_8 : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₈_holds
    )).
  
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
