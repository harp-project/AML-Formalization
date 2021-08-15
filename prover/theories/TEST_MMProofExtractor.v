From Coq Require Import Strings.String.
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

  Definition ϕ₁ := (patt_sym a) ---> ((patt_sym b) ---> (patt_sym a)).

  Lemma ϕ₁_holds:
    (Ensembles.Empty_set _) ⊢ ϕ₁.
  Proof.
    apply P1; auto.
  Defined.
  

  Definition proof₁ : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₁_holds
    )).
  (*Compute proof₁.*)

  Definition A := patt_sym a.
  Definition B := patt_sym b.
  Definition C := patt_sym c.

  Definition ϕ₂ : Pattern := B or ¬ B.

  Lemma ϕ₂_holds:
    (Ensembles.Empty_set _) ⊢ ϕ₂.
  Proof.
    toMyGoal.
  




  (* We put these at the end so that we do not accidentally run it during an interactive session. *)
  Write MetaMath Proof Object File "proof_1.mm" proof₁.

End MMTest.

