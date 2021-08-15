From Coq Require Import Strings.String.
From stdpp Require Export base.
From MatchingLogic Require Import Syntax SignatureHelper ProofSystem.
From MatchingLogicProver Require Import MMProofExtractor.


Module MMTest.
  Import MatchingLogic.Syntax.Notations.
  Import MatchingLogic.DerivedOperators.Notations.

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

  Definition ϕ₁ := patt_imp (patt_sym a) (patt_imp (patt_sym b) (patt_sym a)).

  Lemma P1_holds:
    ML_proof_system (Ensembles.Empty_set _) ϕ₁.
  Proof.
    apply P1; auto.
  Defined.
  

  Definition mm_proof : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          P1_holds
    )).
  Compute mm_proof.
  Write MetaMath Proof Object File "proof_1.mm" mm_proof.

  
End MMTest.

