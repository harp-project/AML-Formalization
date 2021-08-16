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

  
  Definition A := patt_sym a.
  Definition B := patt_sym b.
  Definition C := patt_sym c.
  
  Definition ϕ₁ := A ---> (B ---> A).

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


  Definition ϕ₂ := (A ---> (B ---> C)) ---> (A ---> B) ---> (A ---> C).

  Lemma ϕ₂_holds:
    (Ensembles.Empty_set _) ⊢ ϕ₂.
  Proof.
    apply P2; auto.
  Defined.

  Definition proof₂ : string :=
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
    (Ensembles.Empty_set _) ⊢ ϕ₃.
  Proof.
    apply P3; auto.
  Defined.

  Definition proof₃ : string :=
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
    (Ensembles.Empty_set _) ⊢ ϕ₄.
  Proof.
    apply A_impl_A. auto.
  Defined.

  Definition proof₄ : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₄_holds
    )).
  
  (*Compute proof₄.*)

  Definition ϕ₅ := (A ---> B) <---> (¬ A or B).

  Lemma ϕ₅_holds:
    (Ensembles.Empty_set _) ⊢ ϕ₅.
  Proof.
    apply impl_iff_notp_or_q; auto.
  Defined.

  (* Takes forever *)
  (*Compute ϕ₅_holds.*)


  Definition proof₅ : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₅_holds
    )).
  (*
  Print Opaque Dependencies proof₅.
  Compute proof₅. (* Stack overflow *)
   *)
  (* Time Eval compute in proof₅. *) (* Stack overflow *)

  Definition ϕ₆ := (A ---> ¬ ¬ B) ---> (A ---> B).

  Lemma ϕ₆_holds:
    (Ensembles.Empty_set _) ⊢ ϕ₆.
  Proof.
    apply A_impl_not_not_B; auto.
  Defined.

  (* Finished transaction in 42.649 secs (42.411u,0.203s) (successful) *)
  (* Time Eval vm_compute in ϕ₆_holds. *)


  Definition proof₆ : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₆_holds
    )).


  Definition ϕ₇ := ((B ---> C) ---> ((A ---> B) ---> (A ---> C))).

  Lemma ϕ₇_holds:
    (Ensembles.Empty_set _) ⊢ ϕ₇.
  Proof.
    apply prf_weaken_conclusion; auto.
  Defined.

  (* Finished transaction in 42.649 secs (42.411u,0.203s) (successful) *)
  (* Time Eval vm_compute in ϕ₆_holds. *)


  Definition proof₇ : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₇_holds
    )).

  Compute proof₇.


  
  Definition ϕ₈ := (A and B) ---> A.

  Lemma ϕ₈_holds:
    (Ensembles.Empty_set _) ⊢ ϕ₈.
  Proof.
    apply pf_conj_elim_l; auto.
  Defined.

  (* Finished transaction in 42.649 secs (42.411u,0.203s) (successful) *)
  (* Time Eval vm_compute in ϕ₆_holds. *)


  Definition proof₈ : string :=
    (Database_toString
       (proof2database
          symbolPrinter
          _
          _
          ϕ₈_holds
    )).

  (* Takes forever *)
  (*Compute ϕ₈_holds. *)
  Eval native_compute in proof₈.

(*
  Time Eval vm_compute in proof₆.
  Time Eval lazy in proof₆.
  Set NativeCompute Profiling.
  Set NativeCompute Timing.
  Time Eval native_compute in proof₆.

  *)
  (* Lets crash now, but hopefully we will have a profile if we run coqc under perf.*)
  (*Time Eval compute in proof₅.*)
  
  


(*
  (* We put these at the end so that we do not accidentally run it during an interactive session. *)
  Write MetaMath Proof Object File "proof_1.mm" proof₁.
  Write MetaMath Proof Object File "proof_2.mm" proof₂.
  Write MetaMath Proof Object File "proof_3.mm" proof₃.
  Write MetaMath Proof Object File "proof_4.mm" proof₄.

  (* Stack overflow *)
  (*Write MetaMath Proof Object File "proof_5.mm" proof₅.*)

  Write MetaMath Proof Object File "proof_6.mm" proof₆.
*)
End MMTest.

