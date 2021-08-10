From Coq Require Import String.
From MatchingLogic Require Import Syntax ProofSystem.
From MatchingLogicProver Require Import MMProofExtractorLoader.



Module MetaMath.

  Inductive IncludeStmt := include_stmt (s : string).

  Inductive MathSymbol := ms (s : string).
  Inductive Constant := constant (ms : MathSymbol).
  Inductive ConstantStmt := constant_stmt (cs : list Constant).
  Inductive Variabl := variable (s : string).
  Inductive VariableStmt := vs (lv : list Variabl).
  Inductive DisjointStmt := ds (lv : list Variabl).
  Inductive TypeCode := tc (c : Constant).

  Inductive FloatingStmt := fs (tc : TypeCode) (var : Variabl).
  Inductive EssentialStmt := es (tc : TypeCode) (lms : list MathSymbol).
  
  
  Inductive HypothesisStmt :=
  | hs_floating (fs : FloatingStmt)
  | hs_esential (es : EssentialStmt)
  .

  Inductive AxiomStmt := axs (tc : TypeCode) (lms : list MathSymbol).

  Inductive Label := lbl (s : string).
  Inductive MMProof := pf (ll : list Label).
  
  Inductive ProvableStmt := ps (tc : TypeCode) (lms : list MathSymbol) (pf : MMProof).
  
  Inductive AssertStmt :=
  | as_axiom (axs : AxiomStmt)
  | as_provable (ps : ProvableStmt)
  .
  
  Inductive Stmt :=
  | stmt_block (ls : list Stmt)
  | stmt_variable_stmt (vs : VariableStmt)
  | stmt_disj_stmt (ds : DisjointStmt)
  | stmt_hyp_stmt (hs : HypothesisStmt)
  | stmt_assert_stmt (ass : AssertStmt).
  
  Inductive OutermostScopeStmt :=
  | oss_inc (incs : IncludeStmt)
  | oss_cs (cs : ConstantStmt)
  | oss_s (st : Stmt)
  .
  
  Definition Database := list OutermostScopeStmt.

End MetaMath.

  







Write MetaMath Proof Object File "myfile.mm".

HelloWorld.

Lemma test : True.
Proof.
hello_world.
Abort.
HelloWorld.
