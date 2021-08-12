From Coq Require Import Strings.String.
From stdpp Require Import base finite gmap mapset listset_nodup.
From MatchingLogic Require Import Syntax DerivedOperators ProofSystem.
Require Import MatchingLogic.SignatureHelper.

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

  
  Inductive Label := lbl (s : string).
  
  Inductive FloatingStmt := fs (l : Label) (tc : TypeCode) (var : Variabl).
  Inductive EssentialStmt := es (l : Label) (tc : TypeCode) (lms : list MathSymbol).
  
  
  Inductive HypothesisStmt :=
  | hs_floating (fs : FloatingStmt)
  | hs_essential (es : EssentialStmt)
  .

  Inductive AxiomStmt := axs (l : Label) (tc : TypeCode) (lms : list MathSymbol).

  Inductive MMProof := pf (ll : list Label).
  
  Inductive ProvableStmt := ps (l : Label) (tc : TypeCode) (lms : list MathSymbol) (pf : MMProof).
  
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

  (* Concrete syntax printing. *)
  
  Definition IncludeStmt_toString (x : IncludeStmt) :=
    match x with
    | include_stmt s => append "$[ " (append s " $]")
    end.
  

  Definition MathSymbol_toString (x : MathSymbol) :=
    match x with
    | ms s => s
    end.
  
  Definition Constant_toString (x : Constant) :=
    match x with
    | constant s => MathSymbol_toString s
    end.

  Definition appendWith between x y :=
    append x (append between y).
  
  Definition ConstantStmt_toString (x : ConstantStmt) : string :=
    match x with
    | constant_stmt cs => append "$c " (append (foldr (appendWith " "%string) ""%string (map Constant_toString cs)) " $.")
    end.
  
  Definition Variabl_toString (x : Variabl) :=
    match x with
    | variable s => s
    end.
  
  Definition VariableStmt_toString (x : VariableStmt) : string :=
    match x with
    | vs lv => append "$v " (append (foldr (appendWith " "%string) ""%string (map Variabl_toString lv)) " $.")
    end.
  

  Definition DisjointStmt_toString (x : DisjointStmt) : string :=
    match x with
    | ds lv => append "$d " (append (foldr (appendWith " "%string) ""%string (map Variabl_toString lv)) " $.")
    end.
  
  Definition TypeCode_toString (x : TypeCode) : string :=
    match x with
    | tc c => Constant_toString c
    end.
    
  Definition Label_toString (x : Label) : string :=
    match x with
    | lbl s => s
    end.
  
  
  Definition FloatingStmt_toString (x : FloatingStmt) : string :=
    match x with
    | fs l t var => append
                      (Label_toString l)
                      (append
                         " $f "
                         (append
                            (append (TypeCode_toString t) (Variabl_toString var))
                            " $."
                         )
                      )
    end.

    Definition EssentialStmt_toString (x : EssentialStmt) : string :=
    match x with
    | es l t lms => append
                      (Label_toString l)
                      (append
                         " $e "
                         (append
                            (appendWith " "
                               (TypeCode_toString t)
                               (foldr (appendWith " "%string) ""%string (map MathSymbol_toString lms))
                            )
                            " $."
                         )
                      )
    end.

    Definition HypothesisStmt_toString (x : HypothesisStmt) : string :=
      match x with
      | hs_floating f => FloatingStmt_toString f
      | hs_essential e => EssentialStmt_toString e
      end.
    

    
    Definition AxiomStmt_toString (x : AxiomStmt) : string :=
    match x with
    | axs l t lms => append
                      (Label_toString l)
                      (append
                         " $a "
                         (append
                            (appendWith " "
                               (TypeCode_toString t)
                               (foldr (appendWith " "%string) ""%string (map MathSymbol_toString lms))
                            )
                            " $."
                         )
                      )
    end.

    Definition MMProof_toString (x : MMProof) : string :=
      match x with
      | pf ll =>  foldr (appendWith " "%string) ""%string (map Label_toString ll)
      end.

    Definition ProvableStmt_toString (x : ProvableStmt) : string :=
      match x with
      | ps l t lms p
        => append
             (Label_toString l)
             (append
                " $p "
                (append
                   (append
                      (TypeCode_toString t)
                      (foldr (appendWith " "%string) ""%string (map MathSymbol_toString lms))
                   )
                   (append " $= " (append (MMProof_toString p)  " $."))
                )
             )
      end.

    Definition AssertStmt_toString (x : AssertStmt) : string :=
      match x with
      | as_axiom a => AxiomStmt_toString a
      | as_provable p => ProvableStmt_toString p
      end.

    Fixpoint Stmt_toString (x : Stmt) : string :=
      match x with
      | stmt_block l
        => append "${ "
                  (append
                     (foldr (appendWith " "%string) ""%string (map Stmt_toString l))
                     " $}")
      | stmt_variable_stmt v => VariableStmt_toString v
      | stmt_disj_stmt d => DisjointStmt_toString d
      | stmt_hyp_stmt h => HypothesisStmt_toString h
      | stmt_assert_stmt a => AssertStmt_toString a
      end.

    Definition OutermostScopeStmt_toString (x : OutermostScopeStmt) : string :=
      match x with
      | oss_inc i => IncludeStmt_toString i
      | oss_cs c => ConstantStmt_toString c
      | oss_s s => Stmt_toString s
      end.

    Definition Database_toString (x : Database) : string :=
      foldr (appendWith "
"%string) "
"%string (map OutermostScopeStmt_toString x).


End MetaMath.

Import MetaMath.
Section gen.
  Context
    {signature : Signature}
(*    {finiteSymbols : @Finite (@symbols signature) (@sym_eq signature) }*)
    (symbolPrinter : symbols -> string)
  .
  
  Definition constantForSymbol (s : symbols) : OutermostScopeStmt :=
    oss_cs (constant_stmt [constant (ms (symbolPrinter s))]).

  Definition axiomForSymbol (s : symbols) : OutermostScopeStmt :=
    oss_s (stmt_assert_stmt (as_axiom (axs
                                         (lbl (symbolPrinter s ++ "-is-pattern"))
                                         (tc (constant (ms "#Pattern")))
                                         [(ms (symbolPrinter s))]
          ))).

  Definition constantAndAxiomForSymbol (s : symbols) : Database :=
    [constantForSymbol s; axiomForSymbol s].

  (* For now, we will only use listSet. Later we may want to use gset,
     for performance reasons; but then we will need to implement Countable
     for symbols.
   *)
  (*
  Context
    {sym_countable : @Countable symbols sym_eq}
  .

  Definition SymSet := (@gset symbols sym_eq sym_countable).
   *)

  Check listset_nodup_union.
  Definition SymSet := listset_nodup symbols.

  Existing Instance sym_eq.

  Fixpoint symbols_of (p : Pattern) : SymSet :=
    match p with
    | patt_bott | patt_free_evar _ | patt_free_svar _ | patt_bound_evar _ | patt_bound_svar _ => ∅
    | patt_sym s => {[ s ]}
    | patt_imp p1 p2 => symbols_of p1 ∪ symbols_of p2
    | patt_app p1 p2 => symbols_of p1 ∪ symbols_of p2
    | patt_exists p' => symbols_of p'
    | patt_mu p' => symbols_of p'
    end.

  Definition dependenciesForPattern (p : Pattern) : Database :=
    concat (map constantAndAxiomForSymbol (listset_nodup_car (symbols_of p))).

  Print MathSymbol.
  Fixpoint pattern2mm (p : Pattern) : list MathSymbol :=
    match p with
    | patt_sym s => [ms (symbolPrinter s)]
    | patt_imp p1 p2 =>
      let ms1 := pattern2mm p1 in
      let ms2 := pattern2mm p2 in
      [(ms "("); (ms "\imp")] ++ ms1 ++ ms2 ++ [ (ms ")")]
    | patt_app p1 p2 =>
      let ms1 := pattern2mm p1 in
      let ms2 := pattern2mm p2 in
      [(ms "("); (ms "\app")] ++ ms1 ++ ms2 ++ [ (ms ")")]
    | _ => []
    end.

  Print Label.
  Fixpoint pattern2proof (p : Pattern) : list Label :=
    match p with
    | patt_sym s => [(lbl (symbolPrinter s ++ "-is-pattern"))]
    | patt_imp p1 p2 =>
      let ms1 := pattern2proof p1 in
      let ms2 := pattern2proof p2 in
      ms1 ++ ms2 ++ [(lbl "imp-is-pattern")]
    | patt_app p1 p2 =>
      let ms1 := pattern2proof p1 in
      let ms2 := pattern2proof p2 in
      ms1 ++ ms2 ++ [(lbl "app-is-pattern")]
    | _ => []
    end.

  (*
  Definition generateSymbolAxioms : Database :=
    map (axiomForSymbol) (@enum symbols (@sym_eq signature) finiteSymbols).
*)
End gen.


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

  Definition P := (patt_and
                     (patt_or (patt_sym a) (patt_not (patt_sym a)))
                     (patt_or (patt_sym b) (patt_sym a))).

  Compute (pattern2mm symbolPrinter (patt_imp (patt_sym a) (patt_sym b))).
  Compute (pattern2proof symbolPrinter (patt_imp (patt_sym a) (patt_sym b))).

  Compute (dependenciesForPattern symbolPrinter P).
  Write MetaMath Proof Object File "myfile.mm" (Database_toString (dependenciesForPattern symbolPrinter P)).

  
End MMTest.
