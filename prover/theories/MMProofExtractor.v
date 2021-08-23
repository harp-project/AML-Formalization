From Coq Require Import Strings.String.

From Equations Require Import Equations.

From stdpp Require Import base finite gmap mapset listset_nodup.

From MatchingLogic Require Import Syntax DerivedOperators ProofSystem.

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
                      (append (TypeCode_toString t) " ")
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
    | patt_bott => [(ms "\bot")]
    | _ => []
    end.

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
    | patt_bott => [(lbl "bot-is-pattern")]
    | _ => []
    end.

  Fixpoint proof_size' (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_system Γ ϕ) : nat :=
    match pf with
    | hypothesis _ _ _ _ => 1
    | P1 _ _ _ _ _ => 1
    | P2 _ _ _ _ _ _ _ => 1
    | P3 _ _ _ => 1
    | Modus_ponens _ _ _ _ _ pf1 pf2 => 1 + proof_size' _ _ pf1 + proof_size' _ _ pf2
    | Ex_quan _ _ _ => 1
    | Ex_gen _ _ _ _ _ _ pf' _ => 1 + proof_size' _ _ pf'
    | Prop_bott_left _ _ _ => 1
    | Prop_bott_right _ _ _ => 1
    | Prop_disj_left _ _ _ _ _ _ _ => 1
    | Prop_disj_right _ _ _ _ _ _ _ => 1
    | Prop_ex_left _ _ _ _ _ => 1
    | Prop_ex_right _ _ _ _ _ => 1
    | Framing_left _ _ _ _ pf' => 1 + proof_size' _ _ pf'
    | Framing_right _ _ _ _ pf' => 1 + proof_size' _ _ pf'
    | Svar_subst _ _ _ _ _ _ pf' => 1 + proof_size' _ _ pf'
    | Pre_fixp _ _ => 1
    | Knaster_tarski _ _ _ pf' => 1 + proof_size' _ _ pf'
    | Existence _ => 1
    | Singleton_ctx _ _ _ _ _ => 1
    end.

  Definition proof_size'' Γ (x : {ϕ : Pattern & ML_proof_system Γ ϕ}) :=
    proof_size' Γ (projT1 x) (projT2 x).

  Definition proof2proof'_stack Γ := list ({ϕ : Pattern & ML_proof_system Γ ϕ} + Label).
  
  Definition proof2proof'_stack_size Γ (s : proof2proof'_stack Γ)
    := (fold_right
          plus
          0
          (map
             (fun it =>
                match it with
                | inl p => 2 * proof_size'' Γ p
                | inr _ => 1          
                end
             )
             s
          )
       ).

  (*
  Check Modus_ponens.
  Print sum.*)
  Equations? proof2proof'
            (Γ : Theory)
            (prefix : list Label)
            (pfs : list ({ϕ : Pattern & ML_proof_system Γ ϕ} + Label))
    : list Label
    by wf (proof2proof'_stack_size Γ pfs) lt :=
    
    proof2proof' Γ prefix [] := prefix ;
    
    proof2proof' Γ prefix ((inr l)::pfs')
      := proof2proof' Γ (prefix ++ [l]) pfs' ;
    
    proof2proof' Γ prefix ((inl (existT ϕ (P1 _ p q _ _)))::pfs')
      := proof2proof'
           Γ
           (prefix ++ (pattern2proof p) ++ (pattern2proof q) ++ [lbl "proof-rule-prop-1"])
           pfs' ;
    
    proof2proof' Γ prefix ((inl (existT ϕ (P2 _ p q r _ _ _)))::pfs')
      := proof2proof'
           Γ
           (prefix ++ (pattern2proof p) ++ (pattern2proof q) ++ (pattern2proof r) ++ [lbl "proof-rule-prop-2"])
           pfs' ;
    
    proof2proof' Γ prefix ((inl (existT ϕ (P3 _ p _)))::pfs')
      := proof2proof'
           Γ
           (prefix ++ (pattern2proof p) ++ [lbl "proof-rule-prop-3"])
           pfs' ;

    proof2proof' Γ prefix ((inl (existT _ (Modus_ponens _ p q _ _ pfp pfpiq)))::pfs')
      := proof2proof'
           Γ
           (prefix ++ (pattern2proof p) ++ (pattern2proof q))
           ((inl (existT _ pfpiq))::(inl (existT _ pfp))::(inr (lbl "proof-rule-mp"))::pfs') ;

    proof2proof' Γ prefix ((inl _)::_) := []
  .
  Proof.
    - unfold proof2proof'_stack_size. simpl. lia.
    - unfold proof2proof'_stack_size. simpl. lia.
    - unfold proof2proof'_stack_size. simpl. lia.
    - unfold proof2proof'_stack_size.
      rewrite !map_cons. simpl.
      unfold proof_size''. simpl.
      simpl.
      remember (proof_size' Γ (patt_imp p q) pfpiq) as A.
      remember (proof_size' Γ p pfp) as B.
      remember ((foldr Init.Nat.add 0
                       (map
                          (λ it : {ϕ : Pattern & ML_proof_system Γ ϕ} + Label,
                                  match it with
                                  | inl p0 => proof_size' Γ (projT1 p0) (projT2 p0) + (proof_size' Γ (projT1 p0) (projT2 p0) + 0)
                                  | inr _ => 1
                                  end) pfs'))) as C.
      lia.
    - unfold proof2proof'_stack_size.
      simpl. lia.
  Defined.
  (*Transparent proof2proof'.*)

  Check proof2proof'.
  Definition proof2proof (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_system Γ ϕ) : list Label :=
    proof2proof' Γ [] [(inl (existT ϕ pf))].
  
  
  (*
  Fixpoint proof2proof (Γ : Theory) (ϕ : Pattern) (pf : ML_proof_system Γ ϕ) : list Label :=
    match pf as _ return list Label with
    | P1 _ p q wfp wfq => pattern2proof p ++ pattern2proof q ++ [lbl "proof-rule-prop-1"]
    | P2 _ p q r wfp wfq wfr =>
      pattern2proof p ++ pattern2proof q ++ pattern2proof r ++ [lbl "proof-rule-prop-2"]
    | P3 _ p wfp => pattern2proof p ++ [lbl "proof-rule-prop-3"]
    | Modus_ponens _ p q wfp wfpiq pfp pfpiq =>
      (pattern2proof p)
        ++ (pattern2proof q)
        ++ (proof2proof Γ _ pfpiq)
        ++ (proof2proof Γ _ pfp)
        ++ [lbl "proof-rule-mp"]
    | _ => []
    end.
   *)
  
  Definition proof2database (Γ : Theory) (ϕ : Pattern) (proof : ML_proof_system Γ ϕ) : Database :=
    [oss_inc (include_stmt "mm/matching-logic.mm")] ++
    (dependenciesForPattern ϕ)
      ++ [oss_s (stmt_assert_stmt (as_provable (ps
                                                  (lbl "the-proof")
                                                  (tc (constant (ms "|-")))
                                                  (pattern2mm ϕ)
                                                  (pf (proof2proof Γ ϕ proof))
         )))].
  
  
End gen.
