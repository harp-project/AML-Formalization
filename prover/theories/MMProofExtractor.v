From Coq Require Import Strings.String Strings.Ascii.

From Equations Require Import Equations.

From stdpp Require Import base finite gmap mapset listset_nodup numbers.

From MatchingLogic Require Import Syntax DerivedOperators ProofSystem.

From MatchingLogicProver Require Import Named Metamath.

Section gen.
  Context
    {signature : Signature}
    {symbols_countable : Countable symbols}
    (symbolPrinter : symbols -> string)
    (evarPrinter : @evar variables -> string)
    (svarPrinter : @svar variables -> string)
  .
  
  Definition something (x : evar) := evarPrinter x.
  
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

  Definition SymSet := listset_nodup symbols.
  Definition NEvarSet := listset_nodup evar.
  Definition NSvarSet := listset_nodup svar.


  Fixpoint symbols_of (p : NamedPattern) : SymSet :=
    match p with
    | npatt_bott | npatt_evar _ | npatt_svar _ => ∅
    | npatt_sym s => {[ s ]}
    | npatt_imp p1 p2 => symbols_of p1 ∪ symbols_of p2
    | npatt_app p1 p2 => symbols_of p1 ∪ symbols_of p2
    | npatt_exists _ p' => symbols_of p'
    | npatt_mu _ p' => symbols_of p'
    end.

  Fixpoint nevars_of (p : NamedPattern) : NEvarSet :=
    match p with
    | npatt_bott | npatt_svar _ | npatt_sym _ => ∅
    | npatt_evar x => {[x]}
    | npatt_imp p1 p2 => nevars_of p1 ∪ nevars_of p2
    | npatt_app p1 p2 => nevars_of p1 ∪ nevars_of p2
    | npatt_exists x p' => {[x]} ∪ nevars_of p'
    | npatt_mu _ p' => nevars_of p'
    end.

  Fixpoint nsvars_of (p : NamedPattern) : NSvarSet :=
    match p with
    | npatt_bott | npatt_evar _ | npatt_sym _ => ∅
    | npatt_svar X => {[X]}
    | npatt_imp p1 p2 => nsvars_of p1 ∪ nsvars_of p2
    | npatt_app p1 p2 => nsvars_of p1 ∪ nsvars_of p2
    | npatt_exists _ p' => nsvars_of p'
    | npatt_mu X p' => {[X]} ∪ nsvars_of p'
    end.

  Definition printEvar (x : evar) : string := "evar-" ++ (evarPrinter x).
  Definition isElementVar (x : evar) : Label := lbl ((printEvar x) ++ "-is-element-var").

  Definition printSvar (X : svar) : string := "svar-" ++ (svarPrinter X).
  Definition isSetVar (X : svar) : Label := lbl ((printSvar X) ++ "-is-set-var").
  
  Definition frameAsElementVariable (x : evar) : OutermostScopeStmt :=
    oss_s (stmt_hyp_stmt (hs_floating
                            (fs
                               (isElementVar x)
                               (tc (constant (ms "#ElementVariable")))
                               (variable (printEvar x))))).

  Definition frameAsSetVariable (X : svar) : OutermostScopeStmt :=
    oss_s (stmt_hyp_stmt (hs_floating
                            (fs
                               (isSetVar X)
                               (tc (constant (ms "#SetVariable")))
                               (variable (printSvar X))))).
  
  Definition dependenciesForPattern (p : NamedPattern) : Database :=
    let sms := listset_nodup_car (symbols_of p) in
    let nevs := listset_nodup_car (nevars_of p) in
    let nsvs := listset_nodup_car (nsvars_of p) in
    (concat (map constantAndAxiomForSymbol sms))
      ++ (if decide (0 < length nevs) then
            [(oss_s (stmt_variable_stmt (vs (map (variable ∘ printEvar) nevs))))]
          else []
         )
      ++ (if decide (0 < length nsvs) then
            [(oss_s (stmt_variable_stmt (vs (map (variable ∘ printSvar) nsvs))))]
          else []
         )
      ++ (if decide (1 < length nevs) then
            [(oss_s (stmt_disj_stmt (ds (map (variable ∘ printEvar) nevs))))]
          else []
         )
      ++ (if decide (1 < length nsvs) then
            [(oss_s (stmt_disj_stmt (ds (map (variable ∘ printSvar) nsvs))))]
          else []
         )
      ++ (map frameAsElementVariable nevs)
      ++ (map frameAsSetVariable nsvs)
  .

  Fixpoint pattern2mm (p : NamedPattern) : list MathSymbol :=
    match p with
    | npatt_sym s => [ms (symbolPrinter s)] (* TODO: use printSymbol *)
    | npatt_evar x => [ms (printEvar x)]
    | npatt_svar X => [ms (printSvar X)]
    | npatt_imp p1 p2 =>
      let ms1 := pattern2mm p1 in
      let ms2 := pattern2mm p2 in
      [(ms "("); (ms "\imp")] ++ ms1 ++ ms2 ++ [ (ms ")")]
    | npatt_app p1 p2 =>
      let ms1 := pattern2mm p1 in
      let ms2 := pattern2mm p2 in
      [(ms "("); (ms "\app")] ++ ms1 ++ ms2 ++ [ (ms ")")]
    | npatt_bott => [(ms "\bot")]
    | npatt_exists x p' =>
      let msx := [ms (printEvar x)] in
      let msp' := pattern2mm p' in
      [(ms "("); (ms "\exists")] ++ msx ++ msp' ++ [(ms ")")]
    | npatt_mu X p' =>
      let msX := [ms (printSvar X)] in
      let msp' := pattern2mm p' in
      [(ms "("); (ms "\exists")] ++ msX ++ msp' ++ [(ms ")")]
    end.

  Fixpoint pattern2proof (p : NamedPattern) : list Label :=
    match p with
    | npatt_sym s => [(lbl (symbolPrinter s ++ "-is-pattern"))]
    | npatt_evar x => [(isElementVar x); (lbl "element-var-is-var"); (lbl "var-is-pattern")]
    | npatt_svar X => [(isSetVar X); (lbl "set-var-is-var"); (lbl "var-is-pattern")]                        
    | npatt_imp p1 p2 =>
      let ms1 := pattern2proof p1 in
      let ms2 := pattern2proof p2 in
      ms1 ++ ms2 ++ [(lbl "imp-is-pattern")]
    | npatt_app p1 p2 =>
      let ms1 := pattern2proof p1 in
      let ms2 := pattern2proof p2 in
      ms1 ++ ms2 ++ [(lbl "app-is-pattern")]
    | npatt_bott => [(lbl "bot-is-pattern")]
    | npatt_exists x p' =>
      let lsx := [(isElementVar x)] in
      let lsp' := pattern2proof p' in
      lsp' ++ lsx ++ [(lbl "exists-is-pattern")]
    | npatt_mu X p' =>
      let lsX := [(isSetVar X)] in
      let lsp' := pattern2proof p' in
      lsp' ++ lsX ++ [(lbl "mu-is-pattern")]
    end.

  Fixpoint proof_size' Γ (ϕ : Pattern) (pf : ML_proof_system Γ ϕ) : nat :=
    match pf with
    | hypothesis _ _ _ _ => 1
    | P1 _ _ _ _ _ => 1
    | P2 _ _ _ _ _ _ _ => 1
    | P3 _ _ _ => 1
    | Modus_ponens _ _ _ _ _ pf1 pf2 => 1 + proof_size' _ _ pf1 + proof_size' _ _ pf2
    | Ex_quan _ _ _ _ => 1
    | Ex_gen _ _ _ _ _ _ pf' _ => 1 + proof_size' _ _ pf'
    | Prop_bott_left _ _ _ => 1
    | Prop_bott_right _ _ _ => 1
    | Prop_disj_left _ _ _ _ _ _ _ => 1
    | Prop_disj_right _ _ _ _ _ _ _ => 1
    | Prop_ex_left _ _ _ _ _ => 1
    | Prop_ex_right _ _ _ _ _ => 1
    | Framing_left _ _ _ _ _ pf' => 1 + proof_size' _ _ pf'
    | Framing_right _ _ _ _ _ pf' => 1 + proof_size' _ _ pf'
    | Svar_subst _ _ _ _ _ _ pf' => 1 + proof_size' _ _ pf'
    | Pre_fixp _ _ _ => 1
    | Knaster_tarski _ _ _ _ pf' => 1 + proof_size' _ _ pf'
    | Existence _ => 1
    | Singleton_ctx _ _ _ _ _ _ => 1
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

  (* (exists x, x) -> exists x, (exists y, y)  *)
  (* (exists, 0) -> (exists, exists, 0)  *)
  (* (exists x, x) -> (phi -> (exists y, y)) *)

  Print Ex_quan.

 Equations? proof2proof'
            Γ
            (acc : list Label)
            (pfs : list ({ϕ : Pattern & ML_proof_system Γ ϕ} + Label))
    : list Label
    by wf (proof2proof'_stack_size Γ pfs) lt :=
    
    proof2proof' Γ acc [] := reverse acc ;
    
    proof2proof' Γ acc ((inr l)::pfs')
      := proof2proof' Γ (l::acc) pfs' ;
    
    proof2proof' Γ acc ((inl (existT ϕ (P1 _ p q _ _)))::pfs')
      := proof2proof'
           Γ
           ([lbl "proof-rule-prop-1"]
              ++ (reverse (pattern2proof (to_NamedPattern2 q)))
              ++ (reverse (pattern2proof (to_NamedPattern2 p)))
              ++ acc)
           pfs' ;
    
    proof2proof' Γ acc ((inl (existT ϕ (P2 _ p q r _ _ _)))::pfs')
      := proof2proof'
           Γ
           ([lbl "proof-rule-prop-2"]
              ++ (reverse (pattern2proof (to_NamedPattern2 r)))
              ++ (reverse (pattern2proof (to_NamedPattern2 q)))
              ++ (reverse (pattern2proof (to_NamedPattern2 p)))
              ++ acc)
           pfs' ;
    
    proof2proof' Γ acc ((inl (existT ϕ (P3 _ p _)))::pfs')
      := proof2proof'
           Γ
           ([lbl "proof-rule-prop-3"]
              ++ (reverse (pattern2proof (to_NamedPattern2 p)))
              ++ acc)
           pfs' ;

    proof2proof' Γ acc ((inl (existT _ (Modus_ponens _ p q _ _ pfp pfpiq)))::pfs')
      := proof2proof'
           Γ
           ((reverse (pattern2proof (to_NamedPattern2 q)))
              ++ (reverse (pattern2proof (to_NamedPattern2 p)))
              ++ acc)
           ((inl (existT _ pfpiq))::(inl (existT _ pfp))::(inr (lbl "proof-rule-mp"))::pfs') ;

    proof2proof' Γ acc ((inl (existT ϕ (Ex_quan _ p y _)))::pfs')
      := proof2proof'
           Γ
           ([lbl "proof-rule-exists"]
              ++ (reverse (pattern2proof (to_NamedPattern2 (instantiate p (patt_free_evar y)))))
              ++ (reverse (pattern2proof (to_NamedPattern2 p)))
              ++ acc)
           pfs' ;

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
    - unfold proof2proof'_stack_size. simpl. lia.
    - unfold proof2proof'_stack_size. simpl. lia.
  Defined.

  Definition proof2proof Γ (ϕ : Pattern) (pf : ML_proof_system Γ ϕ) : list Label :=
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
  
  Definition proof2database Γ (ϕ : Pattern) (proof : ML_proof_system Γ ϕ) : Database :=
    let named := to_NamedPattern2 ϕ in
    [oss_inc (include_stmt "mm/matching-logic.mm")] ++
    (dependenciesForPattern named)
      ++ [oss_s (stmt_assert_stmt (as_provable (ps
                                                  (lbl "the-proof")
                                                  (tc (constant (ms "|-")))
                                                  (pattern2mm named)
                                                  (pf (proof2proof Γ ϕ proof))
         )))].
  
  
End gen.
