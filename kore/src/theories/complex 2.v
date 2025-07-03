
From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.
Require Import BuiltIns DVParsers.

From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope string_scope.
Open Scope hlist_scope.

      Module TheorySyntax.


        Inductive Ksorts :=
        | SortK
        | SortKItem
        | SortKCell
        | SortIds
        | SortGeneratedTopCell
        | SortStateCell
        | SortGeneratedCounterCell
        | SortAExp
        | SortMap
        | SortString
        | SortId
        | SortBlock
        | SortBExp
        | SortInt
        | SortPgm
        | SortKResult
        | SortTCell
        | SortStmt
        | SortBool
        .
        Instance Ksorts_eq_dec : EqDecision Ksorts.
        Proof. solve_decision. Defined.
  (*      Program Instance Ksorts_countable : finite.Finite Ksorts :=
        {
          enum := [SortK; SortKItem; SortKCell; SortIds; SortGeneratedTopCell; SortStateCell; SortGeneratedCounterCell; SortAExp; SortMap; SortString; SortId; SortBlock; SortBExp; SortInt; SortPgm; SortKResult; SortTCell; SortStmt; SortBool]
        }.
        Next Obligation.
          compute_done.
        Defined.
        Final Obligation.
          intros. destruct x; set_solver.
        Defined.
  *)



  Inductive Ksyms :=
  | kseq (* q *)
  | dotk (* k *)
  | BangUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp (* !__IMP-SYNTAX_BExp_BExp *)
  | Hash_systemResult (* #systemResult *)
  | UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_Int (* -__IMP-SYNTAX_AExp_Int *)
  | Stop_List_LBraQuotUndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids_QuotRBraUnds_Ids (* .List{"_,__IMP-SYNTAX_Ids_Id_Ids"}_Ids *)
  | UndsPercUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _%__IMP-SYNTAX_AExp_AExp_AExp *)
  | UndsAnd_And_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp_Unds_BExp (* _&&__IMP-SYNTAX_BExp_BExp_BExp *)
  | UndsStarUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _*__IMP-SYNTAX_AExp_AExp_AExp *)
  | UndsPlusUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _+__IMP-SYNTAX_AExp_AExp_AExp *)
  | UndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids (* _,__IMP-SYNTAX_Ids_Id_Ids *)
  | Unds___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _-__IMP-SYNTAX_AExp_AExp_AExp *)
  | UndsSlshUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _/__IMP-SYNTAX_AExp_AExp_AExp *)
  | Unds_LT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _<=__IMP-SYNTAX_BExp_AExp_AExp *)
  | Unds_LT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _<__IMP-SYNTAX_BExp_AExp_AExp *)
  | UndsEqlsEqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _==__IMP-SYNTAX_BExp_AExp_AExp *)
  | Unds_GT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _>=__IMP-SYNTAX_BExp_AExp_AExp *)
  | Unds_GT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _>__IMP-SYNTAX_BExp_AExp_AExp *)
  | Unds_andBool_Unds_ (* _andBool_ *)
  | assign (* assign *)
  | block (* block *)
  | emptyblock (* emptyblock *)
  | if_LParUndsRParUnds_else_UndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block_Unds_Block (* if(_)_else__IMP-SYNTAX_Stmt_BExp_Block_Block *)
  | int_UndsSClnUndsUnds_IMP_SYNTAX_Unds_Pgm_Unds_Ids_Unds_Stmt (* int_;__IMP-SYNTAX_Pgm_Ids_Stmt *)
  | notBool_Unds_ (* notBool_ *)
  | seqcomp (* seqcomp *)
  | while_LParUndsRParUndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block (* while(_)__IMP-SYNTAX_Stmt_BExp_Block *)
  .
  (*
  Instance Ksyms_eq_dec : EqDecision Ksyms.
  Proof. solve_decision. Defined.
  Program Instance Ksyms_countable : finite.Finite Ksyms :=
  {
    enum := [kseq (* q *); dotk (* k *); BangUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp (* !__IMP-SYNTAX_BExp_BExp *); Hash_systemResult (* #systemResult *); UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_Int (* -__IMP-SYNTAX_AExp_Int *); Stop_List_LBraQuotUndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids_QuotRBraUnds_Ids (* .List{"_,__IMP-SYNTAX_Ids_Id_Ids"}_Ids *); UndsPercUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _%__IMP-SYNTAX_AExp_AExp_AExp *); UndsAnd_And_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp_Unds_BExp (* _&&__IMP-SYNTAX_BExp_BExp_BExp *); UndsStarUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _*__IMP-SYNTAX_AExp_AExp_AExp *); UndsPlusUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _+__IMP-SYNTAX_AExp_AExp_AExp *); UndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids (* _,__IMP-SYNTAX_Ids_Id_Ids *); Unds___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _-__IMP-SYNTAX_AExp_AExp_AExp *); UndsSlshUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp (* _/__IMP-SYNTAX_AExp_AExp_AExp *); Unds_LT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _<=__IMP-SYNTAX_BExp_AExp_AExp *); Unds_LT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _<__IMP-SYNTAX_BExp_AExp_AExp *); UndsEqlsEqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _==__IMP-SYNTAX_BExp_AExp_AExp *); Unds_GT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _>=__IMP-SYNTAX_BExp_AExp_AExp *); Unds_GT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp (* _>__IMP-SYNTAX_BExp_AExp_AExp *); Unds_andBool_Unds_ (* _andBool_ *); assign (* assign *); block (* block *); emptyblock (* emptyblock *); if_LParUndsRParUnds_else_UndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block_Unds_Block (* if(_)_else__IMP-SYNTAX_Stmt_BExp_Block_Block *); int_UndsSClnUndsUnds_IMP_SYNTAX_Unds_Pgm_Unds_Ids_Unds_Stmt (* int_;__IMP-SYNTAX_Pgm_Ids_Stmt *); notBool_Unds_ (* notBool_ *); seqcomp (* seqcomp *); while_LParUndsRParUndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block (* while(_)__IMP-SYNTAX_Stmt_BExp_Block *); DVSortBooltrue; DVSortBoolfalse]
  }.
  Next Obligation.
    compute_done.
  Defined.
  Final Obligation.
    intros. destruct x; set_solver.
  Defined.
  *)

        Inductive KSubsort : CRelationClasses.crelation Ksorts :=
|  inj_SortAExp_SortKItem : KSubsort SortAExp SortKItem
|  inj_SortKCell_SortKItem : KSubsort SortKCell SortKItem
|  inj_SortStmt_SortKItem : KSubsort SortStmt SortKItem
|  inj_SortBExp_SortKItem : KSubsort SortBExp SortKItem
|  inj_SortPgm_SortKItem : KSubsort SortPgm SortKItem
|  inj_SortMap_SortKItem : KSubsort SortMap SortKItem
|  inj_SortIds_SortKItem : KSubsort SortIds SortKItem
|  inj_SortBool_SortKItem : KSubsort SortBool SortKItem
|  inj_SortBlock_SortKItem : KSubsort SortBlock SortKItem
|  inj_SortKResult_SortKItem : KSubsort SortKResult SortKItem
|  inj_SortInt_SortKItem : KSubsort SortInt SortKItem
|  inj_SortGeneratedCounterCell_SortKItem : KSubsort SortGeneratedCounterCell SortKItem
|  inj_SortString_SortKItem : KSubsort SortString SortKItem
|  inj_SortStateCell_SortKItem : KSubsort SortStateCell SortKItem
|  inj_SortGeneratedTopCell_SortKItem : KSubsort SortGeneratedTopCell SortKItem
|  inj_SortId_SortKItem : KSubsort SortId SortKItem
|  inj_SortTCell_SortKItem : KSubsort SortTCell SortKItem
|  inj_SortBool_SortBExp : KSubsort SortBool SortBExp
|  inj_SortBlock_SortStmt : KSubsort SortBlock SortStmt
|  inj_SortInt_SortAExp : KSubsort SortInt SortAExp
|  inj_SortId_SortAExp : KSubsort SortId SortAExp
|  inj_SortInt_SortKResult : KSubsort SortInt SortKResult
|  inj_SortBool_SortKResult : KSubsort SortBool SortKResult
.

      Goal forall s1 s2 s3, KSubsort s1 s2 -> KSubsort s2 s3 -> KSubsort s1 s3.
      Proof.
        intros ??? H1 H2; inversion H1; inversion H2; try constructor; subst; try discriminate.
      Defined.
      Goal forall s1 s2, KSubsort s1 s2 -> KSubsort s2 s1 -> s1 = s2.
      Proof.
        intros ?? H H0; inversion H; subst; inversion H0; subst.
      Defined.


Program Instance TheorySignature : Signature := {|
  sorts := {|
    sort := Ksorts;
    subsort := KSubsort;
  |};
  variables := StringVariables;
  symbols := {|
    symbol := Ksyms;
    arg_sorts σ :=
      match σ with
                | kseq => [SortKItem;SortK]
  | dotk => []
  | BangUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp => [SortBExp]
  | Hash_systemResult => [SortInt;SortString;SortString]
  | UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_Int => [SortInt]
  | Stop_List_LBraQuotUndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids_QuotRBraUnds_Ids => []
  | UndsPercUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | UndsAnd_And_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp_Unds_BExp => [SortBExp;SortBExp]
  | UndsStarUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | UndsPlusUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | UndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids => [SortId;SortIds]
  | Unds___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | UndsSlshUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | Unds_LT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | Unds_LT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | UndsEqlsEqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | Unds_GT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | Unds_GT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => [SortAExp;SortAExp]
  | Unds_andBool_Unds_ => [SortBool;SortBool]
  | assign => [SortId;SortAExp]
  | block => [SortStmt]
  | emptyblock => []
  | if_LParUndsRParUnds_else_UndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block_Unds_Block => [SortBExp;SortBlock;SortBlock]
  | int_UndsSClnUndsUnds_IMP_SYNTAX_Unds_Pgm_Unds_Ids_Unds_Stmt => [SortIds;SortStmt]
  | notBool_Unds_ => [SortBool]
  | seqcomp => [SortStmt;SortStmt]
  | while_LParUndsRParUndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block => [SortBExp;SortBlock]
      end;
    ret_sort σ :=
      match σ with
                | kseq => SortK
  | dotk => SortK
  | BangUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp => SortBExp
  | Hash_systemResult => SortKItem
  | UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_Int => SortAExp
  | Stop_List_LBraQuotUndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids_QuotRBraUnds_Ids => SortIds
  | UndsPercUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => SortAExp
  | UndsAnd_And_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp_Unds_BExp => SortBExp
  | UndsStarUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => SortAExp
  | UndsPlusUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => SortAExp
  | UndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids => SortIds
  | Unds___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => SortAExp
  | UndsSlshUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp => SortAExp
  | Unds_LT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => SortBExp
  | Unds_LT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => SortBExp
  | UndsEqlsEqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => SortBExp
  | Unds_GT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => SortBExp
  | Unds_GT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp => SortBExp
  | Unds_andBool_Unds_ => SortBool
  | assign => SortStmt
  | block => SortBlock
  | emptyblock => SortBlock
  | if_LParUndsRParUnds_else_UndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block_Unds_Block => SortStmt
  | int_UndsSClnUndsUnds_IMP_SYNTAX_Unds_Pgm_Unds_Ids_Unds_Stmt => SortPgm
  | notBool_Unds_ => SortBool
  | seqcomp => SortStmt
  | while_LParUndsRParUndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block => SortStmt
      end;
  |};
|}.

Definition Theory_behavioural : @Theory TheorySignature :=
  PropSet (fun pat =>

(* Unds_andBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( (  kore_dv _ "false" ) and ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen1" ) ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen1" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarB"; kore_dv _ "true"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "Var'Unds'Gen0"; kore_dv _ "false"⟩ ) =k{R} ( ( kore_dv _ "false" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv _ "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* notBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv _ "false" ) ) and ( Top{R} ) ) ) --->ₖ ( ( notBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"⟩ ) =k{R} ( ( kore_dv _ "true" ) and ( Top{SortBool} ) ) ) )) \/

(* notBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv _ "true" ) ) and ( Top{R} ) ) ) --->ₖ ( ( notBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"⟩ ) =k{R} ( ( kore_dv _ "false" ) and ( Top{SortBool} ) ) ) ))
  ).

Definition Theory_functional : @Theory TheorySignature :=
  PropSet (fun pat =>

(* BangUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp is functional *)
(exists R, pat = existT R (kore_exists SortBExp (( kore_bevar (In_nil) ) =k{R} ( BangUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp ⋅ ⟨@kore_fevar _ _ _ SortBExp "K0"⟩ )) )) \/

(* Hash_systemResult is functional *)
(exists R, pat = existT R (kore_exists SortKItem (( kore_bevar (In_nil) ) =k{R} ( Hash_systemResult ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortString "K1"; @kore_fevar _ _ _ SortString "K2"⟩ )) )) \/

(* UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_Int is functional *)
(exists R, pat = existT R (kore_exists SortAExp (( kore_bevar (In_nil) ) =k{R} ( UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"⟩ )) )) \/

(* Stop_List_LBraQuotUndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids_QuotRBraUnds_Ids is functional *)
(exists R, pat = existT R (kore_exists SortIds (( kore_bevar (In_nil) ) =k{R} ( Stop_List_LBraQuotUndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids_QuotRBraUnds_Ids ⋅ ⟨⟩ )) )) \/

(* UndsPercUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortAExp (( kore_bevar (In_nil) ) =k{R} ( UndsPercUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* UndsAnd_And_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp_Unds_BExp is functional *)
(exists R, pat = existT R (kore_exists SortBExp (( kore_bevar (In_nil) ) =k{R} ( UndsAnd_And_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp_Unds_BExp ⋅ ⟨@kore_fevar _ _ _ SortBExp "K0"; @kore_fevar _ _ _ SortBExp "K1"⟩ )) )) \/

(* UndsStarUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortAExp (( kore_bevar (In_nil) ) =k{R} ( UndsStarUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* UndsPlusUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortAExp (( kore_bevar (In_nil) ) =k{R} ( UndsPlusUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* UndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids is functional *)
(exists R, pat = existT R (kore_exists SortIds (( kore_bevar (In_nil) ) =k{R} ( UndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids ⋅ ⟨@kore_fevar _ _ _ SortId "K0"; @kore_fevar _ _ _ SortIds "K1"⟩ )) )) \/

(* Unds___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortAExp (( kore_bevar (In_nil) ) =k{R} ( Unds___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* UndsSlshUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortAExp (( kore_bevar (In_nil) ) =k{R} ( UndsSlshUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* Unds_LT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortBExp (( kore_bevar (In_nil) ) =k{R} ( Unds_LT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* Unds_LT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortBExp (( kore_bevar (In_nil) ) =k{R} ( Unds_LT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* UndsEqlsEqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortBExp (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsEqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* Unds_GT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortBExp (( kore_bevar (In_nil) ) =k{R} ( Unds_GT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* Unds_GT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp is functional *)
(exists R, pat = existT R (kore_exists SortBExp (( kore_bevar (In_nil) ) =k{R} ( Unds_GT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp ⋅ ⟨@kore_fevar _ _ _ SortAExp "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* Unds_andBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* assign is functional *)
(exists R, pat = existT R (kore_exists SortStmt (( kore_bevar (In_nil) ) =k{R} ( assign ⋅ ⟨@kore_fevar _ _ _ SortId "K0"; @kore_fevar _ _ _ SortAExp "K1"⟩ )) )) \/

(* block is functional *)
(exists R, pat = existT R (kore_exists SortBlock (( kore_bevar (In_nil) ) =k{R} ( block ⋅ ⟨@kore_fevar _ _ _ SortStmt "K0"⟩ )) )) \/

(* emptyblock is functional *)
(exists R, pat = existT R (kore_exists SortBlock (( kore_bevar (In_nil) ) =k{R} ( emptyblock ⋅ ⟨⟩ )) )) \/

(* if_LParUndsRParUnds_else_UndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block_Unds_Block is functional *)
(exists R, pat = existT R (kore_exists SortStmt (( kore_bevar (In_nil) ) =k{R} ( if_LParUndsRParUnds_else_UndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block_Unds_Block ⋅ ⟨@kore_fevar _ _ _ SortBExp "K0"; @kore_fevar _ _ _ SortBlock "K1"; @kore_fevar _ _ _ SortBlock "K2"⟩ )) )) \/

(* int_UndsSClnUndsUnds_IMP_SYNTAX_Unds_Pgm_Unds_Ids_Unds_Stmt is functional *)
(exists R, pat = existT R (kore_exists SortPgm (( kore_bevar (In_nil) ) =k{R} ( int_UndsSClnUndsUnds_IMP_SYNTAX_Unds_Pgm_Unds_Ids_Unds_Stmt ⋅ ⟨@kore_fevar _ _ _ SortIds "K0"; @kore_fevar _ _ _ SortStmt "K1"⟩ )) )) \/

(* notBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( notBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"⟩ )) )) \/

(* seqcomp is functional *)
(exists R, pat = existT R (kore_exists SortStmt (( kore_bevar (In_nil) ) =k{R} ( seqcomp ⋅ ⟨@kore_fevar _ _ _ SortStmt "K0"; @kore_fevar _ _ _ SortStmt "K1"⟩ )) )) \/

(* while_LParUndsRParUndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block is functional *)
(exists R, pat = existT R (kore_exists SortStmt (( kore_bevar (In_nil) ) =k{R} ( while_LParUndsRParUndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block ⋅ ⟨@kore_fevar _ _ _ SortBExp "K0"; @kore_fevar _ _ _ SortBlock "K1"⟩ )) ))
  ).

      End TheorySyntax.
      Module TheorySemantics.
        Import TheorySyntax.

      Inductive SortK_carrier : Set :=
 | c_dotk
 | c_kseq(ymgtc:SortKItem_carrier) (tyzdg:SortK_carrier)
with SortKItem_carrier : Set :=
 | c__Hash_systemResult(zyjti:SortInt_carrier) (bvall:SortString_carrier) (kgjxz:SortString_carrier)
 | c_inj_SortAExp_SortKItem (b : SortAExp_carrier)
 | c_inj_SortBExp_SortKItem (b : SortBExp_carrier)
 | c_inj_SortBlock_SortKItem (b : SortBlock_carrier)
 | c_inj_SortBool_SortKItem (b : SortBool_carrier)
 | c_inj_SortGeneratedCounterCell_SortKItem (b : SortGeneratedCounterCell_carrier)
 | c_inj_SortGeneratedTopCell_SortKItem (b : SortGeneratedTopCell_carrier)
 | c_inj_SortId_SortKItem (b : SortId_carrier)
 | c_inj_SortIds_SortKItem (b : SortIds_carrier)
 | c_inj_SortInt_SortKItem (b : SortInt_carrier)
 | c_inj_SortKCell_SortKItem (b : SortKCell_carrier)
 | c_inj_SortKResult_SortKItem (b : SortKResult_carrier)
 | c_inj_SortMap_SortKItem (b : SortMap_carrier)
 | c_inj_SortPgm_SortKItem (b : SortPgm_carrier)
 | c_inj_SortStateCell_SortKItem (b : SortStateCell_carrier)
 | c_inj_SortStmt_SortKItem (b : SortStmt_carrier)
 | c_inj_SortString_SortKItem (b : SortString_carrier)
 | c_inj_SortTCell_SortKItem (b : SortTCell_carrier)
with SortKCell_carrier : Set :=
c_dv_SortKCell(v:bool)
with SortIds_carrier : Set :=
 | c__Stop_List_LBraQuotUndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids_QuotRBraUnds_Ids
 | c__UndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids(ocsst:SortId_carrier) (gunav:SortIds_carrier)
with SortGeneratedTopCell_carrier : Set :=
c_dv_SortGeneratedTopCell(v:bool)
with SortStateCell_carrier : Set :=
c_dv_SortStateCell(v:bool)
with SortGeneratedCounterCell_carrier : Set :=
c_dv_SortGeneratedCounterCell(v:bool)
with SortAExp_carrier : Set :=
 | c___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_Int(qcins:SortInt_carrier)
 | c__Unds___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp(eucik:SortAExp_carrier) (ezgyq:SortAExp_carrier)
 | c__UndsPercUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp(qhbmv:SortAExp_carrier) (qxrpe:SortAExp_carrier)
 | c__UndsPlusUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp(zxewo:SortAExp_carrier) (pbiau:SortAExp_carrier)
 | c__UndsSlshUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp(lpnzy:SortAExp_carrier) (ercym:SortAExp_carrier)
 | c__UndsStarUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp(qbpxg:SortAExp_carrier) (bogvs:SortAExp_carrier)
 | c_inj_SortId_SortAExp (b : SortId_carrier)
 | c_inj_SortInt_SortAExp (b : SortInt_carrier)
(* with SortMap_carrier : Set :=
c_dv_SortMap(v:bool) *)
with SortString_carrier : Set :=
c_dv_SortString(v:string)
with SortId_carrier : Set :=
c_dv_SortId(v:string)
with SortBlock_carrier : Set :=
 | c_block(jwyli:SortStmt_carrier)
 | c_emptyblock
with SortBExp_carrier : Set :=
 | c__Unds_GT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp(bckge:SortAExp_carrier) (sppim:SortAExp_carrier)
 | c__Unds_GT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp(aekem:SortAExp_carrier) (eruke:SortAExp_carrier)
 | c__Unds_LT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp(vylat:SortAExp_carrier) (quoyg:SortAExp_carrier)
 | c__Unds_LT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp(hmici:SortAExp_carrier) (fakwl:SortAExp_carrier)
 | c__UndsEqlsEqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp(bsazq:SortAExp_carrier) (iofgm:SortAExp_carrier)
 | c__BangUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp(xmlef:SortBExp_carrier)
 | c__UndsAnd_And_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp_Unds_BExp(aepdf:SortBExp_carrier) (zrgxk:SortBExp_carrier)
 | c_inj_SortBool_SortBExp (b : SortBool_carrier)
with SortInt_carrier : Set :=
c_dv_SortInt(v:Z)
with SortPgm_carrier : Set :=
 | c_int_UndsSClnUndsUnds_IMP_SYNTAX_Unds_Pgm_Unds_Ids_Unds_Stmt(iuuiv:SortIds_carrier) (rrykk:SortStmt_carrier)
with SortKResult_carrier : Set :=
 | c_inj_SortBool_SortKResult (b : SortBool_carrier)
 | c_inj_SortInt_SortKResult (b : SortInt_carrier)
with SortTCell_carrier : Set :=
c_dv_SortTCell(v:bool)
with SortStmt_carrier : Set :=
 | c_assign(pviwl:SortId_carrier) (esuao:SortAExp_carrier)
 | c_if_LParUndsRParUnds_else_UndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block_Unds_Block(sdeyn:SortBExp_carrier) (dnxpo:SortBlock_carrier) (esrke:SortBlock_carrier)
 | c_while_LParUndsRParUndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block(fjoxx:SortBExp_carrier) (ztlzy:SortBlock_carrier)
 | c_seqcomp(uwnas:SortStmt_carrier) (gkitm:SortStmt_carrier)
 | c_inj_SortBlock_SortStmt (b : SortBlock_carrier)
with SortBool_carrier : Set :=
c_dv_SortBool(v:bool)
with SortList_carrier : Set :=
c_dv_SortList (x : list SortKItem_carrier)
with SortSet_carrier : Set :=
c_dv_SortSet (x : list SortKItem_carrier)
with SortMap_carrier : Set :=
c_dv_SortMap (x : list (SortKItem_carrier * SortKItem_carrier))
.

      Definition carrier (s : Ksorts) : Set := match s with
      SortK => SortK_carrier
|SortKItem => SortKItem_carrier
|SortKCell => SortKCell_carrier
|SortIds => SortIds_carrier
|SortGeneratedTopCell => SortGeneratedTopCell_carrier
|SortStateCell => SortStateCell_carrier
|SortGeneratedCounterCell => SortGeneratedCounterCell_carrier
|SortAExp => SortAExp_carrier
|SortMap => SortMap_carrier
|SortString => SortString_carrier
|SortId => SortId_carrier
|SortBlock => SortBlock_carrier
|SortBExp => SortBExp_carrier
|SortInt => SortInt_carrier
|SortPgm => SortPgm_carrier
|SortKResult => SortKResult_carrier
|SortTCell => SortTCell_carrier
|SortStmt => SortStmt_carrier
|SortBool => SortBool_carrier
      end.

Section Prelude.

(* Impure hooks: *)
(* hooked-symbol Lbl'Hash'accept'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int{}(SortInt{}) : SortIOInt{} *)
(* hooked-symbol Lbl'Hash'close'LParUndsRParUnds'K-IO'Unds'K'Unds'Int{}(SortInt{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int{}(SortInt{}) : SortIOInt{} *)
(* hooked-symbol Lbl'Hash'lock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'log{}(SortString{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'logToFile{}(SortString{}, SortString{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'mkstemp'LParUndsRParUnds'K-IO'Unds'IOFile'Unds'String{}(SortString{}) : SortIOFile{} *)
(* hooked-symbol Lbl'Hash'open'LParUndsCommUndsRParUnds'K-IO'Unds'IOInt'Unds'String'Unds'String{}(SortString{}, SortString{}) : SortIOInt{} *)
(* hooked-symbol Lbl'Hash'putc'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'read'LParUndsCommUndsRParUnds'K-IO'Unds'IOString'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortIOString{} *)
(* hooked-symbol Lbl'Hash'remove'LParUndsRParUnds'K-IO'Unds'K'Unds'String{}(SortString{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'seek'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'seekEnd'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'shutdownWrite'LParUndsRParUnds'K-IO'Unds'K'Unds'Int{}(SortInt{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'system'LParUndsRParUnds'K-IO'Unds'KItem'Unds'String{}(SortString{}) : SortKItem{} *)
(* hooked-symbol Lbl'Hash'tell'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int{}(SortInt{}) : SortIOInt{} *)
(* hooked-symbol Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int{}() : SortInt{} *)
(* hooked-symbol Lbl'Hash'trace{}(SortKItem{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'traceK{}(SortK{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'unlock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortK{} *)
(* hooked-symbol Lbl'Hash'write'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'String{}(SortInt{}, SortString{}) : SortK{} 
hooked-symbol LblnewUUID'Unds'STRING-COMMON'Unds'String{}() : SortString{}
hooked-symbol LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int{}(SortInt{}) : SortInt{}
hooked-symbol LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int{}(SortInt{}) : SortK{}
*)


(* Pure hooks: *)
(* hooked-symbol Lbl'Stop'List{}() : SortList{} *)
Definition fun_StopList : option SortList_carrier :=
Some (c_dv_SortList []).

(* hooked-symbol Lbl'Stop'Map{}() : SortMap{} *)
Definition fun_StopMap : option SortMap_carrier :=
Some (c_dv_SortMap []).

(* hooked-symbol Lbl'Stop'Set{}() : SortSet{} *)
Definition fun_StopSet : option SortSet_carrier :=
Some (c_dv_SortSet []).

(* hooked-symbol LblBase2String'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortString{} *)

(* hooked-symbol LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float{}(SortFloat{}) : SortString{} *)

(* hooked-symbol LblFloatFormat{}(SortFloat{}, SortString{}) : SortString{} *)

(* hooked-symbol LblId2String'LParUndsRParUnds'ID-COMMON'Unds'String'Unds'Id{}(SortId{}) : SortString{} *)
Definition fun_Id2String (x : SortId_carrier) : option SortString_carrier :=
Some (c_dv_SortString (SortId_carrier_rect _ id x)).

(* hooked-symbol LblInt2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int{}(SortInt{}) : SortString{} *)

(* hooked-symbol LblList'Coln'get{}(SortList{}, SortInt{}) : SortKItem{} "List:get" *)
Definition fun_List_get (xs : SortList_carrier) (x : SortInt_carrier) : option SortKItem_carrier :=
  SortInt_carrier_rect _ (fun z =>
    SortList_carrier_rect (fun _ => option SortKItem_carrier) (fun xs =>
      if Z.ltb z 0
      then nth_error xs (Z.to_nat (Z.of_nat (length xs) + z))
      else nth_error xs (Z.to_nat z)
  ) xs) x.

(* hooked-symbol LblList'Coln'range{}(SortList{}, SortInt{}, SortInt{}) : SortList{} "List:range" *)
(* Definition fun_List_range (xs : SortList_carrier) (x y : SortInt_carrier) : Admitted. *)

(* hooked-symbol LblList'Coln'set{}(SortList{}, SortInt{}, SortKItem{}) : SortList{} "List:set" *)

(* hooked-symbol LblListItem{}(SortKItem{}) : SortList{} *)
Definition fun_ListItem (x : SortKItem_carrier) : option SortList_carrier :=
  Some (c_dv_SortList [x]).

(* hooked-symbol LblMap'Coln'choice{}(SortMap{}) : SortKItem{} *)

(* hooked-symbol LblMap'Coln'lookup{}(SortMap{}, SortKItem{}) : SortKItem{} *)

(* hooked-symbol LblMap'Coln'lookupOrDefault{}(SortMap{}, SortKItem{}, SortKItem{}) : SortKItem{}  *)

(* hooked-symbol LblMap'Coln'update{}(SortMap{}, SortKItem{}, SortKItem{}) : SortMap{} *)

(* hooked-symbol LblSet'Coln'choice{}(SortSet{}) : SortKItem{} *)

(* hooked-symbol LblSet'Coln'difference{}(SortSet{}, SortSet{}) : SortSet{} *)

(* hooked-symbol LblSet'Coln'in{}(SortKItem{}, SortSet{}) : SortBool{} *)

(* hooked-symbol LblSetItem{}(SortKItem{}) : SortSet{} *)

(* hooked-symbol LblString2Base'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'Int{}(SortString{}, SortInt{}) : SortInt{} *)

(* hooked-symbol LblString2Float'LParUndsRParUnds'STRING-COMMON'Unds'Float'Unds'String{}(SortString{}) : SortFloat{} *)

(* hooked-symbol LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String{}(SortString{}) : SortId{} *)

(* hooked-symbol LblString2Int'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String{}(SortString{}) : SortInt{} *)

(* hooked-symbol Lbl'UndsPerc'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_%Int_"*)
Definition fun_UndsPercInt_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.rem z1) z2)).
(* hooked-symbol Lbl'UndsAnd-'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
Definition fun_UndsAnd_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.land z1) z2)).
(* hooked-symbol Lbl'UndsStar'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_*Int_"*)
Definition fun_UndsStarInt_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.mul z1) z2)).
(* hooked-symbol Lbl'UndsPlus'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_+Int_" *)
Definition fun_UndsPlusInt_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.add z1) z2)).
(* hooked-symbol Lbl'UndsPlus'String'UndsUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String{}(SortString{}, SortString{}) : SortString{} *)

(* hooked-symbol Lbl'Unds'-Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_-Int_" *)
Definition fun_Unds_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub z1) z2)).
(* hooked-symbol Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map{}(SortMap{}, SortMap{}) : SortMap{} *)

(* hooked-symbol Lbl'UndsSlsh'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_/Int_" *)
Definition fun_UndsSlshInt_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.quot z1) z2)).
(* hooked-symbol Lbl'Unds-LT--LT-'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_<<Int_" *)
Definition fun_Unds_LT__LT_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl z1) z2)).
(* hooked-symbol Lbl'Unds-LT-Eqls'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} "_<=Int_" *)
Definition fun_Unds_LT_EqlsInt_Unds_ (z1 z2 : SortInt_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.leb z1) z2)).
(* hooked-symbol Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map{}(SortMap{}, SortMap{}) : SortBool{} *)

(* hooked-symbol Lbl'Unds-LT-Eqls'Set'UndsUnds'SET'Unds'Bool'Unds'Set'Unds'Set{}(SortSet{}, SortSet{}) : SortBool{} *)

(* hooked-symbol Lbl'Unds-LT-Eqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String{}(SortString{}, SortString{}) : SortBool{} *)

(* hooked-symbol Lbl'Unds-LT-'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} "_<Int_" *)
Definition fun_Unds_LT_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.ltb z1) z2)).

(* hooked-symbol Lbl'UndsEqlsSlshEqls'Bool'Unds'{}(SortBool{}, SortBool{}) : SortBool{} "_=/=Bool_" *)
Definition fun_Unds_EqlsSlshEqls_Bool_Unds_ (b1 b2 : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ neqbB b1) b2)).

(* hooked-symbol Lbl'UndsEqlsSlshEqls'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} "_=/=Int_" *)
Definition fun_Unds_EqlsSlshEqls_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ neqbZ z1) z2)).

(* hooked-symbol Lbl'UndsEqlsSlshEqls'K'Unds'{}(SortK{}, SortK{}) : SortBool{} "_=/=K_" *)

(* hooked-symbol Lbl'UndsEqlsSlshEqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String{}(SortString{}, SortString{}) : SortBool{} *)

(* hooked-symbol Lbl'UndsEqlsEqls'Bool'Unds'{}(SortBool{}, SortBool{}) : SortBool{} "_==Bool_" *)
Definition fun_Unds_EqlsEqls_Bool_Unds_ (b1 b2 : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ Bool.eqb b1) b2)).

(* hooked-symbol Lbl'UndsEqlsEqls'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} "_==Int_" *)
Definition fun_Unds_EqlsEqls_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.eqb z1) z2)).

(* hooked-symbol Lbl'UndsEqlsEqls'K'Unds'{}(SortK{}, SortK{}) : SortBool{} "_==K_" *)

(* hooked-symbol Lbl'UndsEqlsEqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String{}(SortString{}, SortString{}) : SortBool{} *)

(* hooked-symbol Lbl'Unds-GT-Eqls'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} "_>=Int_" *)
Definition fun_Unds_GT_Eqls_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.geb z1) z2)).

(* hooked-symbol Lbl'Unds-GT-Eqls'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String{}(SortString{}, SortString{}) : SortBool{} *)

(* hooked-symbol Lbl'Unds-GT--GT-'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_>>Int_" *)
Definition fun_Unds_GT__GT_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftr z1) z2)).

(* hooked-symbol Lbl'Unds-GT-'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} *)
Definition fun_Unds_GT_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.gtb z1) z2)).

(* hooked-symbol Lbl'Unds-GT-'String'UndsUnds'STRING-COMMON'Unds'Bool'Unds'String'Unds'String{}(SortString{}, SortString{}) : SortBool{} *)

(* hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{} "_List_" *)
Definition fun__List_ (xs ys : SortList_carrier) : option SortList_carrier :=
Some (c_dv_SortList (SortList_carrier_rect (fun _ => list SortKItem_carrier) (SortList_carrier_rect _ List.app xs) ys)).


(* hooked-symbol Lbl'Unds'Map'Unds'{}(SortMap{}, SortMap{}) : SortMap{} "_Map_" *)

(* hooked-symbol Lbl'Unds'Set'Unds'{}(SortSet{}, SortSet{}) : SortSet{} "_Set_" *)

(* hooked-symbol Lbl'UndsLSqBUnds-LT-'-undef'RSqB'{}(SortMap{}, SortKItem{}) : SortMap{} -- MAP remove *)

(* hooked-symbol Lbl'UndsXor-Perc'Int'UndsUnds'{}(SortInt{}, SortInt{}, SortInt{}) : SortInt{} "_^+Int_" *)
Definition fun_Unds_Xor_Perc_Int_Unds_ (z1 z2 z3 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ modPow z1) z2) z3)).

(* hooked-symbol Lbl'UndsXor-'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_^Int_" *)
Definition fun_Unds_Xor_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.pow z1) z2)).

(* hooked-symbol Lbl'Unds'andBool'Unds'{}(SortBool{}, SortBool{}) : SortBool{} "_andBool_" *)
Definition fun_Unds_andBool_Unds_ (b1 b2 : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb b1) b2)).

(* hooked-symbol Lbl'Unds'andThenBool'Unds'{}(SortBool{}, SortBool{}) : SortBool{} "_andThenBool_" *)
Definition fun_Unds_andThenBool_Unds_ (b1 b2 : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb b1) b2)).

(* hooked-symbol Lbl'Unds'divInt'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_divInt_" *)
Definition fun_Unds_divInt_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ ediv z1) z2)).

(* hooked-symbol Lbl'Unds'impliesBool'Unds'{}(SortBool{}, SortBool{}) : SortBool{} "_impliesBool_" *)
Definition fun_Unds_impliesBool_Unds_ (b1 b2 : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ implb b1) b2)).

(* hooked-symbol Lbl'Unds'inList'Unds'{}(SortKItem{}, SortList{}) : SortBool{} "_inList_" *)

(* hooked-symbol Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map{}(SortKItem{}, SortMap{}) : SortBool{} --- MAP in_keys *)

(* hooked-symbol Lbl'Unds'modInt'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_modInt_" *)
Definition fun_Unds_modInt_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ emod z1) z2)).

(* hooked-symbol Lbl'Unds'orBool'Unds'{}(SortBool{}, SortBool{}) : SortBool{} "_orBool_" *)
Definition fun_Unds_orBool_Unds_ (b1 b2 : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ orb b1) b2)).

(* hooked-symbol Lbl'Unds'orElseBool'Unds'{}(SortBool{}, SortBool{}) : SortBool{} "_orElseBool_" *)
Definition fun_Unds_orElseBool_Unds_ (b1 b2 : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ orb b1) b2)).

(* hooked-symbol Lbl'Unds'xorBool'Unds'{}(SortBool{}, SortBool{}) : SortBool{} "_xorBool_" *)
Definition fun_Unds_xorBool_Unds_ (b1 b2 : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ xorb b1) b2)).

(* hooked-symbol Lbl'Unds'xorInt'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_xorInt_" *)
Definition fun_Unds_xorInt_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.lxor z1) z2)).

(* hooked-symbol Lbl'UndsPipe'-'-GT-Unds'{}(SortKItem{}, SortKItem{}) : SortMap{} "_|->_" *)

(* hooked-symbol Lbl'UndsPipe'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} "_|Int_" *)
Definition fun_Unds_orInt_Int_Unds_ (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.lor z1) z2)).

(* hooked-symbol Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set{}(SortSet{}, SortSet{}) : SortSet{} -- SET union *)

(* hooked-symbol LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int{}(SortInt{}) : SortInt{} *)
Definition fun_absInt (z : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect _ Z.abs z)).

(* hooked-symbol LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}, SortInt{}) : SortInt{} *)
Definition fun_bitRangeInt (z1 z2 z3 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ bitRange z1) z2) z3)).

(* hooked-symbol LblcategoryChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String{}(SortString{}) : SortString{} *)

(* hooked-symbol LblchrChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int{}(SortInt{}) : SortString{} *)

(* hooked-symbol LblcountAllOccurrences'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String{}(SortString{}, SortString{}) : SortInt{} *)

(* hooked-symbol LbldirectionalityChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String{}(SortString{}) : SortString{} *)

(* hooked-symbol LblfillList'LParUndsCommUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'Int'Unds'KItem{}(SortList{}, SortInt{}, SortInt{}, SortKItem{}) : SortList{} *)

(* hooked-symbol LblfindChar'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int{}(SortString{}, SortString{}, SortInt{}) : SortInt{} *)

(* hooked-symbol LblfindString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int{}(SortString{}, SortString{}, SortInt{}) : SortInt{} *)

(* hooked-symbol LblintersectSet'LParUndsCommUndsRParUnds'SET'Unds'Set'Unds'Set'Unds'Set{}(SortSet{}, SortSet{}) : SortSet{} *)

(* hooked-symbol Lblite{SortSort}(SortBool{}, SortSort, SortSort) : SortSort "ite" *)

(* hooked-symbol Lblkeys'LParUndsRParUnds'MAP'Unds'Set'Unds'Map{}(SortMap{}) : SortSet{} -- MAP keys *)

(* hooked-symbol Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map{}(SortMap{}) : SortList{} -- MAP keys list *)

(* hooked-symbol LbllengthString'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String{}(SortString{}) : SortInt{} *)

(* hooked-symbol Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int{}(SortInt{}) : SortInt{} *)
Definition fun_log2Int (z : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect _ Z.log2 z)).

(* hooked-symbol LblmakeList'LParUndsCommUndsRParUnds'LIST'Unds'List'Unds'Int'Unds'KItem{}(SortInt{}, SortKItem{}) : SortList{} *)

(* hooked-symbol LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortInt{} *)
Definition fun_maxInt (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.max z1) z2)).

(* hooked-symbol LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortInt{} *)
Definition fun_minInt (z1 z2 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.min z1) z2)).

(* hooked-symbol LblnotBool'Unds'{}(SortBool{}) : SortBool{} *)
Definition fun_notBool_Unds_ (b : SortBool_carrier) : option (SortBool_carrier) :=
  Some (c_dv_SortBool (SortBool_carrier_rect _ negb b)).

(* hooked-symbol LblordChar'LParUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String{}(SortString{}) : SortInt{} *)

(* hooked-symbol LblpushList{}(SortKItem{}, SortList{}) : SortList{} "pushList" *)
Definition fun_pushList (x : SortKItem_carrier) (xs : SortList_carrier) : option SortList_carrier :=
  Some (c_dv_SortList (SortList_carrier_rect _ (fun xs => x :: xs) xs)).

(* hooked-symbol LblremoveAll'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Set{}(SortMap{}, SortSet{}) : SortMap{} *)

(* hooked-symbol Lblreplace'LParUndsCommUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String'Unds'Int{}(SortString{}, SortString{}, SortString{}, SortInt{}) : SortString{} *)

(* hooked-symbol LblreplaceAll'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String{}(SortString{}, SortString{}, SortString{}) : SortString{} *)

(* hooked-symbol LblreplaceFirst'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'String'Unds'String{}(SortString{}, SortString{}, SortString{}) : SortString{} *)

(* hooked-symbol LblrfindChar'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int{}(SortString{}, SortString{}, SortInt{}) : SortInt{} *)

(* hooked-symbol LblrfindString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'Int'Unds'String'Unds'String'Unds'Int{}(SortString{}, SortString{}, SortInt{}) : SortInt{} *)

(* hooked-symbol LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}, SortInt{}) : SortInt{} *)
Definition fun_signExtendBitRangeInt (z1 z2 z3 : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ signExtendBitRange z1) z2) z3)).

(* hooked-symbol Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set{}(SortSet{}) : SortInt{} *)

(* hooked-symbol LblsizeList{}(SortList{}) : SortInt{} *)

(* hooked-symbol LblsizeMap{}(SortMap{}) : SortInt{} *)

(* hooked-symbol LblsubstrString'LParUndsCommUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'String'Unds'Int'Unds'Int{}(SortString{}, SortInt{}, SortInt{}) : SortString{} *)

(* hooked-symbol LblupdateList'LParUndsCommUndsCommUndsRParUnds'LIST'Unds'List'Unds'List'Unds'Int'Unds'List{}(SortList{}, SortInt{}, SortList{}) : SortList{} *)

(* hooked-symbol LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map{}(SortMap{}, SortMap{}) : SortMap{} *)

(* hooked-symbol Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map{}(SortMap{}) : SortList{} *)

(* hooked-symbol Lbl'Tild'Int'Unds'{}(SortInt{}) : SortInt{} "~Int_ "*)
Definition fun_TildInt_Unds_ (z : SortInt_carrier) : option (SortInt_carrier) :=
  Some (c_dv_SortInt (SortInt_carrier_rect _ Z.lnot z)).

End Prelude.

      Definition retr_SortKItem_SortAExp x := match x with
  | c_inj_SortId_SortKItem x => Some (c_inj_SortId_SortAExp x)
  | c_inj_SortInt_SortKItem x => Some (c_inj_SortInt_SortAExp x)
  | c_inj_SortAExp_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortKCell x := match x with
  | c_inj_SortKCell_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortStmt x := match x with
  | c_inj_SortBlock_SortKItem x => Some (c_inj_SortBlock_SortStmt x)
  | c_inj_SortStmt_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortBExp x := match x with
  | c_inj_SortBool_SortKItem x => Some (c_inj_SortBool_SortBExp x)
  | c_inj_SortBExp_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortPgm x := match x with
  | c_inj_SortPgm_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortMap x := match x with
  | c_inj_SortMap_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortIds x := match x with
  | c_inj_SortIds_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortBool x := match x with
  | c_inj_SortBool_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortBlock x := match x with
  | c_inj_SortBlock_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortKResult x := match x with
  | c_inj_SortBool_SortKItem x => Some (c_inj_SortBool_SortKResult x)
  | c_inj_SortInt_SortKItem x => Some (c_inj_SortInt_SortKResult x)
  | c_inj_SortKResult_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortInt x := match x with
  | c_inj_SortInt_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortGeneratedCounterCell x := match x with
  | c_inj_SortGeneratedCounterCell_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortString x := match x with
  | c_inj_SortString_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortStateCell x := match x with
  | c_inj_SortStateCell_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortGeneratedTopCell x := match x with
  | c_inj_SortGeneratedTopCell_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortId x := match x with
  | c_inj_SortId_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortTCell x := match x with
  | c_inj_SortTCell_SortKItem x => Some x
  | _ => None end.

Definition retr_SortBExp_SortBool x := match x with
  | c_inj_SortBool_SortBExp x => Some x
  | _ => None end.

Definition retr_SortStmt_SortBlock x := match x with
  | c_inj_SortBlock_SortStmt x => Some x
  | _ => None end.

Definition retr_SortAExp_SortInt x := match x with
  | c_inj_SortInt_SortAExp x => Some x
  | _ => None end.

Definition retr_SortAExp_SortId x := match x with
  | c_inj_SortId_SortAExp x => Some x
  | _ => None end.

Definition retr_SortKResult_SortInt x := match x with
  | c_inj_SortInt_SortKResult x => Some x
  | _ => None end.

Definition retr_SortKResult_SortBool x := match x with
  | c_inj_SortBool_SortKResult x => Some x
  | _ => None end.

Print Ksyms.
(*      Definition _61fbef3 : SortBool_carrier -> SortBool_carrier -> option SortBool_carrier
   := fun x => match x with  false, _Gen0 => Some false
  | _, _ => None end.
Definition _5b9db8d : SortBool_carrier -> SortBool_carrier -> option SortBool_carrier
   := fun x => match x with  true, B => Some B
  | _, _ => None end.
Definition _17ebc68 : SortBool_carrier -> option SortBool_carrier
   := fun x => match x with  false => Some true
  | _ => None end.
Definition _afefecb : SortK_carrier -> option SortBool_carrier
   := fun x => match x with  K => Some false end.
Definition _53fc758 : SortBool_carrier -> option SortBool_carrier
   := fun x => match x with  true => Some false
  | _ => None end.
axiom «_%Int_» (x0 : SortInt) (x1 : SortInt) : Option SortIntTODOOOOOOOOOOO
axiom «.Map» : Option SortMapTODOOOOOOOOOOO
Definition _f4c2469 : SortK_carrier -> option SortBool_carrier
   := fun x => match x with  c_kseq _Pat0 c_dotk => match (retr_SortKItem_SortKResult) _Pat0 with
    | Some KResult => Some true
    | _ => None
  | _ => None end end.
axiom «_ := fun x => match x with ->_» (x0 : SortKItem) (x1 : SortKItem) : Option SortMap end.
axiom _Map_ (x0 : SortMap) (x1 : SortMap) : Option SortMapTODOOOOOOOOOOO
Definition N/A (x0 : SortBool_carrier) (x1 : SortBool_carrier) : option SortBool_carrier := (_5b9db8d x0 x1) <|> (_61fbef3 x0 x1).
Definition N/A (x0 : SortBool_carrier) : option SortBool_carrier := (_17ebc68 x0) <|> (_53fc758 x0).
Definition N/A (x0 : SortK_carrier) : option SortBool_carrier := (_f4c2469 x0) <|> (_afefecb x0).
Definition _4de6e05 : SortInt_carrier -> SortInt_carrier -> option SortBool_carrier
   := fun x => match x with  I1, I2 => do
    let _Val0 <- «_==Int_» I1 I2
    let _Val1 <- notBool_ _Val0
    return _Val1 end.
Definition N/A (x0 : SortInt_carrier) (x1 : SortInt_carrier) : option SortBool_carrier := _4de6e05 x0 x1. *)
      Definition parser (s : Ksorts) : string -> option (carrier s) :=
            match s with
             | SortString => map_parser c_dv_SortString string_parser
             | SortId => map_parser c_dv_SortId string_parser
             | SortInt => map_parser c_dv_SortInt Z_parser
             | SortBool => map_parser c_dv_SortBool bool_parser
             | _ => None_parser
            end.
      
      Definition P (σ : symbol) := foldr (λ c a, carrier c -> a) (option (carrier (ret_sort σ))) (arg_sorts σ).
      Program Definition Model : @Model TheorySignature :=
        mkModel_partial
          carrier (* (Ksorts_rect _ SortK_carrier SortKItem_carrier SortKCell_carrier SortIds_carrier SortGeneratedTopCell_carrier SortStateCell_carrier SortGeneratedCounterCell_carrier SortAExp_carrier SortMap_carrier SortString_carrier SortId_carrier SortBlock_carrier SortBExp_carrier SortInt_carrier SortPgm_carrier SortKResult_carrier SortTCell_carrier SortStmt_carrier SortBool_carrier) *)
          (Ksyms_rect P (fun x0 x1 => Some (c_kseq x0 x1))
(Some c_dotk)
(fun x0 => Some (c__BangUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp x0))
(fun x0 x1 x2 => Some (c__Hash_systemResult x0 x1 x2))
(fun x0 => Some (c___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_Int x0))
(Some c__Stop_List_LBraQuotUndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids_QuotRBraUnds_Ids)
(fun x0 x1 => Some (c__UndsPercUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__UndsAnd_And_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_BExp_Unds_BExp x0 x1))
(fun x0 x1 => Some (c__UndsStarUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__UndsPlusUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__UndsCommUndsUnds_IMP_SYNTAX_Unds_Ids_Unds_Id_Unds_Ids x0 x1))
(fun x0 x1 => Some (c__Unds___UndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__UndsSlshUndsUnds_IMP_SYNTAX_Unds_AExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__Unds_LT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__Unds_LT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__UndsEqlsEqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__Unds_GT_EqlsUndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp x0 x1))
(fun x0 x1 => Some (c__Unds_GT_UndsUnds_IMP_SYNTAX_Unds_BExp_Unds_AExp_Unds_AExp x0 x1))
fun_Unds_andBool_Unds_
(fun x0 x1 => Some (c_assign x0 x1))
(fun x0 => Some (c_block x0))
(Some c_emptyblock)
(fun x0 x1 x2 => Some (c_if_LParUndsRParUnds_else_UndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block_Unds_Block x0 x1 x2))
(fun x0 x1 => Some (c_int_UndsSClnUndsUnds_IMP_SYNTAX_Unds_Pgm_Unds_Ids_Unds_Stmt x0 x1))
fun_notBool_Unds_
(fun x0 x1 => Some (c_seqcomp x0 x1))
(fun x0 x1 => Some (c_while_LParUndsRParUndsUnds_IMP_SYNTAX_Unds_Stmt_Unds_BExp_Unds_Block x0 x1)))
          _
          _
          parser.
      Next Obligation.
        destruct s.
        all: timeout 1 repeat constructor.
      Defined.
      Final Obligation.
        intros s1 s2 H x; inversion H; subst.
      * exact (c_inj_SortAExp_SortKItem x).
* exact (c_inj_SortKCell_SortKItem x).
* exact (c_inj_SortStmt_SortKItem x).
* exact (c_inj_SortBExp_SortKItem x).
* exact (c_inj_SortPgm_SortKItem x).
* exact (c_inj_SortMap_SortKItem x).
* exact (c_inj_SortIds_SortKItem x).
* exact (c_inj_SortBool_SortKItem x).
* exact (c_inj_SortBlock_SortKItem x).
* exact (c_inj_SortKResult_SortKItem x).
* exact (c_inj_SortInt_SortKItem x).
* exact (c_inj_SortGeneratedCounterCell_SortKItem x).
* exact (c_inj_SortString_SortKItem x).
* exact (c_inj_SortStateCell_SortKItem x).
* exact (c_inj_SortGeneratedTopCell_SortKItem x).
* exact (c_inj_SortId_SortKItem x).
* exact (c_inj_SortTCell_SortKItem x).
* exact (c_inj_SortBool_SortBExp x).
* exact (c_inj_SortBlock_SortStmt x).
* exact (c_inj_SortInt_SortAExp x).
* exact (c_inj_SortId_SortAExp x).
* exact (c_inj_SortInt_SortKResult x).
* exact (c_inj_SortBool_SortKResult x).
Defined.

Ltac autorewrite_set :=
  repeat (
    rewrite intersection_top_l_L +
    rewrite intersection_top_r_L +
    rewrite union_empty_l_L +
    rewrite union_empty_r_L +
    rewrite propset_difference_neg +
    rewrite propset_union_simpl +
    rewrite propset_intersection_simpl +
    rewrite singleton_subseteq_l +
    rewrite fmap_propset_singleton
  ).

Ltac basic_simplify_krule :=
  eval_helper2;
  simpl sort_inj;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
  autorewrite_set.

Ltac simplify_krule :=
  basic_simplify_krule;
  apply propset_top_elem_of_2;
  intro;
  apply elem_of_PropSet;
  repeat rewrite elem_of_PropSet;
  repeat rewrite singleton_subseteq;
  repeat rewrite singleton_eq.

Ltac classicize :=
  apply Classical_Prop.imply_to_or.

Ltac simplify_equality :=
match goal with
      | [H : _ _ = _ _ |- _] => simplify_eq H; clear H; intro
      end.

Ltac abstract_var := 
  match goal with
    | [|- context [evar_valuation ?σ ?s]] =>
      let x := fresh "var" in
      let Hx := fresh "Hvar" in
        remember (evar_valuation σ s) as x eqn:Hx (*;
        clear Hx;
        revert x *)
    end.


  Goal satT Theory_behavioural Model.
  Proof.
    unfold satT, satM. intros.
    unfold Theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst.
    all: simplify_krule; try reflexivity;
         try classicize;
         intros;
         repeat destruct_evar_val; subst;
         repeat simplify_equality; subst;
         try tauto;
         try congruence.
    (* 4 goals remain *)
    all: cbn.
    1: try destruct H; subst; apply singleton_subseteq_l in H;
         destruct H0;
         try rewrite singleton_subseteq in H0; set_solver.
         1-2: by rewrite andb_comm.
    set_solver.
  Defined.

      End TheorySemantics.

