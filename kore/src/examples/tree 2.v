
From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
From Kore Require Import BuiltIns DVParsers.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope string_scope.
Open Scope hlist_scope.

Require Import Btauto.

      Module TheorySyntax.


        Inductive Ksorts :=
        | SortK
        | SortKItem
        | SortKCellOpt
        | SortTree
        | SortKCell
        | SortMap
        | SortGeneratedCounterCellOpt
        | SortKConfigVar
        | SortInt
        | SortSet
        | SortGeneratedTopCellFragment
        | SortList
        | SortGeneratedTopCell
        | SortGeneratedCounterCell
        | SortIntList
        | SortBool
        .
        Instance Ksorts_eq_dec : EqDecision Ksorts.
        Proof. solve_decision. Defined.
  (*      Program Instance Ksorts_countable : finite.Finite Ksorts :=
        {
          enum := [SortK; SortKItem; SortKCellOpt; SortTree; SortKCell; SortMap; SortGeneratedCounterCellOpt; SortKConfigVar; SortInt; SortSet; SortGeneratedTopCellFragment; SortList; SortGeneratedTopCell; SortGeneratedCounterCell; SortIntList; SortBool]
        }.
        Next Obligation.
          compute_done.
        Defined.
        Final Obligation.
          intros. destruct x; set_solver.
        Defined.
  *)



  Inductive Ksyms :=
  | kseq (* kseq *)
  | dotk (* dotk *)
  | append (* append *)
  | Stop_List (* .List *)
  | Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList (* .List{"_,__TREE_IntList_Int_IntList"}_IntList *)
  | LT__generatedTop__GT___fragment (* <generatedTop>-fragment *)
  | Empty_Unds_TREE_Unds_Tree (* Empty_TREE_Tree *)
  | ListItem (* ListItem *)
  | Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree (* Node(_,_,_,_)_TREE_Tree_Int_Int_Tree_Tree *)
  | Set_Coln_difference (* Set:difference *)
  | UndsPerc_Int_Unds_ (* _%Int_ *)
  | UndsPlus_Int_Unds_ (* _+Int_ *)
  | UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList (* _,__TREE_IntList_Int_IntList *)
  | Unds__Int_Unds_ (* _-Int_ *)
  | UndsSlsh_Int_Unds_ (* _/Int_ *)
  | Unds_LT__LT__Int_Unds_ (* _<<Int_ *)
  | Unds_LT_Eqls_Int_Unds_ (* _<=Int_ *)
  | Unds_LT__Int_Unds_ (* _<Int_ *)
  | UndsEqlsSlshEqls_Bool_Unds_ (* _=/=Bool_ *)
  | UndsEqlsSlshEqls_Int_Unds_ (* _=/=Int_ *)
  | UndsEqlsSlshEqls_K_Unds_ (* _=/=K_ *)
  | UndsEqlsEqls_Bool_Unds_ (* _==Bool_ *)
  | UndsEqlsEqls_Int_Unds_ (* _==Int_ *)
  | UndsEqlsEqls_K_Unds_ (* _==K_ *)
  | Unds_GT_Eqls_Int_Unds_ (* _>=Int_ *)
  | Unds_GT__GT__Int_Unds_ (* _>>Int_ *)
  | Unds_GT__Int_Unds_ (* _>Int_ *)
  | Unds_List_Unds_ (* _List_ *)
  | Unds_Set_Unds_ (* _Set_ *)
  | Unds_andBool_Unds_ (* _andBool_ *)
  | Unds_andThenBool_Unds_ (* _andThenBool_ *)
  | Unds_divInt_Unds_ (* _divInt_ *)
  | Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int (* _dividesInt__INT-COMMON_Bool_Int_Int *)
  | Unds_impliesBool_Unds_ (* _impliesBool_ *)
  | Unds_modInt_Unds_ (* _modInt_ *)
  | Unds_orBool_Unds_ (* _orBool_ *)
  | Unds_orElseBool_Unds_ (* _orElseBool_ *)
  | Unds_xorBool_Unds_ (* _xorBool_ *)
  | UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set (* _|Set__SET_Set_Set_Set *)
  | absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int (* absInt(_)_INT-COMMON_Int_Int *)
  | balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* balance(_)_TREE_Tree_Tree *)
  | balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* balanceFactor(_)_TREE_Int_Tree *)
  | bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int (* bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int *)
  | freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int (* freshInt(_)_INT_Int_Int *)
  | height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* height(_)_TREE_Int_Tree *)
  | inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree (* inorder(_)_TREE_List_Tree *)
  | insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int (* insert(_,_)_TREE_Tree_Tree_Int *)
  | isBool (* isBool *)
  | isInt (* isInt *)
  | isIntList (* isIntList *)
  | isK (* isK *)
  | isKCell (* isKCell *)
  | isKCellOpt (* isKCellOpt *)
  | isKConfigVar (* isKConfigVar *)
  | isKItem (* isKItem *)
  | isList (* isList *)
  | isMap (* isMap *)
  | isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree (* isNode(_)_TREE_Bool_Tree *)
  | isSet (* isSet *)
  | isTree (* isTree *)
  | leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* leftT(_)_TREE_Tree_Tree *)
  | maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int (* maxInt(_,_)_INT-COMMON_Int_Int_Int *)
  | minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int (* minInt(_,_)_INT-COMMON_Int_Int_Int *)
  | noKCell (* noKCell *)
  | node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree (* node(_,_,_)_TREE_Tree_Int_Tree_Tree *)
  | notBool_Unds_ (* notBool_ *)
  | project_Coln_Bool (* project:Bool *)
  | project_Coln_Int (* project:Int *)
  | project_Coln_IntList (* project:IntList *)
  | project_Coln_K (* project:K *)
  | project_Coln_KCell (* project:KCell *)
  | project_Coln_KCellOpt (* project:KCellOpt *)
  | project_Coln_KItem (* project:KItem *)
  | project_Coln_List (* project:List *)
  | project_Coln_Map (* project:Map *)
  | project_Coln_Set (* project:Set *)
  | project_Coln_Tree (* project:Tree *)
  | pushList (* pushList *)
  | rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rightT(_)_TREE_Tree_Tree *)
  | rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateLeft(_)_TREE_Tree_Tree *)
  | rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateLeftRight(_)_TREE_Tree_Tree *)
  | rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateRight(_)_TREE_Tree_Tree *)
  | rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateRightLeft(_)_TREE_Tree_Tree *)
  | value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* value(_)_TREE_Int_Tree *)
  .
  (*
  Instance Ksyms_eq_dec : EqDecision Ksyms.
  Proof. solve_decision. Defined.
  Program Instance Ksyms_countable : finite.Finite Ksyms :=
  {
    enum := [kseq (* kseq *); dotk (* dotk *); append (* append *); Stop_List (* .List *); Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList (* .List{"_,__TREE_IntList_Int_IntList"}_IntList *); LT__generatedTop__GT___fragment (* <generatedTop>-fragment *); Empty_Unds_TREE_Unds_Tree (* Empty_TREE_Tree *); ListItem (* ListItem *); Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree (* Node(_,_,_,_)_TREE_Tree_Int_Int_Tree_Tree *); Set_Coln_difference (* Set:difference *); UndsPerc_Int_Unds_ (* _%Int_ *); UndsPlus_Int_Unds_ (* _+Int_ *); UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList (* _,__TREE_IntList_Int_IntList *); Unds__Int_Unds_ (* _-Int_ *); UndsSlsh_Int_Unds_ (* _/Int_ *); Unds_LT__LT__Int_Unds_ (* _<<Int_ *); Unds_LT_Eqls_Int_Unds_ (* _<=Int_ *); Unds_LT__Int_Unds_ (* _<Int_ *); UndsEqlsSlshEqls_Bool_Unds_ (* _=/=Bool_ *); UndsEqlsSlshEqls_Int_Unds_ (* _=/=Int_ *); UndsEqlsSlshEqls_K_Unds_ (* _=/=K_ *); UndsEqlsEqls_Bool_Unds_ (* _==Bool_ *); UndsEqlsEqls_Int_Unds_ (* _==Int_ *); UndsEqlsEqls_K_Unds_ (* _==K_ *); Unds_GT_Eqls_Int_Unds_ (* _>=Int_ *); Unds_GT__GT__Int_Unds_ (* _>>Int_ *); Unds_GT__Int_Unds_ (* _>Int_ *); Unds_List_Unds_ (* _List_ *); Unds_Set_Unds_ (* _Set_ *); Unds_andBool_Unds_ (* _andBool_ *); Unds_andThenBool_Unds_ (* _andThenBool_ *); Unds_divInt_Unds_ (* _divInt_ *); Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int (* _dividesInt__INT-COMMON_Bool_Int_Int *); Unds_impliesBool_Unds_ (* _impliesBool_ *); Unds_modInt_Unds_ (* _modInt_ *); Unds_orBool_Unds_ (* _orBool_ *); Unds_orElseBool_Unds_ (* _orElseBool_ *); Unds_xorBool_Unds_ (* _xorBool_ *); UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set (* _|Set__SET_Set_Set_Set *); absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int (* absInt(_)_INT-COMMON_Int_Int *); balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* balance(_)_TREE_Tree_Tree *); balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* balanceFactor(_)_TREE_Int_Tree *); bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int (* bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int *); freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int (* freshInt(_)_INT_Int_Int *); height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* height(_)_TREE_Int_Tree *); inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree (* inorder(_)_TREE_List_Tree *); insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int (* insert(_,_)_TREE_Tree_Tree_Int *); isBool (* isBool *); isInt (* isInt *); isIntList (* isIntList *); isK (* isK *); isKCell (* isKCell *); isKCellOpt (* isKCellOpt *); isKConfigVar (* isKConfigVar *); isKItem (* isKItem *); isList (* isList *); isMap (* isMap *); isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree (* isNode(_)_TREE_Bool_Tree *); isSet (* isSet *); isTree (* isTree *); leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* leftT(_)_TREE_Tree_Tree *); maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int (* maxInt(_,_)_INT-COMMON_Int_Int_Int *); minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int (* minInt(_,_)_INT-COMMON_Int_Int_Int *); noKCell (* noKCell *); node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree (* node(_,_,_)_TREE_Tree_Int_Tree_Tree *); notBool_Unds_ (* notBool_ *); project_Coln_Bool (* project:Bool *); project_Coln_Int (* project:Int *); project_Coln_IntList (* project:IntList *); project_Coln_K (* project:K *); project_Coln_KCell (* project:KCell *); project_Coln_KCellOpt (* project:KCellOpt *); project_Coln_KItem (* project:KItem *); project_Coln_List (* project:List *); project_Coln_Map (* project:Map *); project_Coln_Set (* project:Set *); project_Coln_Tree (* project:Tree *); pushList (* pushList *); rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rightT(_)_TREE_Tree_Tree *); rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateLeft(_)_TREE_Tree_Tree *); rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateLeftRight(_)_TREE_Tree_Tree *); rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateRight(_)_TREE_Tree_Tree *); rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateRightLeft(_)_TREE_Tree_Tree *); value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* value(_)_TREE_Int_Tree *)]
  }.
  Next Obligation.
    compute_done.
  Defined.
  Final Obligation.
    intros. destruct x; set_solver.
  Defined.
  *)

        Inductive KSubsort : CRelationClasses.crelation Ksorts :=
|  inj_SortBool_SortKItem : KSubsort SortBool SortKItem
|  inj_SortInt_SortKItem : KSubsort SortInt SortKItem
|  inj_SortGeneratedTopCell_SortKItem : KSubsort SortGeneratedTopCell SortKItem
|  inj_SortMap_SortKItem : KSubsort SortMap SortKItem
|  inj_SortKCell_SortKItem : KSubsort SortKCell SortKItem
|  inj_SortGeneratedCounterCellOpt_SortKItem : KSubsort SortGeneratedCounterCellOpt SortKItem
|  inj_SortGeneratedCounterCell_SortKItem : KSubsort SortGeneratedCounterCell SortKItem
|  inj_SortTree_SortKItem : KSubsort SortTree SortKItem
|  inj_SortGeneratedTopCellFragment_SortKItem : KSubsort SortGeneratedTopCellFragment SortKItem
|  inj_SortIntList_SortKItem : KSubsort SortIntList SortKItem
|  inj_SortSet_SortKItem : KSubsort SortSet SortKItem
|  inj_SortList_SortKItem : KSubsort SortList SortKItem
|  inj_SortKCellOpt_SortKItem : KSubsort SortKCellOpt SortKItem
|  inj_SortKConfigVar_SortKItem : KSubsort SortKConfigVar SortKItem
|  inj_SortKCell_SortKCellOpt : KSubsort SortKCell SortKCellOpt
|  inj_SortGeneratedCounterCell_SortGeneratedCounterCellOpt : KSubsort SortGeneratedCounterCell SortGeneratedCounterCellOpt
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
  | append => [SortK;SortK]
  | Stop_List => []
  | Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList => []
  | LT__generatedTop__GT___fragment => [SortKCellOpt;SortGeneratedCounterCellOpt]
  | Empty_Unds_TREE_Unds_Tree => []
  | ListItem => [SortKItem]
  | Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree => [SortInt;SortInt;SortTree;SortTree]
  | Set_Coln_difference => [SortSet;SortSet]
  | UndsPerc_Int_Unds_ => [SortInt;SortInt]
  | UndsPlus_Int_Unds_ => [SortInt;SortInt]
  | UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList => [SortInt;SortIntList]
  | Unds__Int_Unds_ => [SortInt;SortInt]
  | UndsSlsh_Int_Unds_ => [SortInt;SortInt]
  | Unds_LT__LT__Int_Unds_ => [SortInt;SortInt]
  | Unds_LT_Eqls_Int_Unds_ => [SortInt;SortInt]
  | Unds_LT__Int_Unds_ => [SortInt;SortInt]
  | UndsEqlsSlshEqls_Bool_Unds_ => [SortBool;SortBool]
  | UndsEqlsSlshEqls_Int_Unds_ => [SortInt;SortInt]
  | UndsEqlsSlshEqls_K_Unds_ => [SortK;SortK]
  | UndsEqlsEqls_Bool_Unds_ => [SortBool;SortBool]
  | UndsEqlsEqls_Int_Unds_ => [SortInt;SortInt]
  | UndsEqlsEqls_K_Unds_ => [SortK;SortK]
  | Unds_GT_Eqls_Int_Unds_ => [SortInt;SortInt]
  | Unds_GT__GT__Int_Unds_ => [SortInt;SortInt]
  | Unds_GT__Int_Unds_ => [SortInt;SortInt]
  | Unds_List_Unds_ => [SortList;SortList]
  | Unds_Set_Unds_ => [SortSet;SortSet]
  | Unds_andBool_Unds_ => [SortBool;SortBool]
  | Unds_andThenBool_Unds_ => [SortBool;SortBool]
  | Unds_divInt_Unds_ => [SortInt;SortInt]
  | Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int => [SortInt;SortInt]
  | Unds_impliesBool_Unds_ => [SortBool;SortBool]
  | Unds_modInt_Unds_ => [SortInt;SortInt]
  | Unds_orBool_Unds_ => [SortBool;SortBool]
  | Unds_orElseBool_Unds_ => [SortBool;SortBool]
  | Unds_xorBool_Unds_ => [SortBool;SortBool]
  | UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set => [SortSet;SortSet]
  | absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int => [SortInt]
  | balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => [SortTree]
  | bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int => [SortInt;SortInt;SortInt]
  | freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int => [SortInt]
  | height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => [SortTree]
  | inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree => [SortTree]
  | insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int => [SortTree;SortInt]
  | isBool => [SortK]
  | isInt => [SortK]
  | isIntList => [SortK]
  | isK => [SortK]
  | isKCell => [SortK]
  | isKCellOpt => [SortK]
  | isKConfigVar => [SortK]
  | isKItem => [SortK]
  | isList => [SortK]
  | isMap => [SortK]
  | isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree => [SortTree]
  | isSet => [SortK]
  | isTree => [SortK]
  | leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int => [SortInt;SortInt]
  | minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int => [SortInt;SortInt]
  | noKCell => []
  | node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree => [SortInt;SortTree;SortTree]
  | notBool_Unds_ => [SortBool]
  | project_Coln_Bool => [SortK]
  | project_Coln_Int => [SortK]
  | project_Coln_IntList => [SortK]
  | project_Coln_K => [SortK]
  | project_Coln_KCell => [SortK]
  | project_Coln_KCellOpt => [SortK]
  | project_Coln_KItem => [SortK]
  | project_Coln_List => [SortK]
  | project_Coln_Map => [SortK]
  | project_Coln_Set => [SortK]
  | project_Coln_Tree => [SortK]
  | pushList => [SortKItem;SortList]
  | rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => [SortTree]
      end;
    ret_sort σ :=
      match σ with
                | kseq => SortK
  | dotk => SortK
  | append => SortK
  | Stop_List => SortList
  | Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList => SortIntList
  | LT__generatedTop__GT___fragment => SortGeneratedTopCellFragment
  | Empty_Unds_TREE_Unds_Tree => SortTree
  | ListItem => SortList
  | Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree => SortTree
  | Set_Coln_difference => SortSet
  | UndsPerc_Int_Unds_ => SortInt
  | UndsPlus_Int_Unds_ => SortInt
  | UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList => SortIntList
  | Unds__Int_Unds_ => SortInt
  | UndsSlsh_Int_Unds_ => SortInt
  | Unds_LT__LT__Int_Unds_ => SortInt
  | Unds_LT_Eqls_Int_Unds_ => SortBool
  | Unds_LT__Int_Unds_ => SortBool
  | UndsEqlsSlshEqls_Bool_Unds_ => SortBool
  | UndsEqlsSlshEqls_Int_Unds_ => SortBool
  | UndsEqlsSlshEqls_K_Unds_ => SortBool
  | UndsEqlsEqls_Bool_Unds_ => SortBool
  | UndsEqlsEqls_Int_Unds_ => SortBool
  | UndsEqlsEqls_K_Unds_ => SortBool
  | Unds_GT_Eqls_Int_Unds_ => SortBool
  | Unds_GT__GT__Int_Unds_ => SortInt
  | Unds_GT__Int_Unds_ => SortBool
  | Unds_List_Unds_ => SortList
  | Unds_Set_Unds_ => SortSet
  | Unds_andBool_Unds_ => SortBool
  | Unds_andThenBool_Unds_ => SortBool
  | Unds_divInt_Unds_ => SortInt
  | Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int => SortBool
  | Unds_impliesBool_Unds_ => SortBool
  | Unds_modInt_Unds_ => SortInt
  | Unds_orBool_Unds_ => SortBool
  | Unds_orElseBool_Unds_ => SortBool
  | Unds_xorBool_Unds_ => SortBool
  | UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set => SortSet
  | absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int => SortInt
  | balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => SortInt
  | bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int => SortInt
  | freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int => SortInt
  | height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => SortInt
  | inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree => SortList
  | insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int => SortTree
  | isBool => SortBool
  | isInt => SortBool
  | isIntList => SortBool
  | isK => SortBool
  | isKCell => SortBool
  | isKCellOpt => SortBool
  | isKConfigVar => SortBool
  | isKItem => SortBool
  | isList => SortBool
  | isMap => SortBool
  | isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree => SortBool
  | isSet => SortBool
  | isTree => SortBool
  | leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int => SortInt
  | minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int => SortInt
  | noKCell => SortKCellOpt
  | node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree => SortTree
  | notBool_Unds_ => SortBool
  | project_Coln_Bool => SortBool
  | project_Coln_Int => SortInt
  | project_Coln_IntList => SortIntList
  | project_Coln_K => SortK
  | project_Coln_KCell => SortKCell
  | project_Coln_KCellOpt => SortKCellOpt
  | project_Coln_KItem => SortKItem
  | project_Coln_List => SortList
  | project_Coln_Map => SortMap
  | project_Coln_Set => SortSet
  | project_Coln_Tree => SortTree
  | pushList => SortList
  | rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => SortInt
      end;
  |};
|}.

Definition Theory_behavioural : @Theory TheorySignature :=
  PropSet (fun pat =>

(* UndsEqlsSlshEqls_Bool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB1" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( UndsEqlsSlshEqls_Bool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( notBool_Unds_ ⋅ ⟨UndsEqlsEqls_Bool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarB1"; @kore_fevar _ _ _ SortBool "VarB2"⟩⟩ ) and ( Top{SortBool} ) ) ) )) \/

(* UndsEqlsSlshEqls_Int_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI1" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( UndsEqlsSlshEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( notBool_Unds_ ⋅ ⟨UndsEqlsEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; @kore_fevar _ _ _ SortInt "VarI2"⟩⟩ ) and ( Top{SortBool} ) ) ) )) \/

(* UndsEqlsSlshEqls_K_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK1" ) ) and ( ( ( @kore_fevar _ _ _ SortK "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( UndsEqlsSlshEqls_K_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortK "X0"; @kore_fevar _ _ _ SortK "X1"⟩ ) =k{R} ( ( notBool_Unds_ ⋅ ⟨UndsEqlsEqls_K_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortK "VarK1"; @kore_fevar _ _ _ SortK "VarK2"⟩⟩ ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( ( kore_dv SortBool "false" ) and ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen1" ) ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen1" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarB"; kore_dv SortBool "true"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "Var'Unds'Gen0"; kore_dv SortBool "false"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andThenBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( ( kore_dv SortBool "false" ) and ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen1" ) ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andThenBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen1" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andThenBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_andThenBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarK"; kore_dv SortBool "true"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarK" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andThenBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_andThenBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "Var'Unds'Gen0"; kore_dv SortBool "false"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_andThenBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andThenBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarK" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_divInt_Unds_ *)
(exists R, pat = existT R (( ( ( UndsEqlsSlshEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI2"; kore_dv SortInt "0"⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI1" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_divInt_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( UndsSlsh_Int_Unds_ ⋅ ⟨Unds__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; Unds_modInt_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; @kore_fevar _ _ _ SortInt "VarI2"⟩⟩; @kore_fevar _ _ _ SortInt "VarI2"⟩ ) and ( Top{SortInt} ) ) ) )) \/

(* Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI1" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( UndsEqlsEqls_Int_Unds_ ⋅ ⟨UndsPerc_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI2"; @kore_fevar _ _ _ SortInt "VarI1"⟩; kore_dv SortInt "0"⟩ ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_impliesBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_impliesBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarB"; kore_dv SortBool "false"⟩ ) =k{R} ( ( notBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarB"⟩ ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_impliesBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_impliesBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "Var'Unds'Gen0"; kore_dv SortBool "true"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_impliesBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "false" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_impliesBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_impliesBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_impliesBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_modInt_Unds_ simplification *)
(exists R, pat = existT R (( ( UndsEqlsSlshEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI2"; kore_dv SortInt "0"⟩ ) =k{R} ( kore_dv SortBool "true" ) ) --->ₖ ( ( Unds_modInt_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; @kore_fevar _ _ _ SortInt "VarI2"⟩ ) =k{R} ( ( UndsPerc_Int_Unds_ ⋅ ⟨UndsPlus_Int_Unds_ ⋅ ⟨UndsPerc_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI2"⟩⟩; absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI2"⟩⟩; absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI2"⟩⟩ ) and ( Top{SortInt} ) ) ) )) \/

(* Unds_orBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_orBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarB"; kore_dv SortBool "false"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_orBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_orBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "Var'Unds'Gen0"; kore_dv SortBool "true"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_orBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "false" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_orBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_orBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_orBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_orElseBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_orElseBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarK"; kore_dv SortBool "false"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarK" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_orElseBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_orElseBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "Var'Unds'Gen0"; kore_dv SortBool "true"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_orElseBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "false" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_orElseBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarK" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_orElseBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_orElseBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_xorBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_xorBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_xorBool_Unds_ simplification *)
(exists R, pat = existT R (( Top{R} ) --->ₖ ( ( Unds_xorBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "VarB"; kore_dv SortBool "false"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* Unds_xorBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "false" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_xorBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

(* UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortSet "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortSet "VarS1" ) ) and ( ( ( @kore_fevar _ _ _ SortSet "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortSet "VarS2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set ⋅ ⟨@kore_fevar _ _ _ SortSet "X0"; @kore_fevar _ _ _ SortSet "X1"⟩ ) =k{R} ( ( Unds_Set_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortSet "VarS1"; Set_Coln_difference ⋅ ⟨@kore_fevar _ _ _ SortSet "VarS2"; @kore_fevar _ _ _ SortSet "VarS1"⟩⟩ ) and ( Top{SortSet} ) ) ) )) \/

(* balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( (! ( kore_exists SortTree (( ( Unds_andBool_Unds_ ⋅ ⟨Unds_LT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨kore_bevar (In_nil)⟩; kore_dv SortInt "-1"⟩; Unds_LT_Eqls_Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_nil)⟩⟩; kore_dv SortInt "0"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( kore_bevar (In_nil) ) ) and ( Top{R} ) )) ) or ( ( kore_exists SortTree (( ( Unds_andBool_Unds_ ⋅ ⟨Unds_LT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨kore_bevar (In_nil)⟩; kore_dv SortInt "-1"⟩; Unds_GT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_nil)⟩⟩; kore_dv SortInt "0"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( kore_bevar (In_nil) ) ) and ( Top{R} ) )) ) or ( ( kore_exists SortTree (( ( Unds_andBool_Unds_ ⋅ ⟨Unds_GT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨kore_bevar (In_nil)⟩; kore_dv SortInt "1"⟩; Unds_LT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_nil)⟩⟩; kore_dv SortInt "0"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( kore_bevar (In_nil) ) ) and ( Top{R} ) )) ) or ( ( kore_exists SortTree (( ( Unds_andBool_Unds_ ⋅ ⟨Unds_GT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨kore_bevar (In_nil)⟩; kore_dv SortInt "1"⟩; Unds_GT_Eqls_Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_nil)⟩⟩; kore_dv SortInt "0"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( kore_bevar (In_nil) ) ) and ( Top{R} ) )) ) or ( ⊥{R} ) ) ) )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarT" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortTree "VarT" ) and ( Top{SortTree} ) ) ) )) \/

(* balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( ( Unds_andBool_Unds_ ⋅ ⟨Unds_LT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩; kore_dv SortInt "-1"⟩; Unds_LT_Eqls_Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩; kore_dv SortInt "0"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarT" ) ) and ( Top{R} ) ) ) --->ₖ ( ( balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( ( Unds_andBool_Unds_ ⋅ ⟨Unds_GT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩; kore_dv SortInt "1"⟩; Unds_LT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩; kore_dv SortInt "0"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarT" ) ) and ( Top{R} ) ) ) --->ₖ ( ( balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( ( Unds_andBool_Unds_ ⋅ ⟨Unds_GT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩; kore_dv SortInt "1"⟩; Unds_GT_Eqls_Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩; kore_dv SortInt "0"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarT" ) ) and ( Top{R} ) ) ) --->ₖ ( ( balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( ( Unds_andBool_Unds_ ⋅ ⟨Unds_LT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩; kore_dv SortInt "-1"⟩; Unds_GT__Int_Unds_ ⋅ ⟨balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩; kore_dv SortInt "0"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarT" ) ) and ( Top{R} ) ) ) --->ₖ ( ( balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( kore_dv SortInt "0" ) and ( Top{SortInt} ) ) ) )) \/

(* balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "VarL"; @kore_fevar _ _ _ SortTree "VarR"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( Unds__Int_Unds_ ⋅ ⟨height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarL"⟩; height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarR"⟩⟩ ) and ( Top{SortInt} ) ) ) )) \/

(* bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarIDX" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X2" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarLEN" ) ) and ( Top{R} ) ) ) ) ) --->ₖ ( ( bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"; @kore_fevar _ _ _ SortInt "X2"⟩ ) =k{R} ( ( Unds_modInt_Unds_ ⋅ ⟨Unds_GT__GT__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI"; @kore_fevar _ _ _ SortInt "VarIDX"⟩; Unds_LT__LT__Int_Unds_ ⋅ ⟨kore_dv SortInt "1"; @kore_fevar _ _ _ SortInt "VarLEN"⟩⟩ ) and ( Top{SortInt} ) ) ) )) \/

(* freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI" ) ) and ( Top{R} ) ) ) --->ₖ ( ( freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortInt "VarI" ) and ( Top{SortInt} ) ) ) )) \/

(* height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( kore_dv SortInt "0" ) and ( Top{SortInt} ) ) ) )) \/

(* height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortInt "VarH"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen2"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortInt "VarH" ) and ( Top{SortInt} ) ) ) )) \/

(* inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( Stop_List ⋅ ⟨⟩ ) and ( Top{SortList} ) ) ) )) \/

(* inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarV"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortTree "VarL"; @kore_fevar _ _ _ SortTree "VarR"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( Unds_List_Unds_ ⋅ ⟨Unds_List_Unds_ ⋅ ⟨inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarL"⟩; ListItem ⋅ ⟨kore_inj _ inj_SortInt_SortKItem (@kore_fevar _ _ _ SortInt "VarV")⟩⟩; inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarR"⟩⟩ ) and ( Top{SortList} ) ) ) )) \/

(* insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ ) and ( @kore_fevar _ _ _ SortTree "Var'Unds'Gen0" ) ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarV" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarV"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen0"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen0"⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int *)
(exists R, pat = existT R (( ( (! ( kore_exists SortInt (kore_exists SortInt (kore_exists SortInt (kore_exists SortTree (kore_exists SortTree (( ( Unds_LT__Int_Unds_ ⋅ ⟨kore_bevar (In_cons (In_cons (In_cons (In_cons (In_nil))))); kore_bevar (In_cons (In_cons (In_cons (In_nil))))⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_cons (In_cons (In_cons (In_nil)))); kore_bevar (In_cons (In_cons (In_nil))); kore_bevar (In_cons (In_nil)); kore_bevar (In_nil)⟩ ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( kore_bevar (In_cons (In_cons (In_cons (In_cons (In_nil))))) ) ) and ( Top{R} ) ) )))))) ) or ( ( kore_exists SortTree (kore_exists SortInt (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ ) and ( kore_bevar (In_cons (In_nil)) ) ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( kore_bevar (In_nil) ) ) and ( Top{R} ) ) ))) ) or ( ⊥{R} ) )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarX"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortTree "VarL"; @kore_fevar _ _ _ SortTree "VarR"⟩ ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarV" ) ) and ( Top{R} ) ) ) ) ) --->ₖ ( ( insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarX"; @kore_fevar _ _ _ SortTree "VarL"; insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortTree "VarR"; @kore_fevar _ _ _ SortInt "VarV"⟩⟩⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int *)
(exists R, pat = existT R (( ( ( Unds_LT__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarV"; @kore_fevar _ _ _ SortInt "VarX"⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarX"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortTree "VarL"; @kore_fevar _ _ _ SortTree "VarR"⟩ ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarV" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarX"; insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortTree "VarL"; @kore_fevar _ _ _ SortInt "VarV"⟩; @kore_fevar _ _ _ SortTree "VarR"⟩⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* isBool *)
(exists R, pat = existT R (( ( (! ( kore_exists SortBool (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortBool_SortKItem (kore_bevar (In_nil)); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isBool ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isBool *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortBool_SortKItem (@kore_fevar _ _ _ SortBool "VarBool"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isBool ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isInt *)
(exists R, pat = existT R (( ( (! ( kore_exists SortInt (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortInt_SortKItem (kore_bevar (In_nil)); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isInt ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isInt *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortInt_SortKItem (@kore_fevar _ _ _ SortInt "VarInt"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isInt ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isIntList *)
(exists R, pat = existT R (( ( (! ( kore_exists SortIntList (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortIntList_SortKItem (kore_bevar (In_nil)); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isIntList ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isIntList *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortIntList_SortKItem (@kore_fevar _ _ _ SortIntList "VarIntList"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isIntList ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isK *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) --->ₖ ( ( isK ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isKCellOpt *)
(exists R, pat = existT R (( ( (! ( kore_exists SortKCellOpt (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortKCellOpt_SortKItem (kore_bevar (In_nil)); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isKCellOpt ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isKCellOpt *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortKCellOpt_SortKItem (@kore_fevar _ _ _ SortKCellOpt "VarKCellOpt"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isKCellOpt ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isKItem *)
(exists R, pat = existT R (( ( (! ( kore_exists SortKItem (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_bevar (In_nil); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isKItem ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isKItem *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨@kore_fevar _ _ _ SortKItem "VarKItem"; dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isKItem ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isList *)
(exists R, pat = existT R (( ( (! ( kore_exists SortList (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortList_SortKItem (kore_bevar (In_nil)); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isList ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isList *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortList_SortKItem (@kore_fevar _ _ _ SortList "VarList"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isList ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isMap *)
(exists R, pat = existT R (( ( (! ( kore_exists SortMap (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortMap_SortKItem (kore_bevar (In_nil)); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isMap ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isMap *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortMap_SortKItem (@kore_fevar _ _ _ SortMap "VarMap"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isMap ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree *)
(exists R, pat = existT R (( ( (! ( kore_exists SortInt (kore_exists SortInt (kore_exists SortTree (kore_exists SortTree (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_cons (In_cons (In_cons (In_nil)))); kore_bevar (In_cons (In_cons (In_nil))); kore_bevar (In_cons (In_nil)); kore_bevar (In_nil)⟩ ) ) and ( Top{R} ) ))))) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen2"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen3"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isSet *)
(exists R, pat = existT R (( ( (! ( kore_exists SortSet (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortSet_SortKItem (kore_bevar (In_nil)); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isSet ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isSet *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortSet_SortKItem (@kore_fevar _ _ _ SortSet "VarSet"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isSet ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* isTree *)
(exists R, pat = existT R (( ( (! ( kore_exists SortTree (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortTree_SortKItem (kore_bevar (In_nil)); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) )) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( isTree ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* isTree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortTree_SortKItem (@kore_fevar _ _ _ SortTree "VarTree"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( isTree ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( (! ( kore_exists SortTree (kore_exists SortInt (kore_exists SortInt (kore_exists SortTree (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_cons (In_cons (In_nil))); kore_bevar (In_cons (In_nil)); kore_bevar (In_nil); kore_bevar (In_cons (In_cons (In_cons (In_nil))))⟩ ) ) and ( Top{R} ) ))))) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "VarL"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen2"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortTree "VarL" ) and ( Top{SortTree} ) ) ) )) \/

(* minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int *)
(exists R, pat = existT R (( ( ( Unds_LT__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; @kore_fevar _ _ _ SortInt "VarI2"⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI1" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortInt "VarI1" ) and ( Top{SortInt} ) ) ) )) \/

(* minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int *)
(exists R, pat = existT R (( ( ( Unds_GT_Eqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; @kore_fevar _ _ _ SortInt "VarI2"⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI1" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortInt "VarI2" ) and ( Top{SortInt} ) ) ) )) \/

(* node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarV" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarL" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X2" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarR" ) ) and ( Top{R} ) ) ) ) ) --->ₖ ( ( node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortTree "X1"; @kore_fevar _ _ _ SortTree "X2"⟩ ) =k{R} ( ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarV"; UndsPlus_Int_Unds_ ⋅ ⟨kore_dv SortInt "1"; maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarL"⟩; height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarR"⟩⟩⟩; @kore_fevar _ _ _ SortTree "VarL"; @kore_fevar _ _ _ SortTree "VarR"⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* notBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "false" ) ) and ( Top{R} ) ) ) --->ₖ ( ( notBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

(* notBool_Unds_ *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( Top{R} ) ) ) --->ₖ ( ( notBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

(* project_Coln_Bool *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortBool_SortKItem (@kore_fevar _ _ _ SortBool "VarK"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_Bool ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarK" ) and ( Top{SortBool} ) ) ) )) \/

(* project_Coln_Int *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortInt_SortKItem (@kore_fevar _ _ _ SortInt "VarK"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_Int ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortInt "VarK" ) and ( Top{SortInt} ) ) ) )) \/

(* project_Coln_IntList *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortIntList_SortKItem (@kore_fevar _ _ _ SortIntList "VarK"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_IntList ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortIntList "VarK" ) and ( Top{SortIntList} ) ) ) )) \/

(* project_Coln_K *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortK "VarK" ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_K ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortK "VarK" ) and ( Top{SortK} ) ) ) )) \/

(* project_Coln_KCellOpt *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortKCellOpt_SortKItem (@kore_fevar _ _ _ SortKCellOpt "VarK"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_KCellOpt ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortKCellOpt "VarK" ) and ( Top{SortKCellOpt} ) ) ) )) \/

(* project_Coln_KItem *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨@kore_fevar _ _ _ SortKItem "VarK"; dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_KItem ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortKItem "VarK" ) and ( Top{SortKItem} ) ) ) )) \/

(* project_Coln_List *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortList_SortKItem (@kore_fevar _ _ _ SortList "VarK"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_List ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortList "VarK" ) and ( Top{SortList} ) ) ) )) \/

(* project_Coln_Map *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortMap_SortKItem (@kore_fevar _ _ _ SortMap "VarK"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_Map ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortMap "VarK" ) and ( Top{SortMap} ) ) ) )) \/

(* project_Coln_Set *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortSet_SortKItem (@kore_fevar _ _ _ SortSet "VarK"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_Set ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortSet "VarK" ) and ( Top{SortSet} ) ) ) )) \/

(* project_Coln_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortK "X0" ) ⊆k{R} ( kseq ⋅ ⟨kore_inj _ inj_SortTree_SortKItem (@kore_fevar _ _ _ SortTree "VarK"); dotk ⋅ ⟨⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( project_Coln_Tree ⋅ ⟨@kore_fevar _ _ _ SortK "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortTree "VarK" ) and ( Top{SortTree} ) ) ) )) \/

(* pushList *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortKItem "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortKItem "VarK" ) ) and ( ( ( @kore_fevar _ _ _ SortList "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortList "VarL1" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( pushList ⋅ ⟨@kore_fevar _ _ _ SortKItem "X0"; @kore_fevar _ _ _ SortList "X1"⟩ ) =k{R} ( ( Unds_List_Unds_ ⋅ ⟨ListItem ⋅ ⟨@kore_fevar _ _ _ SortKItem "VarK"⟩; @kore_fevar _ _ _ SortList "VarL1"⟩ ) and ( Top{SortList} ) ) ) )) \/

(* rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( (! ( kore_exists SortInt (kore_exists SortInt (kore_exists SortTree (kore_exists SortTree (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_cons (In_cons (In_cons (In_nil)))); kore_bevar (In_cons (In_cons (In_nil))); kore_bevar (In_cons (In_nil)); kore_bevar (In_nil)⟩ ) ) and ( Top{R} ) ))))) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen2"; @kore_fevar _ _ _ SortTree "VarR"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortTree "VarR" ) and ( Top{SortTree} ) ) ) )) \/

(* rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarX"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortTree "VarA"; Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarY"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "VarB"; @kore_fevar _ _ _ SortTree "VarC"⟩⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarY"; node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarX"; @kore_fevar _ _ _ SortTree "VarA"; @kore_fevar _ _ _ SortTree "VarB"⟩; @kore_fevar _ _ _ SortTree "VarC"⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( ( isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree ⋅ ⟨leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarT" ) ) and ( Top{R} ) ) ) --->ₖ ( ( rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩; rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩; rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarY"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarX"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "VarA"; @kore_fevar _ _ _ SortTree "VarB"⟩; @kore_fevar _ _ _ SortTree "VarC"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarX"; @kore_fevar _ _ _ SortTree "VarA"; node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarY"; @kore_fevar _ _ _ SortTree "VarB"; @kore_fevar _ _ _ SortTree "VarC"⟩⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree *)
(exists R, pat = existT R (( ( ( isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree ⋅ ⟨rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "VarT" ) ) and ( Top{R} ) ) ) --->ₖ ( ( rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩; leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩; rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "VarT"⟩⟩⟩⟩ ) and ( Top{SortTree} ) ) ) )) \/

(* value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree *)
(exists R, pat = existT R (( ( (! ( kore_exists SortTree (kore_exists SortInt (kore_exists SortInt (kore_exists SortTree (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_cons (In_cons (In_nil))); kore_bevar (In_cons (In_nil)); kore_bevar (In_nil); kore_bevar (In_cons (In_cons (In_cons (In_nil))))⟩ ) ) and ( Top{R} ) ))))) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( kore_dv SortInt "0" ) and ( Top{SortInt} ) ) ) )) \/

(* value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarV"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen2"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortInt "VarV" ) and ( Top{SortInt} ) ) ) ))
  ).

Definition Theory_functional : @Theory TheorySignature :=
  PropSet (fun pat =>

(* Stop_List is functional *)
(exists R, pat = existT R (kore_exists SortList (( kore_bevar (In_nil) ) =k{R} ( Stop_List ⋅ ⟨⟩ )) )) \/

(* Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList is functional *)
(exists R, pat = existT R (kore_exists SortIntList (( kore_bevar (In_nil) ) =k{R} ( Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList ⋅ ⟨⟩ )) )) \/

(* LT__generatedTop__GT___fragment is functional *)
(exists R, pat = existT R (kore_exists SortGeneratedTopCellFragment (( kore_bevar (In_nil) ) =k{R} ( LT__generatedTop__GT___fragment ⋅ ⟨@kore_fevar _ _ _ SortKCellOpt "K0"; @kore_fevar _ _ _ SortGeneratedCounterCellOpt "K1"⟩ )) )) \/

(* Empty_Unds_TREE_Unds_Tree is functional *)
(exists R, pat = existT R (kore_exists SortTree (( kore_bevar (In_nil) ) =k{R} ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ )) )) \/

(* ListItem is functional *)
(exists R, pat = existT R (kore_exists SortList (( kore_bevar (In_nil) ) =k{R} ( ListItem ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"⟩ )) )) \/

(* Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree is functional *)
(exists R, pat = existT R (kore_exists SortTree (( kore_bevar (In_nil) ) =k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"; @kore_fevar _ _ _ SortTree "K2"; @kore_fevar _ _ _ SortTree "K3"⟩ )) )) \/

(* Set_Coln_difference is functional *)
(exists R, pat = existT R (kore_exists SortSet (( kore_bevar (In_nil) ) =k{R} ( Set_Coln_difference ⋅ ⟨@kore_fevar _ _ _ SortSet "K0"; @kore_fevar _ _ _ SortSet "K1"⟩ )) )) \/

(* UndsPlus_Int_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( UndsPlus_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList is functional *)
(exists R, pat = existT R (kore_exists SortIntList (( kore_bevar (In_nil) ) =k{R} ( UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortIntList "K1"⟩ )) )) \/

(* Unds__Int_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( Unds__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* Unds_LT_Eqls_Int_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_LT_Eqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* Unds_LT__Int_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_LT__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* UndsEqlsSlshEqls_Bool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsSlshEqls_Bool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* UndsEqlsSlshEqls_Int_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsSlshEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* UndsEqlsSlshEqls_K_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsSlshEqls_K_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortK "K0"; @kore_fevar _ _ _ SortK "K1"⟩ )) )) \/

(* UndsEqlsEqls_Bool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsEqls_Bool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* UndsEqlsEqls_Int_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* UndsEqlsEqls_K_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsEqls_K_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortK "K0"; @kore_fevar _ _ _ SortK "K1"⟩ )) )) \/

(* Unds_GT_Eqls_Int_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_GT_Eqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* Unds_GT__Int_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_GT__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* Unds_List_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortList (( kore_bevar (In_nil) ) =k{R} ( Unds_List_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortList "K0"; @kore_fevar _ _ _ SortList "K1"⟩ )) )) \/

(* Unds_andBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* Unds_andThenBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_andThenBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* Unds_impliesBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_impliesBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* Unds_orBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_orBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* Unds_orElseBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_orElseBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* Unds_xorBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_xorBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

(* UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set is functional *)
(exists R, pat = existT R (kore_exists SortSet (( kore_bevar (In_nil) ) =k{R} ( UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set ⋅ ⟨@kore_fevar _ _ _ SortSet "K0"; @kore_fevar _ _ _ SortSet "K1"⟩ )) )) \/

(* absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int is functional *)
(exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"⟩ )) )) \/

(* freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int is functional *)
(exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"⟩ )) )) \/

(* isBool is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isBool ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isInt is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isInt ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isIntList is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isIntList ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isK is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isK ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isKCellOpt is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isKCellOpt ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isKItem is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isKItem ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isList is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isList ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isMap is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isMap ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isSet is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isSet ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* isTree is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isTree ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

(* maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int is functional *)
(exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int is functional *)
(exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

(* notBool_Unds_ is functional *)
(exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( notBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"⟩ )) )) \/

(* pushList is functional *)
(exists R, pat = existT R (kore_exists SortList (( kore_bevar (In_nil) ) =k{R} ( pushList ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"; @kore_fevar _ _ _ SortList "K1"⟩ )) ))
  ).

      End TheorySyntax.
      Module TheorySemantics.
        Import TheorySyntax.

      Inductive SortK_carrier : Set :=
 | c_dotk
 | c_kseq(wjrhf:SortKItem_carrier) (snzoz:SortK_carrier)
with SortKItem_carrier : Set :=
 | c_inj_SortBool_SortKItem (b : SortBool_carrier)
 | c_inj_SortGeneratedCounterCell_SortKItem (b : SortGeneratedCounterCell_carrier)
 | c_inj_SortGeneratedCounterCellOpt_SortKItem (b : SortGeneratedCounterCellOpt_carrier)
 | c_inj_SortGeneratedTopCell_SortKItem (b : SortGeneratedTopCell_carrier)
 | c_inj_SortGeneratedTopCellFragment_SortKItem (b : SortGeneratedTopCellFragment_carrier)
 | c_inj_SortInt_SortKItem (b : SortInt_carrier)
 | c_inj_SortIntList_SortKItem (b : SortIntList_carrier)
 | c_inj_SortKCell_SortKItem (b : SortKCell_carrier)
 | c_inj_SortKCellOpt_SortKItem (b : SortKCellOpt_carrier)
 | c_inj_SortKConfigVar_SortKItem (b : SortKConfigVar_carrier)
 | c_inj_SortList_SortKItem (b : SortList_carrier)
 | c_inj_SortMap_SortKItem (b : SortMap_carrier)
 | c_inj_SortSet_SortKItem (b : SortSet_carrier)
 | c_inj_SortTree_SortKItem (b : SortTree_carrier)
with SortKCellOpt_carrier : Set :=
 | c_noKCell
 | c_inj_SortKCell_SortKCellOpt (b : SortKCell_carrier)
with SortTree_carrier : Set :=
 | c_Empty_Unds_TREE_Unds_Tree
 | c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree(oltyd:SortInt_carrier) (fexxy:SortInt_carrier) (ranvd:SortTree_carrier) (zkqgz:SortTree_carrier)
with SortKCell_carrier : Set :=
c_dv_SortKCell(v:bool)
with SortMap_carrier : Set :=
c_dv_SortMap(v:list (SortKItem_carrier * SortKItem_carrier))
with SortGeneratedCounterCellOpt_carrier : Set :=
 | c_inj_SortGeneratedCounterCell_SortGeneratedCounterCellOpt (b : SortGeneratedCounterCell_carrier)
with SortKConfigVar_carrier : Set :=
c_dv_SortKConfigVar(v:string)
with SortInt_carrier : Set :=
c_dv_SortInt(v:Z)
with SortSet_carrier : Set :=
c_dv_SortSet(v:list SortKItem_carrier)
with SortGeneratedTopCellFragment_carrier : Set :=
 | c___LT__generatedTop__GT___fragment(utklz:SortKCellOpt_carrier) (vayha:SortGeneratedCounterCellOpt_carrier)
with SortList_carrier : Set :=
c_dv_SortList(v:list SortKItem_carrier)
with SortGeneratedTopCell_carrier : Set :=
c_dv_SortGeneratedTopCell(v:bool)
with SortGeneratedCounterCell_carrier : Set :=
c_dv_SortGeneratedCounterCell(v:bool)
with SortIntList_carrier : Set :=
 | c__Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList
 | c__UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList(aycii:SortInt_carrier) (otiah:SortIntList_carrier)
with SortBool_carrier : Set :=
c_dv_SortBool(v:bool)
.

      Definition carrier (s : Ksorts) : Set := match s with
      SortK => SortK_carrier
|SortKItem => SortKItem_carrier
|SortKCellOpt => SortKCellOpt_carrier
|SortTree => SortTree_carrier
|SortKCell => SortKCell_carrier
|SortMap => SortMap_carrier
|SortGeneratedCounterCellOpt => SortGeneratedCounterCellOpt_carrier
|SortKConfigVar => SortKConfigVar_carrier
|SortInt => SortInt_carrier
|SortSet => SortSet_carrier
|SortGeneratedTopCellFragment => SortGeneratedTopCellFragment_carrier
|SortList => SortList_carrier
|SortGeneratedTopCell => SortGeneratedTopCell_carrier
|SortGeneratedCounterCell => SortGeneratedCounterCell_carrier
|SortIntList => SortIntList_carrier
|SortBool => SortBool_carrier
      end.

      Scheme Boolean Equality for SortK_carrier.
      Definition retr_SortKItem_SortBool x := match x with
  | c_inj_SortBool_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortInt x := match x with
  | c_inj_SortInt_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortGeneratedTopCell x := match x with
  | c_inj_SortGeneratedTopCell_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortMap x := match x with
  | c_inj_SortMap_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortKCell x := match x with
  | c_inj_SortKCell_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortGeneratedCounterCellOpt x := match x with
  | c_inj_SortGeneratedCounterCell_SortKItem x => Some (c_inj_SortGeneratedCounterCell_SortGeneratedCounterCellOpt x)
  | c_inj_SortGeneratedCounterCellOpt_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortGeneratedCounterCell x := match x with
  | c_inj_SortGeneratedCounterCell_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortTree x := match x with
  | c_inj_SortTree_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortGeneratedTopCellFragment x := match x with
  | c_inj_SortGeneratedTopCellFragment_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortIntList x := match x with
  | c_inj_SortIntList_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortSet x := match x with
  | c_inj_SortSet_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortList x := match x with
  | c_inj_SortList_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortKCellOpt x := match x with
  | c_inj_SortKCell_SortKItem x => Some (c_inj_SortKCell_SortKCellOpt x)
  | c_inj_SortKCellOpt_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortKConfigVar x := match x with
  | c_inj_SortKConfigVar_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKCellOpt_SortKCell x := match x with
  | c_inj_SortKCell_SortKCellOpt x => Some x
  | _ => None end.


      Definition _894c13c (x0:SortK_carrier) : option SortKCell_carrier
   := match x0 with  c_kseq (c_inj_SortKCell_SortKItem K) tk => Some K
  | _ => None end
.
Definition _f68a616 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _0e7f507 (x0:SortK_carrier) : option SortSet_carrier
   := match x0 with  c_kseq (c_inj_SortSet_SortKItem K) tk => Some K
  | _ => None end
.
Definition _105572a (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _1242e49 (x0:SortK_carrier) : option SortKItem_carrier
   := match x0 with  c_kseq K tk => Some K
  | _ => None end
.
Definition _83812b6 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _cdf99a2 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _7e746e2 (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Empty_Unds_TREE_Unds_Tree => Some (c_dv_SortInt 0)
  | _ => None end
.
Definition _54f8b2b (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 H _Gen1 _Gen2 => Some H
  | _ => None end
.
Definition _1ff8f4d {SortSort_carrier : Type} (x0:SortBool_carrier) (x1:SortSort_carrier) (x2:SortSort_carrier) : option SortSort_carrier
   := match x0,x1,x2 with  C, B1, _Gen0 => 
    match C with (c_dv_SortBool b) => if b then (Some (B1)) else None end end
.
Definition _19729cf (x0:SortTree_carrier) : option SortBool_carrier
   := match x0 with  _Gen0 => Some (c_dv_SortBool false) end
.
Definition _c385138 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  _Gen0 => Some c_Empty_Unds_TREE_Unds_Tree end
.
Definition _d5d5965 (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree V _Gen0 _Gen1 _Gen2 => Some V
  | _ => None end
.
Definition _42dba6c (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 _Gen1 L _Gen2 => Some L
  | _ => None end
.
Definition _aa256d5 (x0:SortTree_carrier) : option SortBool_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 _Gen1 _Gen2 _Gen3 => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _62d53c4 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 _Gen1 _Gen2 R => Some R
  | _ => None end
.
Definition _7fa9c19 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  _Gen0 => Some c_Empty_Unds_TREE_Unds_Tree end
.
Definition _e56be4f (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  _Gen0 => Some (c_dv_SortInt 0) end
.
Definition _c620995 (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Empty_Unds_TREE_Unds_Tree => Some (c_dv_SortInt 0)
  | _ => None end
.
Definition _f316b87 (x0:SortK_carrier) : option SortInt_carrier
   := match x0 with  c_kseq (c_inj_SortInt_SortKItem K) tk => Some K
  | _ => None end
.
Definition _031237d (x0:SortK_carrier) : option SortMap_carrier
   := match x0 with  c_kseq (c_inj_SortMap_SortKItem K) tk => Some K
  | _ => None end
.
Definition _63c1d06 (x0:SortK_carrier) : option SortIntList_carrier
   := match x0 with  c_kseq (c_inj_SortIntList_SortKItem K) tk => Some K
  | _ => None end
.
Definition _9a3f841 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _2b75eac (x0:SortK_carrier) : option SortList_carrier
   := match x0 with  c_kseq (c_inj_SortList_SortKItem K) tk => Some K
  | _ => None end
.
Definition _f684dd7 (x0:SortK_carrier) : option SortKCellOpt_carrier
   := match x0 with  c_kseq _Pat0 tk => match (retr_SortKItem_SortKCellOpt) _Pat0 with
    | Some K => Some K
    | _ => None
  end | _ => None end
.
Definition _92664aa (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortInt_SortKItem int) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _2b5aadc (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _dadad71 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortBool_SortKItem Bool) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _495da55 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _513dc3f (x0:SortK_carrier) : option SortTree_carrier
   := match x0 with  c_kseq (c_inj_SortTree_SortKItem K) tk => Some K
  | _ => None end
.
Definition _25b529d (x0:SortK_carrier) : option SortK_carrier
   := match x0 with  K => Some K end
.
Definition _1516473 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq _Pat0 tk => match (retr_SortKItem_SortKCellOpt) _Pat0 with
    | Some KCellOpt => Some (c_dv_SortBool true)
    | _ => None
  end | _ => None end
.
Definition _d30be57 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _2695222 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortKCell_SortKItem KCell) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _c0705f1 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => Some T end
.
Definition _9a9489a (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _16ff77c (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool true) end
.
Definition _5352e22 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortTree_SortKItem Tree) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _f205bc4 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortSet_SortKItem _Set) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _7d4dddf (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortList_SortKItem List) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _6fb2c05 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortIntList_SortKItem intList) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _41e0b3a (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _5872f0d (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortBool_SortKItem K) tk => Some K
  | _ => None end
.
Definition _6f30a20 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false) end
.
Definition _4879c0f (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortMap_SortKItem Map) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _ed3c25a (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq KItem tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _0ef0a00 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortKConfigVar_SortKItem KConfigVar) tk => Some (c_dv_SortBool true)
  | _ => None end
.
Definition _cf2cb8f (x0:SortInt_carrier) : option SortInt_carrier
   := match x0 with  i => Some i end
.
Definition project_KCell (x0 : SortK_carrier) : option SortKCell_carrier := _894c13c x0
.
Definition project_Set (x0 : SortK_carrier) : option SortSet_carrier := _0e7f507 x0
.
Definition project_KItem (x0 : SortK_carrier) : option SortKItem_carrier := _1242e49 x0
.
Definition height____TREE_Int_Tree (x0 : SortTree_carrier) : option SortInt_carrier := (_54f8b2b x0) <|> (_7e746e2 x0)
.
Definition leftT____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := (_42dba6c x0) <|> (_c385138 x0)
.
Definition isNode____TREE_Bool_Tree (x0 : SortTree_carrier) : option SortBool_carrier := (_aa256d5 x0) <|> (_19729cf x0)
.
Definition rightT____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := (_62d53c4 x0) <|> (_7fa9c19 x0)
.
Definition value____TREE_Int_Tree (x0 : SortTree_carrier) : option SortInt_carrier := (_d5d5965 x0) <|> (_e56be4f x0)
.
Definition project_Int (x0 : SortK_carrier) : option SortInt_carrier := _f316b87 x0
.
Definition project_Map (x0 : SortK_carrier) : option SortMap_carrier := _031237d x0
.
Definition project_IntList (x0 : SortK_carrier) : option SortIntList_carrier := _63c1d06 x0
.
Definition project_List (x0 : SortK_carrier) : option SortList_carrier := _2b75eac x0
.
Definition project_KCellOpt (x0 : SortK_carrier) : option SortKCellOpt_carrier := _f684dd7 x0
.
Definition isInt (x0 : SortK_carrier) : option SortBool_carrier := (_92664aa x0) <|> (_105572a x0)
.
Definition isBool (x0 : SortK_carrier) : option SortBool_carrier := (_dadad71 x0) <|> (_495da55 x0)
.
Definition project_Tree (x0 : SortK_carrier) : option SortTree_carrier := _513dc3f x0
.
Definition project_K (x0 : SortK_carrier) : option SortK_carrier := _25b529d x0
.
Definition isKCellOpt (x0 : SortK_carrier) : option SortBool_carrier := (_1516473 x0) <|> (_9a3f841 x0)
.
Definition isKCell (x0 : SortK_carrier) : option SortBool_carrier := (_2695222 x0) <|> (_d30be57 x0)
.
Definition _fd8faca (x0:SortInt_carrier) (x1:SortInt_carrier) : option SortBool_carrier
   := match x0,x1 with  i1, i2 => 
    _Val0 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.rem x) y))) i2 i1 ;
    _Val1 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.eqb x) y))) _Val0 (c_dv_SortInt 0) ;
    mret _Val1 end
.
Definition isK (x0 : SortK_carrier) : option SortBool_carrier := _16ff77c x0
.
Definition _f6efc09 (x0:SortTree_carrier) : option SortList_carrier
   := match x0 with  c_Empty_Unds_TREE_Unds_Tree => 
    _Val0 ← (Some (c_dv_SortList [])) ;
    mret _Val0
  | _ => None end
.
Definition isTree (x0 : SortK_carrier) : option SortBool_carrier := (_5352e22 x0) <|> (_cdf99a2 x0)
.
Definition isSet (x0 : SortK_carrier) : option SortBool_carrier := (_f205bc4 x0) <|> (_2b5aadc x0)
.
Definition isList (x0 : SortK_carrier) : option SortBool_carrier := (_7d4dddf x0) <|> (_9a9489a x0)
.
Definition isIntList (x0 : SortK_carrier) : option SortBool_carrier := (_6fb2c05 x0) <|> (_41e0b3a x0)
.
Definition project_Bool (x0 : SortK_carrier) : option SortBool_carrier := _5872f0d x0
.
Definition isMap (x0 : SortK_carrier) : option SortBool_carrier := (_4879c0f x0) <|> (_6f30a20 x0)
.
Definition isKItem (x0 : SortK_carrier) : option SortBool_carrier := (_ed3c25a x0) <|> (_83812b6 x0)
.
Definition isKConfigVar (x0 : SortK_carrier) : option SortBool_carrier := (_0ef0a00 x0) <|> (_f68a616 x0)
.
Definition freshInt____INT_Int_Int (x0 : SortInt_carrier) : option SortInt_carrier := _cf2cb8f x0
.
Definition _780a187 (x0:SortInt_carrier) (x1:SortTree_carrier) (x2:SortTree_carrier) : option SortTree_carrier
   := match x0,x1,x2 with  V, L, R => 
    _Val0 ← height____TREE_Int_Tree L ;
    _Val1 ← height____TREE_Int_Tree R ;
    _Val2 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.max x) y))) _Val0 _Val1 ;
    _Val3 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.add x) y))) (c_dv_SortInt 1) _Val2 ;
    mret (c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree V _Val3 L R) end
.
Definition _533014b (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 _Gen1 L R => 
    _Val0 ← height____TREE_Int_Tree L ;
    _Val1 ← height____TREE_Int_Tree R ;
    _Val2 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y))) _Val0 _Val1 ;
    mret _Val2
  | _ => None end
.
Definition _2f3f58a {SortSort_carrier : Type} (x0:SortBool_carrier) (x1:SortSort_carrier) (x2:SortSort_carrier) : option SortSort_carrier
   := match x0,x1,x2 with  C, _Gen0, B2 => 
    _Val0 ← (fun (x: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect _ negb x))) C ;
    match _Val0 with (c_dv_SortBool b) => if b then (Some (B2)) else None end end
.
Definition _dividesInt__INT_COMMON_Bool_Int_Int (x0 : SortInt_carrier) (x1 : SortInt_carrier) : option SortBool_carrier := _fd8faca x0 x1
.
Fixpoint inorder____TREE_List_Tree (x0 : SortTree_carrier) : option SortList_carrier  := 
let _fdf0244 (x0:SortTree_carrier) : option SortList_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree V _Gen0 L R => 
    _Val0 ← inorder____TREE_List_Tree L ;
    _Val1 ← (fun x => Some (c_dv_SortList [x])) ((c_inj_SortInt_SortKItem) V) ;
    _Val2 ← (fun xs ys => Some (c_dv_SortList (SortList_carrier_rect (fun _ => list SortKItem_carrier) (SortList_carrier_rect _ List.app xs) ys))) _Val0 _Val1 ;
    _Val3 ← inorder____TREE_List_Tree R ;
    _Val4 ← (fun xs ys => Some (c_dv_SortList (SortList_carrier_rect (fun _ => list SortKItem_carrier) (SortList_carrier_rect _ List.app xs) ys))) _Val2 _Val3 ;
    mret _Val4
  | _ => None end in
 (_f6efc09 x0) <|> (_fdf0244 x0)
.
Definition node________TREE_Tree_Int_Tree_Tree (x0 : SortInt_carrier) (x1 : SortTree_carrier) (x2 : SortTree_carrier) : option SortTree_carrier := _780a187 x0 x1 x2
.
Definition balanceFactor____TREE_Int_Tree (x0 : SortTree_carrier) : option SortInt_carrier := (_533014b x0) <|> (_c620995 x0)
.
Definition kite {SortSort_carrier : Type} (x0 : SortBool_carrier) (x1 : SortSort_carrier) (x2 : SortSort_carrier) : option SortSort_carrier := (_1ff8f4d x0 x1 x2) <|> (_2f3f58a x0 x1 x2)
.
Definition _3b67f4b (x0:SortInt_carrier) (x1:SortInt_carrier) (x2:SortInt_carrier) : option SortInt_carrier
   := match x0,x1,x2 with  i, iDX, LEN => 
    _Val0 ← (fun x y z => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ bitRange x) y) z))) i iDX LEN ;
    _Val1 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y))) LEN (c_dv_SortInt 1) ;
    _Val2 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y))) (c_dv_SortInt 1) _Val1 ;
    _Val3 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.add x) y))) _Val0 _Val2 ;
    _Val4 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y))) (c_dv_SortInt 1) LEN ;
    _Val5 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ emod x) y))) _Val3 _Val4 ;
    _Val6 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y))) LEN (c_dv_SortInt 1) ;
    _Val7 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y))) (c_dv_SortInt 1) _Val6 ;
    _Val8 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y))) _Val5 _Val7 ;
    mret _Val8 end
.
Definition _1a74dc5 (x0:SortTree_carrier) (x1:SortInt_carrier) : option SortTree_carrier
   := match x0,x1 with  c_Empty_Unds_TREE_Unds_Tree, V => 
    _Val0 ← node________TREE_Tree_Int_Tree_Tree V c_Empty_Unds_TREE_Unds_Tree c_Empty_Unds_TREE_Unds_Tree ;
    mret _Val0
  | _, _ => None end
.
Definition _bd2ae08 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree Y _Gen0 (c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree X _Gen1 A B) C => 
    _Val0 ← node________TREE_Tree_Int_Tree_Tree Y B C ;
    _Val1 ← node________TREE_Tree_Int_Tree_Tree X A _Val0 ;
    mret _Val1
  | _ => None end
.
Definition _f76f624 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree X _Gen0 A (c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree Y _Gen1 B C) => 
    _Val0 ← node________TREE_Tree_Int_Tree_Tree X A B ;
    _Val1 ← node________TREE_Tree_Int_Tree_Tree Y _Val0 C ;
    mret _Val1
  | _ => None end
.
Definition signExtendBitRangeInt________INT_COMMON_Int_Int_Int_Int (x0 : SortInt_carrier) (x1 : SortInt_carrier) (x2 : SortInt_carrier) : option SortInt_carrier := _3b67f4b x0 x1 x2
.
Definition rotateRight____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := _bd2ae08 x0
.
Definition rotateLeft____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := _f76f624 x0
.
Definition _143cf23 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => 
    _Val0 ← balanceFactor____TREE_Int_Tree T ;
    _Val1 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.gtb x) y))) _Val0 (c_dv_SortInt 1) ;
    _Val2 ← leftT____TREE_Tree_Tree T ;
    _Val3 ← balanceFactor____TREE_Int_Tree _Val2 ;
    _Val4 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.geb x) y))) _Val3 (c_dv_SortInt 0) ;
    _Val5 ← (fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y))) _Val1 _Val4 ;
    _Val6 ← rotateRight____TREE_Tree_Tree T ;
    match _Val5 with (c_dv_SortBool b) => if b then (Some (_Val6)) else None end end
.
Definition _a4ef7ef (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => 
    _Val0 ← balanceFactor____TREE_Int_Tree T ;
    _Val1 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.ltb x) y))) _Val0 (c_dv_SortInt (-1)) ;
    _Val2 ← rightT____TREE_Tree_Tree T ;
    _Val3 ← balanceFactor____TREE_Int_Tree _Val2 ;
    _Val4 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.leb x) y))) _Val3 (c_dv_SortInt 0) ;
    _Val5 ← (fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y))) _Val1 _Val4 ;
    _Val6 ← rotateLeft____TREE_Tree_Tree T ;
    match _Val5 with (c_dv_SortBool b) => if b then (Some (_Val6)) else None end end
.
Definition _b647727 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => 
    _Val0 ← leftT____TREE_Tree_Tree T ;
    _Val1 ← isNode____TREE_Bool_Tree _Val0 ;
    _Val2 ← value____TREE_Int_Tree T ;
    _Val3 ← leftT____TREE_Tree_Tree T ;
    _Val4 ← rotateLeft____TREE_Tree_Tree _Val3 ;
    _Val5 ← rightT____TREE_Tree_Tree T ;
    _Val6 ← node________TREE_Tree_Int_Tree_Tree _Val2 _Val4 _Val5 ;
    _Val7 ← rotateRight____TREE_Tree_Tree _Val6 ;
    match _Val1 with (c_dv_SortBool b) => if b then (Some (_Val7)) else None end end
.
Definition _15d45ab (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => 
    _Val0 ← rightT____TREE_Tree_Tree T ;
    _Val1 ← isNode____TREE_Bool_Tree _Val0 ;
    _Val2 ← value____TREE_Int_Tree T ;
    _Val3 ← leftT____TREE_Tree_Tree T ;
    _Val4 ← rightT____TREE_Tree_Tree T ;
    _Val5 ← rotateRight____TREE_Tree_Tree _Val4 ;
    _Val6 ← node________TREE_Tree_Int_Tree_Tree _Val2 _Val3 _Val5 ;
    _Val7 ← rotateLeft____TREE_Tree_Tree _Val6 ;
    match _Val1 with (c_dv_SortBool b) => if b then (Some (_Val7)) else None end end
.
Definition rotateLeftRight____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := _b647727 x0
.
Definition rotateRightLeft____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := _15d45ab x0
.
Definition _d5a13c7 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => 
    _Val0 ← balanceFactor____TREE_Int_Tree T ;
    _Val1 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.gtb x) y))) _Val0 (c_dv_SortInt 1) ;
    _Val2 ← leftT____TREE_Tree_Tree T ;
    _Val3 ← balanceFactor____TREE_Int_Tree _Val2 ;
    _Val4 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.ltb x) y))) _Val3 (c_dv_SortInt 0) ;
    _Val5 ← (fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y))) _Val1 _Val4 ;
    _Val6 ← rotateLeftRight____TREE_Tree_Tree T ;
    match _Val5 with (c_dv_SortBool b) => if b then (Some (_Val6)) else None end end
.
Definition _db49e2d (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => 
    _Val0 ← balanceFactor____TREE_Int_Tree T ;
    _Val1 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.ltb x) y))) _Val0 (c_dv_SortInt (-1)) ;
    _Val2 ← rightT____TREE_Tree_Tree T ;
    _Val3 ← balanceFactor____TREE_Int_Tree _Val2 ;
    _Val4 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.gtb x) y))) _Val3 (c_dv_SortInt 0) ;
    _Val5 ← (fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y))) _Val1 _Val4 ;
    _Val6 ← rotateRightLeft____TREE_Tree_Tree T ;
    match _Val5 with (c_dv_SortBool b) => if b then (Some (_Val6)) else None end end
.
Definition balance____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := (_143cf23 x0) <|> (_a4ef7ef x0) <|> (_d5a13c7 x0) <|> (_db49e2d x0) <|> (_c0705f1 x0)
.
Fixpoint insert______TREE_Tree_Tree_Int (x0 : SortTree_carrier) (x1 : SortInt_carrier) : option SortTree_carrier  := 
let _2fb2b0c (x0:SortTree_carrier) (x1:SortInt_carrier) : option SortTree_carrier
   := match x0,x1 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree X _Gen0 L R, V => 
    _Val0 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.ltb x) y))) V X ;
    _Val1 ← insert______TREE_Tree_Tree_Int L V ;
    _Val2 ← node________TREE_Tree_Int_Tree_Tree X _Val1 R ;
    _Val3 ← balance____TREE_Tree_Tree _Val2 ;
    match _Val0 with (c_dv_SortBool b) => if b then (Some (_Val3)) else None
  end | _, _ => None end in
let _edaaa1f (x0:SortTree_carrier) (x1:SortInt_carrier) : option SortTree_carrier
   := match x0,x1 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree X _Gen0 L R, V => 
    _Val0 ← insert______TREE_Tree_Tree_Int R V ;
    _Val1 ← node________TREE_Tree_Int_Tree_Tree X L _Val0 ;
    _Val2 ← balance____TREE_Tree_Tree _Val1 ;
    mret _Val2
  | _, _ => None end in
 (_1a74dc5 x0 x1) <|> (_2fb2b0c x0 x1) <|> (_edaaa1f x0 x1)
. 

       (*TODO make sure we only include the below lines if the sort is present*)

      Definition parser (s : Ksorts) : string -> option (carrier s) :=
            match s with
             | SortInt => map_parser c_dv_SortInt Z_parser
             | SortBool => map_parser c_dv_SortBool bool_parser
             (* extend here with MInt, and other DVs *)
             | _ => None_parser
            end.

      Definition P (σ : symbol) := foldr (λ c a, carrier c -> a) (option (carrier (ret_sort σ))) (arg_sorts σ).

      Program Definition Model : @Model TheorySignature :=
        mkModel_partial
          carrier (* (Ksorts_rect _ SortK_carrier SortKItem_carrier SortKCellOpt_carrier SortTree_carrier SortKCell_carrier SortMap_carrier SortGeneratedCounterCellOpt_carrier SortKConfigVar_carrier SortInt_carrier SortSet_carrier SortGeneratedTopCellFragment_carrier SortList_carrier SortGeneratedTopCell_carrier SortGeneratedCounterCell_carrier SortIntList_carrier SortBool_carrier) *)
          (Ksyms_rect P (fun x0 x1 => Some (c_kseq x0 x1))
(Some c_dotk)
(fun xs ys => Some ((fix append xs ys := match xs with c_dotk => ys | c_kseq x xs => c_kseq x (append xs ys) end) xs ys))(*append*)
(Some (c_dv_SortList []))(*.List*)
(Some c__Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList)
(fun x0 x1 => Some (c___LT__generatedTop__GT___fragment x0 x1))
(Some c_Empty_Unds_TREE_Unds_Tree)
(fun x => Some (c_dv_SortList [x]))(*ListItem*)
(fun x0 x1 x2 x3 => Some (c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree x0 x1 x2 x3))
(fun xs ys => Some (c_dv_SortSet (SortSet_carrier_rect (fun _ => list SortKItem_carrier) (SortSet_carrier_rect _ (SSet.difference SortKItem_carrier_beq) xs) ys)))(*Set:difference*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.rem x) y)))(*_%Int_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.add x) y)))(*_+Int_*)
(fun x0 x1 => Some (c__UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList x0 x1))
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y)))(*_-Int_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.quot x) y)))(*_/Int_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y)))(*_<<Int_*)
(fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.leb x) y)))(*_<=Int_*)
(fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.ltb x) y)))(*_<Int_*)
(fun x y => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ neqbB x) y)))(*_=/=Bool_*)
(fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ neqbZ x) y)))(*_=/=Int_*)
(fun x y => Some (c_dv_SortBool (negb (SortK_carrier_beq x y))))(*_=/=K_*)
(fun x y => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ Bool.eqb x) y)))(*_==Bool_*)
(fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.eqb x) y)))(*_==Int_*)
(fun x y => Some (c_dv_SortBool (SortK_carrier_beq x y)))(*_==K_*)
(fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.geb x) y)))(*_>=Int_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftr x) y)))(*_>>Int_*)
(fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.gtb x) y)))(*_>Int_*)
(fun xs ys => Some (c_dv_SortList (SortList_carrier_rect (fun _ => list SortKItem_carrier) (SortList_carrier_rect _ List.app xs) ys)))(*_List_*)
(fun xs ys => c_dv_SortSet <$> (SortSet_carrier_rect (fun _ => option (list SortKItem_carrier)) (SortSet_carrier_rect _ (SSet.concat SortKItem_carrier_beq) xs) ys))(*_Set_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y)))(*_andBool_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y)))(*_andThenBool_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ ediv x) y)))(*_divInt_*)
_dividesInt__INT_COMMON_Bool_Int_Int
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ implb x) y)))(*_impliesBool_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ emod x) y)))(*_modInt_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ orb x) y)))(*_orBool_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ orb x) y)))(*_orElseBool_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ xorb x) y)))(*_xorBool_*)
(fun xs ys => Some (c_dv_SortSet (SortSet_carrier_rect (fun _ => list SortKItem_carrier) (SortSet_carrier_rect _ (SSet.union SortKItem_carrier_beq) xs) ys)))(*_|Set__SET_Set_Set_Set*)
(fun x => Some (c_dv_SortInt (SortInt_carrier_rect _ Z.abs x)))(*absInt(_)_INT-COMMON_Int_Int*)
balance____TREE_Tree_Tree
balanceFactor____TREE_Int_Tree
(fun x y z => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ bitRange x) y) z)))(*bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int*)
freshInt____INT_Int_Int
height____TREE_Int_Tree
inorder____TREE_List_Tree
insert______TREE_Tree_Tree_Int
isBool
isInt
isIntList
isK
isKCell
isKCellOpt
isKConfigVar
isKItem
isList
isMap
isNode____TREE_Bool_Tree
isSet
isTree
leftT____TREE_Tree_Tree
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.max x) y)))(*maxInt(_,_)_INT-COMMON_Int_Int_Int*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.min x) y)))(*minInt(_,_)_INT-COMMON_Int_Int_Int*)
(Some c_noKCell)
node________TREE_Tree_Int_Tree_Tree
(fun (x: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect _ negb x)))(*notBool_*)
project_Bool
project_Int
project_IntList
project_K
project_KCell
project_KCellOpt
project_KItem
project_List
project_Map
project_Set
project_Tree
(fun x xs => Some (c_dv_SortList (SortList_carrier_rect _ (fun xs => x :: xs) xs)))(*pushList*)
rightT____TREE_Tree_Tree
rotateLeft____TREE_Tree_Tree
rotateLeftRight____TREE_Tree_Tree
rotateRight____TREE_Tree_Tree
rotateRightLeft____TREE_Tree_Tree
value____TREE_Int_Tree)
          _ _ (parser).
      Next Obligation.
        destruct s; repeat constructor.
      Defined.
      Final Obligation.
        intros s1 s2 H x; inversion H; subst.
      * exact (c_inj_SortBool_SortKItem x).
* exact (c_inj_SortInt_SortKItem x).
* exact (c_inj_SortGeneratedTopCell_SortKItem x).
* exact (c_inj_SortMap_SortKItem x).
* exact (c_inj_SortKCell_SortKItem x).
* exact (c_inj_SortGeneratedCounterCellOpt_SortKItem x).
* exact (c_inj_SortGeneratedCounterCell_SortKItem x).
* exact (c_inj_SortTree_SortKItem x).
* exact (c_inj_SortGeneratedTopCellFragment_SortKItem x).
* exact (c_inj_SortIntList_SortKItem x).
* exact (c_inj_SortSet_SortKItem x).
* exact (c_inj_SortList_SortKItem x).
* exact (c_inj_SortKCellOpt_SortKItem x).
* exact (c_inj_SortKConfigVar_SortKItem x).
* exact (c_inj_SortKCell_SortKCellOpt x).
* exact (c_inj_SortGeneratedCounterCell_SortGeneratedCounterCellOpt x).
Defined.

(*   Ltac remember_fresh :=
    match goal with
    | [ |- context [@fresh_evar ?Σ ?ex ?ex' ?mu ?s ?φ] ] =>
      let F := fresh "F" in
      let HF := fresh "HF" in
      let HeqF := fresh "HeqF" in
      pose proof (@fresh_evar_is_fresh Σ ex ex' mu s φ ) as HF;
      simpl in HF;
      remember (@fresh_evar Σ ex ex' mu s φ) as F eqn:HeqF;
      clear HeqF
    end. *)

(*   Ltac solve_ineqs :=
  match goal with
  | |- context [decide (?F = ?X)] =>
    idtac "solving eqs";
    (
    (rewrite decide_eq_same; simpl) ||
    (
      let P := fresh "P" in
      destruct (decide (F = X)) eqn:P; [set_solver|
        try rewrite P])
    )
  end. *)

(* Ltac simplify_equality :=
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
    end. *)

(* Ltac idtac AXIOM :=
  match goal with
  | [t : Semantics.carrier _ (projT1 (existT _ ?ax)) |- _] => idtac ax
  end. *)

  Goal satT Theory_functional Model.
  Proof.
    unfold satT, satM, Theory_functional. intros.
    unfold_elem_of; destruct_or?; destruct_ex?; subst; cbn.
    all: try (solve_functional_axiom_option_sym; cbn; clear; repeat dependent destruction l; cbv; try congruence; repeat case_match; congruence).
  Defined.

  Lemma propset_SortInt :
    forall A P,
      (propset_fa_union (fun x : SortInt_carrier => P x) : propset A) =
      (propset_fa_union (fun z : Z => P (c_dv_SortInt z)) : propset A).
  Proof.
    intros. unfold propset_fa_union.
    f_equal. extensionality c.
    apply PropExtensionality.propositional_extensionality.
    split; intros [].
    - destruct x. exists v. assumption.
    - exists (c_dv_SortInt x). assumption.
  Qed.

  Lemma propset_SortBool :
    forall A P,
      (propset_fa_union (fun x : SortBool_carrier => P x) : propset A) =
      (propset_fa_union (fun b : bool => P (c_dv_SortBool b)) : propset A).
  Proof.
    intros. unfold propset_fa_union.
    f_equal. extensionality c.
    apply PropExtensionality.propositional_extensionality.
    split; intros [].
    - destruct x. exists v. assumption.
    - exists (c_dv_SortBool x). assumption.
  Qed.

  Lemma propset_SortList :
    forall A P,
      (propset_fa_union (fun x : SortList_carrier => P x) : propset A) =
      (propset_fa_union (fun x : list _ => P (c_dv_SortList x)) : propset A).
  Proof.
    intros. unfold propset_fa_union.
    f_equal. extensionality c.
    apply PropExtensionality.propositional_extensionality.
    split; intros [].
    - destruct x. exists v. assumption.
    - exists (c_dv_SortList x). assumption.
  Qed.

  Lemma propset_SortSet :
    forall A P,
      (propset_fa_union (fun x : SortSet_carrier => P x) : propset A) =
      (propset_fa_union (fun x : list _ => P (c_dv_SortSet x)) : propset A).
  Proof.
    intros. unfold propset_fa_union.
    f_equal. extensionality c.
    apply PropExtensionality.propositional_extensionality.
    split; intros [].
    - destruct x. exists v. assumption.
    - exists (c_dv_SortSet x). assumption.
  Qed.

  Lemma propset_SortMap :
    forall A P,
      (propset_fa_union (fun x : SortSet_carrier => P x) : propset A) =
      (propset_fa_union (fun x : list _ => P (c_dv_SortSet x)) : propset A).
  Proof.
    intros. unfold propset_fa_union.
    f_equal. extensionality c.
    apply PropExtensionality.propositional_extensionality.
    split; intros [].
    - destruct x. exists v. assumption.
    - exists (c_dv_SortSet x). assumption.
  Qed.

  Definition builtin_propset_fa_union_lemmas :=
  (
  propset_SortInt,
  propset_SortBool,
  propset_SortList,
  propset_SortSet,
  propset_SortMap
  ).

Definition builtin_props := (
  @SSet.concat_difference,
  rem_abs_0,
  land_rem_abs
).

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

Ltac classicize :=
  apply Classical_Prop.imply_to_or.

  Ltac app_ext_rewrite C :=
  lazymatch C with
  | context [propset_fa_union ?Cnew] =>
      try (rewrite builtin_propset_fa_union_lemmas; simpl);
      idtac "success";
      erewrite propset_fa_union_rewrite; [
      |
        intro;
        match goal with
        | |- ?G => app_ext_rewrite G
        end;
        unfold propset_fa_union;
        try rewrite propset_double;
        reflexivity
      ]

  | context [app_ext ?sym _] =>
    idtac "app_ext";
    repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
    autorewrite_set;
    apply propset_top_eq;
    repeat rewrite singleton_subseteq;
    repeat rewrite singleton_eq;
    simpl;
    reflexivity
  end.

  Ltac app_ext_rewrite_all :=
  repeat match goal with
  | |- context [propset_fa_union ?C] =>
      app_ext_rewrite (propset_fa_union C); unfold propset_fa_union at 1;
      rewrite propset_double
  end.

  Ltac basic_simplify_krule :=
    repeat eval_simplifier;
    simpl sort_inj;
    app_ext_rewrite_all;
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

  Ltac solver_macro AX :=
    simplify_krule;
    try reflexivity;
    try classicize;
    intros;
    destruct_and?; subst;
    repeat match goal with
    | [H : _ = evar_valuation ?ρ ?x, H1 : _ = evar_valuation ?ρ ?x |- _] => rewrite <- H in *; clear H
    | [H : evar_valuation ?ρ ?x = _, H1 : _ = evar_valuation ?ρ ?x |- _] => rewrite -> H in *; clear H
    end;
    repeat destruct_evar_val;
    destruct_and?; subst;
    repeat match goal with
    | [H : {[_]} ⊆ _ |- _] => apply singleton_subseteq_l in H as [? ?]
    end;
    simplify_eq;
    cbn;
    repeat f_equal;
    repeat rewrite implb_orb;
    repeat rewrite builtin_props;
    try reflexivity;
    try congruence;
    try btauto;
    try tauto;
    try lia;
    tryif done then idtac else (idtac "failed to prove: "; let X := eval cbn in AX in idtac X; admit).


      Goal satT Theory_behavioural Model.
      Proof.
        unfold satT, satM. intros.
        unfold Theory_behavioural in H.
        unfold_elem_of; destruct_or?; destruct_ex?; subst;
        match goal with
        | |- eval _ ?φ = ⊤ =>
          set AXIOM := φ
        end.
        * solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* simplify_krule.
  clear AXIOM. admit.
* simplify_krule.
  repeat destruct_evar_val;
  destruct_and?; subst;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
  simpl;
  repeat match goal with
  | [H : {[_]} ⊆ _ |- _] => apply singleton_subseteq_l in H as [? ?]
  end;
  simplify_eq;
  cbn;
  repeat f_equal;
  repeat rewrite implb_orb;
  repeat rewrite builtin_props;
  try reflexivity;
  try congruence;
  try btauto;
  try tauto;
  try lia;
  try timeout 1 set_solver.
  admit. (* TODO: could be done *)
* simplify_krule.
  clear AXIOM.
  repeat destruct_evar_val;
  destruct_and?; subst;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
  simpl;
  repeat match goal with
  | [H : {[_]} ⊆ _ |- _] => apply singleton_subseteq_l in H as [? ?]
  end;
  simplify_eq;
  cbn;
  repeat f_equal;
  repeat rewrite implb_orb;
  repeat rewrite builtin_props;
  try reflexivity;
  try congruence;
  try btauto;
  try tauto;
  try lia;
  try timeout 1 set_solver.
  admit.  (* TODO: could be done *)
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* basic_simplify_krule.





  repeat eval_simplifier.
  
  
  clear AXIOM.

(*   assert (
    forall A P,
      (propset_fa_union (fun x : SortInt_carrier => P x) : propset A) =
      (propset_fa_union (fun z : Z => P (c_dv_SortInt z)) : propset A)
  ) as XXX. {
    intros. unfold propset_fa_union.
    f_equal. extensionality c.
    apply PropExtensionality.propositional_extensionality.
    split; intros [].
    - destruct x0. exists v. assumption.
    - exists (c_dv_SortInt x0). assumption.
  }
  rewrite XXX. simpl. *)


  simpl sort_inj.
(*   Ltac unfold_dvs :=
    match goal with
    | [n : SortInt_carrier |- _] => destruct n
    end.
Search (not (∃ _, _)). *)
(*   try (rewrite XXX; simpl).
  erewrite propset_fa_union_rewrite.
  2: {
    intro.
    try (rewrite XXX; simpl).
    erewrite propset_fa_union_rewrite.
    2: {
    intro.
    try (rewrite XXX; simpl).
    erewrite propset_fa_union_rewrite.
    2: {
    intro.
    try (rewrite XXX; simpl).
    erewrite propset_fa_union_rewrite.
    2: {
    intro.
    try (rewrite XXX; simpl).
    erewrite propset_fa_union_rewrite.
    2: {
    intro.
    repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
    autorewrite_set;
    assert (propset_top_eq : forall {A : Type} (P Q : Prop),
              P <-> Q ->
              ({[ _ | P]} : propset A) = ({[_ | Q]} : propset A)
            ); [ intros; set_solver | ];
    apply propset_top_eq;
    repeat rewrite singleton_subseteq;
    repeat rewrite singleton_eq;
    simpl;
    reflexivity. }
  } *)
  repeat match goal with
  | |- context [propset_fa_union ?C] =>
    app_ext_rewrite (propset_fa_union C); unfold propset_fa_union at 1;
    rewrite propset_double
  end.

(*   unfold propset_fa_union;
  repeat rewrite propset_double.
  simpl.
 *)
  autorewrite_set.

  apply propset_top_elem_of_2;
  intro;
  apply elem_of_PropSet;
  repeat rewrite elem_of_PropSet;
  repeat rewrite singleton_subseteq;
  repeat rewrite singleton_eq.
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton); cbn.

  classicize.
  intro. destruct_and?.
  repeat rewrite singleton_subseteq in H1.
  
  destruct H2.
  - 
    
    
    repeat (setoid_rewrite XXX2 in H2; simpl in H2).
    repeat (setoid_rewrite XXX3 in H2; simpl in H2).
    repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton); cbn.
    repeat destruct_evar_val;
    repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton); cbn.
    all: try reflexivity.
    all: try congruence.
    all: simplify_eq; cbn.
    all: exfalso; set_solver.
    
    
    pose proof (Classical_Pred_Type.not_ex_all_not _ _ H0).
    simpl in H1.
  -
  
  
  repeat destruct_evar_val;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton); cbn.
  all: try reflexivity.
  all: try congruence.
  all: simplify_eq; cbn.
  

  apply Classical_Pred_Type.not_ex_all_not in H. destruct H.
  Ltac deMorgan :=
    rewrite Classical_Prop.not_and_or ||
    rewrite Classical_Prop.not_or_and.
  deMorgan.
  


  classicize. intro Contra.
  destruct_and?.
  
  repeat destruct_evar_val;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton); cbn;
  destruct_and?; subst; cbn in *;
  repeat match goal with
  | [H : {[_]} ⊆ {[_]} |- _] => apply singleton_subseteq in H
  | [H : {[_]} ⊆ _ |- _] => apply singleton_subseteq_l in H as [? ?]
  end; try congruence;
  simplify_eq;
  cbn.
  (* all: set_unfold.
  all: repeat case_match; try set_solver.
  repeat f_equal.
  - case_match; simpl; repeat f_equal.
    all: exfalso; apply H.
  - 
  
  
  
  
  repeat destruct_evar_val;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton); cbn.
  all: repeat f_equal.
  
  
  
  Search "/\" not.
  Ltac deMorgan :=
    rewrite Classical_Prop.not_and_or;
    rewrite Classical_Prop.not_or_and.
  deMorgan.
  Check elem_of_PropSet.
  




  erewrite propset_fa_union_rewrite.
  
  
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton).
  (* match goal with
  | |- context [oapp singleton ∅ ?C] =>
    idtac C;
    multimatch C with
    | context [evar_valuation ?ρ ?x] =>
      let H := fresh "Val" in
        idtac ρ x;
        destruct (evar_valuation ρ x) eqn:H;
        simpl
    end
  end. *)
  repeat destruct_evar_val;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton); cbn.
  Print propset_fa_union.






simplify_krule. *) all: admit.
* solver_macro AXIOM.
* (* repeat eval_simplifier. cbn.
 *)





solver_macro AXIOM. (* inj *)
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj *)
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj *)
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj *)
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj *)
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj *)
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj *)
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj + tree *)
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj *)
* solver_macro AXIOM.
* solver_macro AXIOM. (* inj + tree *)
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
Unshelve.
- admit.
- admit.
- 
      Defined.
      End TheorySemantics.

