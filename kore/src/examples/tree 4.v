
From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
From Kore Require Import BuiltIns DVParsers.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.
Import BuiltIns.List BuiltIns.SSet BuiltIns.MMap.


From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope string_scope.
Open Scope hlist_scope.

Require Import Btauto.

      Module TheorySyntax.


        Inductive Ksorts :=
        | SortK
        | SortKItem
        | SortTree
        | SortMap
        | SortInt
        | SortSet
        | SortList
        | SortIntList
        | SortBool
        .
        Instance Ksorts_eq_dec : EqDecision Ksorts.
        Proof. solve_decision. Defined.
  (*      Program Instance Ksorts_countable : finite.Finite Ksorts :=
        {
          enum := [SortK; SortKItem; SortTree; SortMap; SortInt; SortSet; SortList; SortIntList; SortBool]
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
  | Stop_Map (* .Map *)
  | Stop_Set (* .Set *)
  | Empty_Unds_TREE_Unds_Tree (* Empty_TREE_Tree *)
  | List_Coln_get (* List:get *)
  | List_Coln_range (* List:range *)
  | List_Coln_set (* List:set *)
  | ListItem (* ListItem *)
  | Map_Coln_choice (* Map:choice *)
  | Map_Coln_lookup (* Map:lookup *)
  | Map_Coln_lookupOrDefault (* Map:lookupOrDefault *)
  | Map_Coln_update (* Map:update *)
  | Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree (* Node(_,_,_,_)_TREE_Tree_Int_Int_Tree_Tree *)
  | Set_Coln_choice (* Set:choice *)
  | Set_Coln_difference (* Set:difference *)
  | Set_Coln_in (* Set:in *)
  | SetItem (* SetItem *)
  | UndsPerc_Int_Unds_ (* _%Int_ *)
  | UndsAnd__Int_Unds_ (* _&Int_ *)
  | UndsStar_Int_Unds_ (* _*Int_ *)
  | UndsPlus_Int_Unds_ (* _+Int_ *)
  | UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList (* _,__TREE_IntList_Int_IntList *)
  | Unds__Int_Unds_ (* _-Int_ *)
  | Unds__Map_UndsUnds_MAP_Unds_Map_Unds_Map_Unds_Map (* _-Map__MAP_Map_Map_Map *)
  | UndsSlsh_Int_Unds_ (* _/Int_ *)
  | Unds_LT__LT__Int_Unds_ (* _<<Int_ *)
  | Unds_LT_Eqls_Int_Unds_ (* _<=Int_ *)
  | Unds_LT_Eqls_Map_UndsUnds_MAP_Unds_Bool_Unds_Map_Unds_Map (* _<=Map__MAP_Bool_Map_Map *)
  | Unds_LT_Eqls_Set_UndsUnds_SET_Unds_Bool_Unds_Set_Unds_Set (* _<=Set__SET_Bool_Set_Set *)
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
  | Unds_Map_Unds_ (* _Map_ *)
  | Unds_Set_Unds_ (* _Set_ *)
  | UndsLSqBUnds_LT___undef_RSqB_ (* _[_<-undef] *)
  | UndsXor_Perc_Int_UndsUnds_ (* _^%Int__ *)
  | UndsXor__Int_Unds_ (* _^Int_ *)
  | Unds_andBool_Unds_ (* _andBool_ *)
  | Unds_andThenBool_Unds_ (* _andThenBool_ *)
  | Unds_divInt_Unds_ (* _divInt_ *)
  | Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int (* _dividesInt__INT-COMMON_Bool_Int_Int *)
  | Unds_impliesBool_Unds_ (* _impliesBool_ *)
  | Unds_inList_Unds_ (* _inList_ *)
  | Unds_in_Unds_keys_LParUndsRParUnds_MAP_Unds_Bool_Unds_KItem_Unds_Map (* _in_keys(_)_MAP_Bool_KItem_Map *)
  | Unds_modInt_Unds_ (* _modInt_ *)
  | Unds_orBool_Unds_ (* _orBool_ *)
  | Unds_orElseBool_Unds_ (* _orElseBool_ *)
  | Unds_xorBool_Unds_ (* _xorBool_ *)
  | Unds_xorInt_Unds_ (* _xorInt_ *)
  | UndsPipe____GT_Unds_ (* _|->_ *)
  | UndsPipe_Int_Unds_ (* _|Int_ *)
  | UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set (* _|Set__SET_Set_Set_Set *)
  | absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int (* absInt(_)_INT-COMMON_Int_Int *)
  | balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* balance(_)_TREE_Tree_Tree *)
  | balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* balanceFactor(_)_TREE_Int_Tree *)
  | bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int (* bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int *)
  | freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int (* freshInt(_)_INT_Int_Int *)
  | height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* height(_)_TREE_Int_Tree *)
  | inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree (* inorder(_)_TREE_List_Tree *)
  | insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int (* insert(_,_)_TREE_Tree_Tree_Int *)
  | intersectSet_LParUndsCommUndsRParUnds_SET_Unds_Set_Unds_Set_Unds_Set (* intersectSet(_,_)_SET_Set_Set_Set *)
  | isBool (* isBool *)
  | isInt (* isInt *)
  | isIntList (* isIntList *)
  | isK (* isK *)
  | isKItem (* isKItem *)
  | isList (* isList *)
  | isMap (* isMap *)
  | isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree (* isNode(_)_TREE_Bool_Tree *)
  | isSet (* isSet *)
  | isTree (* isTree *)
  | keys_LParUndsRParUnds_MAP_Unds_Set_Unds_Map (* keys(_)_MAP_Set_Map *)
  | keys_Unds_list_LParUndsRParUnds_MAP_Unds_List_Unds_Map (* keys_list(_)_MAP_List_Map *)
  | leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* leftT(_)_TREE_Tree_Tree *)
  | log2Int_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int (* log2Int(_)_INT-COMMON_Int_Int *)
  | makeList_LParUndsCommUndsRParUnds_LIST_Unds_List_Unds_Int_Unds_KItem (* makeList(_,_)_LIST_List_Int_KItem *)
  | maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int (* maxInt(_,_)_INT-COMMON_Int_Int_Int *)
  | minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int (* minInt(_,_)_INT-COMMON_Int_Int_Int *)
  | node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree (* node(_,_,_)_TREE_Tree_Int_Tree_Tree *)
  | notBool_Unds_ (* notBool_ *)
  | pushList (* pushList *)
  | removeAll_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Set (* removeAll(_,_)_MAP_Map_Map_Set *)
  | rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rightT(_)_TREE_Tree_Tree *)
  | rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateLeft(_)_TREE_Tree_Tree *)
  | rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateLeftRight(_)_TREE_Tree_Tree *)
  | rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateRight(_)_TREE_Tree_Tree *)
  | rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateRightLeft(_)_TREE_Tree_Tree *)
  | signExtendBitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int (* signExtendBitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int *)
  | size_LParUndsRParUnds_SET_Unds_Int_Unds_Set (* size(_)_SET_Int_Set *)
  | sizeList (* sizeList *)
  | sizeMap (* sizeMap *)
  | updateList_LParUndsCommUndsCommUndsRParUnds_LIST_Unds_List_Unds_List_Unds_Int_Unds_List (* updateList(_,_,_)_LIST_List_List_Int_List *)
  | updateMap_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Map (* updateMap(_,_)_MAP_Map_Map_Map *)
  | value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* value(_)_TREE_Int_Tree *)
  | values_LParUndsRParUnds_MAP_Unds_List_Unds_Map (* values(_)_MAP_List_Map *)
  | Tild_Int_Unds_ (* ~Int_ *)
  .
  (*
  Instance Ksyms_eq_dec : EqDecision Ksyms.
  Proof. solve_decision. Defined.
  Program Instance Ksyms_countable : finite.Finite Ksyms :=
  {
    enum := [kseq (* kseq *); dotk (* dotk *); append (* append *); Stop_List (* .List *); Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList (* .List{"_,__TREE_IntList_Int_IntList"}_IntList *); Stop_Map (* .Map *); Stop_Set (* .Set *); Empty_Unds_TREE_Unds_Tree (* Empty_TREE_Tree *); List_Coln_get (* List:get *); List_Coln_range (* List:range *); List_Coln_set (* List:set *); ListItem (* ListItem *); Map_Coln_choice (* Map:choice *); Map_Coln_lookup (* Map:lookup *); Map_Coln_lookupOrDefault (* Map:lookupOrDefault *); Map_Coln_update (* Map:update *); Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree (* Node(_,_,_,_)_TREE_Tree_Int_Int_Tree_Tree *); Set_Coln_choice (* Set:choice *); Set_Coln_difference (* Set:difference *); Set_Coln_in (* Set:in *); SetItem (* SetItem *); UndsPerc_Int_Unds_ (* _%Int_ *); UndsAnd__Int_Unds_ (* _&Int_ *); UndsStar_Int_Unds_ (* _*Int_ *); UndsPlus_Int_Unds_ (* _+Int_ *); UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList (* _,__TREE_IntList_Int_IntList *); Unds__Int_Unds_ (* _-Int_ *); Unds__Map_UndsUnds_MAP_Unds_Map_Unds_Map_Unds_Map (* _-Map__MAP_Map_Map_Map *); UndsSlsh_Int_Unds_ (* _/Int_ *); Unds_LT__LT__Int_Unds_ (* _<<Int_ *); Unds_LT_Eqls_Int_Unds_ (* _<=Int_ *); Unds_LT_Eqls_Map_UndsUnds_MAP_Unds_Bool_Unds_Map_Unds_Map (* _<=Map__MAP_Bool_Map_Map *); Unds_LT_Eqls_Set_UndsUnds_SET_Unds_Bool_Unds_Set_Unds_Set (* _<=Set__SET_Bool_Set_Set *); Unds_LT__Int_Unds_ (* _<Int_ *); UndsEqlsSlshEqls_Bool_Unds_ (* _=/=Bool_ *); UndsEqlsSlshEqls_Int_Unds_ (* _=/=Int_ *); UndsEqlsSlshEqls_K_Unds_ (* _=/=K_ *); UndsEqlsEqls_Bool_Unds_ (* _==Bool_ *); UndsEqlsEqls_Int_Unds_ (* _==Int_ *); UndsEqlsEqls_K_Unds_ (* _==K_ *); Unds_GT_Eqls_Int_Unds_ (* _>=Int_ *); Unds_GT__GT__Int_Unds_ (* _>>Int_ *); Unds_GT__Int_Unds_ (* _>Int_ *); Unds_List_Unds_ (* _List_ *); Unds_Map_Unds_ (* _Map_ *); Unds_Set_Unds_ (* _Set_ *); UndsLSqBUnds_LT___undef_RSqB_ (* _[_<-undef] *); UndsXor_Perc_Int_UndsUnds_ (* _^%Int__ *); UndsXor__Int_Unds_ (* _^Int_ *); Unds_andBool_Unds_ (* _andBool_ *); Unds_andThenBool_Unds_ (* _andThenBool_ *); Unds_divInt_Unds_ (* _divInt_ *); Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int (* _dividesInt__INT-COMMON_Bool_Int_Int *); Unds_impliesBool_Unds_ (* _impliesBool_ *); Unds_inList_Unds_ (* _inList_ *); Unds_in_Unds_keys_LParUndsRParUnds_MAP_Unds_Bool_Unds_KItem_Unds_Map (* _in_keys(_)_MAP_Bool_KItem_Map *); Unds_modInt_Unds_ (* _modInt_ *); Unds_orBool_Unds_ (* _orBool_ *); Unds_orElseBool_Unds_ (* _orElseBool_ *); Unds_xorBool_Unds_ (* _xorBool_ *); Unds_xorInt_Unds_ (* _xorInt_ *); UndsPipe____GT_Unds_ (* _|->_ *); UndsPipe_Int_Unds_ (* _|Int_ *); UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set (* _|Set__SET_Set_Set_Set *); absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int (* absInt(_)_INT-COMMON_Int_Int *); balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* balance(_)_TREE_Tree_Tree *); balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* balanceFactor(_)_TREE_Int_Tree *); bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int (* bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int *); freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int (* freshInt(_)_INT_Int_Int *); height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* height(_)_TREE_Int_Tree *); inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree (* inorder(_)_TREE_List_Tree *); insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int (* insert(_,_)_TREE_Tree_Tree_Int *); intersectSet_LParUndsCommUndsRParUnds_SET_Unds_Set_Unds_Set_Unds_Set (* intersectSet(_,_)_SET_Set_Set_Set *); isBool (* isBool *); isInt (* isInt *); isIntList (* isIntList *); isK (* isK *); isKItem (* isKItem *); isList (* isList *); isMap (* isMap *); isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree (* isNode(_)_TREE_Bool_Tree *); isSet (* isSet *); isTree (* isTree *); keys_LParUndsRParUnds_MAP_Unds_Set_Unds_Map (* keys(_)_MAP_Set_Map *); keys_Unds_list_LParUndsRParUnds_MAP_Unds_List_Unds_Map (* keys_list(_)_MAP_List_Map *); leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* leftT(_)_TREE_Tree_Tree *); log2Int_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int (* log2Int(_)_INT-COMMON_Int_Int *); makeList_LParUndsCommUndsRParUnds_LIST_Unds_List_Unds_Int_Unds_KItem (* makeList(_,_)_LIST_List_Int_KItem *); maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int (* maxInt(_,_)_INT-COMMON_Int_Int_Int *); minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int (* minInt(_,_)_INT-COMMON_Int_Int_Int *); node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree (* node(_,_,_)_TREE_Tree_Int_Tree_Tree *); notBool_Unds_ (* notBool_ *); pushList (* pushList *); removeAll_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Set (* removeAll(_,_)_MAP_Map_Map_Set *); rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rightT(_)_TREE_Tree_Tree *); rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateLeft(_)_TREE_Tree_Tree *); rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateLeftRight(_)_TREE_Tree_Tree *); rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateRight(_)_TREE_Tree_Tree *); rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree (* rotateRightLeft(_)_TREE_Tree_Tree *); signExtendBitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int (* signExtendBitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int *); size_LParUndsRParUnds_SET_Unds_Int_Unds_Set (* size(_)_SET_Int_Set *); sizeList (* sizeList *); sizeMap (* sizeMap *); updateList_LParUndsCommUndsCommUndsRParUnds_LIST_Unds_List_Unds_List_Unds_Int_Unds_List (* updateList(_,_,_)_LIST_List_List_Int_List *); updateMap_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Map (* updateMap(_,_)_MAP_Map_Map_Map *); value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree (* value(_)_TREE_Int_Tree *); values_LParUndsRParUnds_MAP_Unds_List_Unds_Map (* values(_)_MAP_List_Map *); Tild_Int_Unds_ (* ~Int_ *)]
  }.
  Next Obligation.
    compute_done.
  Defined.
  Final Obligation.
    intros. destruct x; set_solver.
  Defined.
  *)

        Inductive KSubsort : CRelationClasses.crelation Ksorts :=
|  inj_SortList_SortKItem : KSubsort SortList SortKItem
|  inj_SortMap_SortKItem : KSubsort SortMap SortKItem
|  inj_SortTree_SortKItem : KSubsort SortTree SortKItem
|  inj_SortSet_SortKItem : KSubsort SortSet SortKItem
|  inj_SortInt_SortKItem : KSubsort SortInt SortKItem
|  inj_SortIntList_SortKItem : KSubsort SortIntList SortKItem
|  inj_SortBool_SortKItem : KSubsort SortBool SortKItem
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
  | Stop_Map => []
  | Stop_Set => []
  | Empty_Unds_TREE_Unds_Tree => []
  | List_Coln_get => [SortList;SortInt]
  | List_Coln_range => [SortList;SortInt;SortInt]
  | List_Coln_set => [SortList;SortInt;SortKItem]
  | ListItem => [SortKItem]
  | Map_Coln_choice => [SortMap]
  | Map_Coln_lookup => [SortMap;SortKItem]
  | Map_Coln_lookupOrDefault => [SortMap;SortKItem;SortKItem]
  | Map_Coln_update => [SortMap;SortKItem;SortKItem]
  | Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree => [SortInt;SortInt;SortTree;SortTree]
  | Set_Coln_choice => [SortSet]
  | Set_Coln_difference => [SortSet;SortSet]
  | Set_Coln_in => [SortKItem;SortSet]
  | SetItem => [SortKItem]
  | UndsPerc_Int_Unds_ => [SortInt;SortInt]
  | UndsAnd__Int_Unds_ => [SortInt;SortInt]
  | UndsStar_Int_Unds_ => [SortInt;SortInt]
  | UndsPlus_Int_Unds_ => [SortInt;SortInt]
  | UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList => [SortInt;SortIntList]
  | Unds__Int_Unds_ => [SortInt;SortInt]
  | Unds__Map_UndsUnds_MAP_Unds_Map_Unds_Map_Unds_Map => [SortMap;SortMap]
  | UndsSlsh_Int_Unds_ => [SortInt;SortInt]
  | Unds_LT__LT__Int_Unds_ => [SortInt;SortInt]
  | Unds_LT_Eqls_Int_Unds_ => [SortInt;SortInt]
  | Unds_LT_Eqls_Map_UndsUnds_MAP_Unds_Bool_Unds_Map_Unds_Map => [SortMap;SortMap]
  | Unds_LT_Eqls_Set_UndsUnds_SET_Unds_Bool_Unds_Set_Unds_Set => [SortSet;SortSet]
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
  | Unds_Map_Unds_ => [SortMap;SortMap]
  | Unds_Set_Unds_ => [SortSet;SortSet]
  | UndsLSqBUnds_LT___undef_RSqB_ => [SortMap;SortKItem]
  | UndsXor_Perc_Int_UndsUnds_ => [SortInt;SortInt;SortInt]
  | UndsXor__Int_Unds_ => [SortInt;SortInt]
  | Unds_andBool_Unds_ => [SortBool;SortBool]
  | Unds_andThenBool_Unds_ => [SortBool;SortBool]
  | Unds_divInt_Unds_ => [SortInt;SortInt]
  | Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int => [SortInt;SortInt]
  | Unds_impliesBool_Unds_ => [SortBool;SortBool]
  | Unds_inList_Unds_ => [SortKItem;SortList]
  | Unds_in_Unds_keys_LParUndsRParUnds_MAP_Unds_Bool_Unds_KItem_Unds_Map => [SortKItem;SortMap]
  | Unds_modInt_Unds_ => [SortInt;SortInt]
  | Unds_orBool_Unds_ => [SortBool;SortBool]
  | Unds_orElseBool_Unds_ => [SortBool;SortBool]
  | Unds_xorBool_Unds_ => [SortBool;SortBool]
  | Unds_xorInt_Unds_ => [SortInt;SortInt]
  | UndsPipe____GT_Unds_ => [SortKItem;SortKItem]
  | UndsPipe_Int_Unds_ => [SortInt;SortInt]
  | UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set => [SortSet;SortSet]
  | absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int => [SortInt]
  | balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => [SortTree]
  | bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int => [SortInt;SortInt;SortInt]
  | freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int => [SortInt]
  | height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => [SortTree]
  | inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree => [SortTree]
  | insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int => [SortTree;SortInt]
  | intersectSet_LParUndsCommUndsRParUnds_SET_Unds_Set_Unds_Set_Unds_Set => [SortSet;SortSet]
  | isBool => [SortK]
  | isInt => [SortK]
  | isIntList => [SortK]
  | isK => [SortK]
  | isKItem => [SortK]
  | isList => [SortK]
  | isMap => [SortK]
  | isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree => [SortTree]
  | isSet => [SortK]
  | isTree => [SortK]
  | keys_LParUndsRParUnds_MAP_Unds_Set_Unds_Map => [SortMap]
  | keys_Unds_list_LParUndsRParUnds_MAP_Unds_List_Unds_Map => [SortMap]
  | leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | log2Int_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int => [SortInt]
  | makeList_LParUndsCommUndsRParUnds_LIST_Unds_List_Unds_Int_Unds_KItem => [SortInt;SortKItem]
  | maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int => [SortInt;SortInt]
  | minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int => [SortInt;SortInt]
  | node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree => [SortInt;SortTree;SortTree]
  | notBool_Unds_ => [SortBool]
  | pushList => [SortKItem;SortList]
  | removeAll_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Set => [SortMap;SortSet]
  | rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => [SortTree]
  | signExtendBitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int => [SortInt;SortInt;SortInt]
  | size_LParUndsRParUnds_SET_Unds_Int_Unds_Set => [SortSet]
  | sizeList => [SortList]
  | sizeMap => [SortMap]
  | updateList_LParUndsCommUndsCommUndsRParUnds_LIST_Unds_List_Unds_List_Unds_Int_Unds_List => [SortList;SortInt;SortList]
  | updateMap_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Map => [SortMap;SortMap]
  | value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => [SortTree]
  | values_LParUndsRParUnds_MAP_Unds_List_Unds_Map => [SortMap]
  | Tild_Int_Unds_ => [SortInt]
      end;
    ret_sort σ :=
      match σ with
                | kseq => SortK
  | dotk => SortK
  | append => SortK
  | Stop_List => SortList
  | Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList => SortIntList
  | Stop_Map => SortMap
  | Stop_Set => SortSet
  | Empty_Unds_TREE_Unds_Tree => SortTree
  | List_Coln_get => SortKItem
  | List_Coln_range => SortList
  | List_Coln_set => SortList
  | ListItem => SortList
  | Map_Coln_choice => SortKItem
  | Map_Coln_lookup => SortKItem
  | Map_Coln_lookupOrDefault => SortKItem
  | Map_Coln_update => SortMap
  | Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree => SortTree
  | Set_Coln_choice => SortKItem
  | Set_Coln_difference => SortSet
  | Set_Coln_in => SortBool
  | SetItem => SortSet
  | UndsPerc_Int_Unds_ => SortInt
  | UndsAnd__Int_Unds_ => SortInt
  | UndsStar_Int_Unds_ => SortInt
  | UndsPlus_Int_Unds_ => SortInt
  | UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList => SortIntList
  | Unds__Int_Unds_ => SortInt
  | Unds__Map_UndsUnds_MAP_Unds_Map_Unds_Map_Unds_Map => SortMap
  | UndsSlsh_Int_Unds_ => SortInt
  | Unds_LT__LT__Int_Unds_ => SortInt
  | Unds_LT_Eqls_Int_Unds_ => SortBool
  | Unds_LT_Eqls_Map_UndsUnds_MAP_Unds_Bool_Unds_Map_Unds_Map => SortBool
  | Unds_LT_Eqls_Set_UndsUnds_SET_Unds_Bool_Unds_Set_Unds_Set => SortBool
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
  | Unds_Map_Unds_ => SortMap
  | Unds_Set_Unds_ => SortSet
  | UndsLSqBUnds_LT___undef_RSqB_ => SortMap
  | UndsXor_Perc_Int_UndsUnds_ => SortInt
  | UndsXor__Int_Unds_ => SortInt
  | Unds_andBool_Unds_ => SortBool
  | Unds_andThenBool_Unds_ => SortBool
  | Unds_divInt_Unds_ => SortInt
  | Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int => SortBool
  | Unds_impliesBool_Unds_ => SortBool
  | Unds_inList_Unds_ => SortBool
  | Unds_in_Unds_keys_LParUndsRParUnds_MAP_Unds_Bool_Unds_KItem_Unds_Map => SortBool
  | Unds_modInt_Unds_ => SortInt
  | Unds_orBool_Unds_ => SortBool
  | Unds_orElseBool_Unds_ => SortBool
  | Unds_xorBool_Unds_ => SortBool
  | Unds_xorInt_Unds_ => SortInt
  | UndsPipe____GT_Unds_ => SortMap
  | UndsPipe_Int_Unds_ => SortInt
  | UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set => SortSet
  | absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int => SortInt
  | balance_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | balanceFactor_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => SortInt
  | bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int => SortInt
  | freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int => SortInt
  | height_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => SortInt
  | inorder_LParUndsRParUnds_TREE_Unds_List_Unds_Tree => SortList
  | insert_LParUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Tree_Unds_Int => SortTree
  | intersectSet_LParUndsCommUndsRParUnds_SET_Unds_Set_Unds_Set_Unds_Set => SortSet
  | isBool => SortBool
  | isInt => SortBool
  | isIntList => SortBool
  | isK => SortBool
  | isKItem => SortBool
  | isList => SortBool
  | isMap => SortBool
  | isNode_LParUndsRParUnds_TREE_Unds_Bool_Unds_Tree => SortBool
  | isSet => SortBool
  | isTree => SortBool
  | keys_LParUndsRParUnds_MAP_Unds_Set_Unds_Map => SortSet
  | keys_Unds_list_LParUndsRParUnds_MAP_Unds_List_Unds_Map => SortList
  | leftT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | log2Int_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int => SortInt
  | makeList_LParUndsCommUndsRParUnds_LIST_Unds_List_Unds_Int_Unds_KItem => SortList
  | maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int => SortInt
  | minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int => SortInt
  | node_LParUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Tree_Unds_Tree => SortTree
  | notBool_Unds_ => SortBool
  | pushList => SortList
  | removeAll_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Set => SortMap
  | rightT_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | rotateLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | rotateLeftRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | rotateRight_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | rotateRightLeft_LParUndsRParUnds_TREE_Unds_Tree_Unds_Tree => SortTree
  | signExtendBitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int => SortInt
  | size_LParUndsRParUnds_SET_Unds_Int_Unds_Set => SortInt
  | sizeList => SortInt
  | sizeMap => SortInt
  | updateList_LParUndsCommUndsCommUndsRParUnds_LIST_Unds_List_Unds_List_Unds_Int_Unds_List => SortList
  | updateMap_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Map => SortMap
  | value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree => SortInt
  | values_LParUndsRParUnds_MAP_Unds_List_Unds_Map => SortList
  | Tild_Int_Unds_ => SortInt
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

  (* Unds_andBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_andThenBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( ( kore_dv SortBool "false" ) and ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen1" ) ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andThenBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen1" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_andThenBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_andThenBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarK" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_divInt_Unds_ *)
  (exists R, pat = existT R (( ( ( UndsEqlsSlshEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI2"; kore_dv SortInt "0"⟩ ) =k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI1" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_divInt_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( UndsSlsh_Int_Unds_ ⋅ ⟨Unds__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; Unds_modInt_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI1"; @kore_fevar _ _ _ SortInt "VarI2"⟩⟩; @kore_fevar _ _ _ SortInt "VarI2"⟩ ) and ( Top{SortInt} ) ) ) )) \/

  (* Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI1" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI2" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_dividesInt_UndsUnds_INT_COMMON_Unds_Bool_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"⟩ ) =k{R} ( ( UndsEqlsEqls_Int_Unds_ ⋅ ⟨UndsPerc_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI2"; @kore_fevar _ _ _ SortInt "VarI1"⟩; kore_dv SortInt "0"⟩ ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_impliesBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "false" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_impliesBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_impliesBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_impliesBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_orBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "false" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_orBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarB" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_orBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_orBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_orElseBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "false" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarK" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_orElseBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortBool "VarK" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_orElseBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( kore_dv SortBool "true" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_orElseBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( kore_dv SortBool "true" ) and ( Top{SortBool} ) ) ) )) \/

  (* Unds_xorBool_Unds_ *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortBool "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( ( ( @kore_fevar _ _ _ SortBool "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortBool "VarB" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( Unds_xorBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "X0"; @kore_fevar _ _ _ SortBool "X1"⟩ ) =k{R} ( ( kore_dv SortBool "false" ) and ( Top{SortBool} ) ) ) )) \/

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

  (* signExtendBitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortInt "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarI" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X1" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarIDX" ) ) and ( ( ( @kore_fevar _ _ _ SortInt "X2" ) ⊆k{R} ( @kore_fevar _ _ _ SortInt "VarLEN" ) ) and ( Top{R} ) ) ) ) ) --->ₖ ( ( signExtendBitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "X0"; @kore_fevar _ _ _ SortInt "X1"; @kore_fevar _ _ _ SortInt "X2"⟩ ) =k{R} ( ( Unds__Int_Unds_ ⋅ ⟨Unds_modInt_Unds_ ⋅ ⟨UndsPlus_Int_Unds_ ⋅ ⟨bitRangeInt_LParUndsCommUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "VarI"; @kore_fevar _ _ _ SortInt "VarIDX"; @kore_fevar _ _ _ SortInt "VarLEN"⟩; Unds_LT__LT__Int_Unds_ ⋅ ⟨kore_dv SortInt "1"; Unds__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarLEN"; kore_dv SortInt "1"⟩⟩⟩; Unds_LT__LT__Int_Unds_ ⋅ ⟨kore_dv SortInt "1"; @kore_fevar _ _ _ SortInt "VarLEN"⟩⟩; Unds_LT__LT__Int_Unds_ ⋅ ⟨kore_dv SortInt "1"; Unds__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "VarLEN"; kore_dv SortInt "1"⟩⟩⟩ ) and ( Top{SortInt} ) ) ) )) \/

  (* value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree *)
  (exists R, pat = existT R (( ( (! ( kore_exists SortTree (kore_exists SortInt (kore_exists SortInt (kore_exists SortTree (( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨kore_bevar (In_cons (In_cons (In_nil))); kore_bevar (In_cons (In_nil)); kore_bevar (In_nil); kore_bevar (In_cons (In_cons (In_cons (In_nil))))⟩ ) ) and ( Top{R} ) ))))) ) or ( ⊥{R} )) ) and ( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortTree "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) ) --->ₖ ( ( value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( kore_dv SortInt "0" ) and ( Top{SortInt} ) ) ) )) \/

  (* value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree *)
  (exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortTree "X0" ) ⊆k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "VarV"; @kore_fevar _ _ _ SortInt "Var'Unds'Gen0"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen1"; @kore_fevar _ _ _ SortTree "Var'Unds'Gen2"⟩ ) ) and ( Top{R} ) ) ) --->ₖ ( ( value_LParUndsRParUnds_TREE_Unds_Int_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortTree "X0"⟩ ) =k{R} ( ( @kore_fevar _ _ _ SortInt "VarV" ) and ( Top{SortInt} ) ) ) ))
  ).

Definition Theory_functional : @Theory TheorySignature :=
  PropSet (fun pat =>

  (* Lbl'Stop'List is functional *)
  (exists R, pat = existT R (kore_exists SortList (( kore_bevar (In_nil) ) =k{R} ( Stop_List ⋅ ⟨⟩ )) )) \/

  (* Lbl'Stop'List'LBraQuotUndsCommUndsUnds'TREE'Unds'IntList'Unds'Int'Unds'IntList'QuotRBraUnds'IntList is functional *)
  (exists R, pat = existT R (kore_exists SortIntList (( kore_bevar (In_nil) ) =k{R} ( Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList ⋅ ⟨⟩ )) )) \/

  (* Lbl'Stop'Map is functional *)
  (exists R, pat = existT R (kore_exists SortMap (( kore_bevar (In_nil) ) =k{R} ( Stop_Map ⋅ ⟨⟩ )) )) \/

  (* Lbl'Stop'Set is functional *)
  (exists R, pat = existT R (kore_exists SortSet (( kore_bevar (In_nil) ) =k{R} ( Stop_Set ⋅ ⟨⟩ )) )) \/

  (* LblEmpty'Unds'TREE'Unds'Tree is functional *)
  (exists R, pat = existT R (kore_exists SortTree (( kore_bevar (In_nil) ) =k{R} ( Empty_Unds_TREE_Unds_Tree ⋅ ⟨⟩ )) )) \/

  (* LblListItem is functional *)
  (exists R, pat = existT R (kore_exists SortList (( kore_bevar (In_nil) ) =k{R} ( ListItem ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"⟩ )) )) \/

  (* LblMap'Coln'lookupOrDefault is functional *)
  (exists R, pat = existT R (kore_exists SortKItem (( kore_bevar (In_nil) ) =k{R} ( Map_Coln_lookupOrDefault ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"; @kore_fevar _ _ _ SortKItem "K1"; @kore_fevar _ _ _ SortKItem "K2"⟩ )) )) \/

  (* LblMap'Coln'update is functional *)
  (exists R, pat = existT R (kore_exists SortMap (( kore_bevar (In_nil) ) =k{R} ( Map_Coln_update ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"; @kore_fevar _ _ _ SortKItem "K1"; @kore_fevar _ _ _ SortKItem "K2"⟩ )) )) \/

  (* LblNode'LParUndsCommUndsCommUndsCommUndsRParUnds'TREE'Unds'Tree'Unds'Int'Unds'Int'Unds'Tree'Unds'Tree is functional *)
  (exists R, pat = existT R (kore_exists SortTree (( kore_bevar (In_nil) ) =k{R} ( Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"; @kore_fevar _ _ _ SortTree "K2"; @kore_fevar _ _ _ SortTree "K3"⟩ )) )) \/

  (* LblSet'Coln'difference is functional *)
  (exists R, pat = existT R (kore_exists SortSet (( kore_bevar (In_nil) ) =k{R} ( Set_Coln_difference ⋅ ⟨@kore_fevar _ _ _ SortSet "K0"; @kore_fevar _ _ _ SortSet "K1"⟩ )) )) \/

  (* LblSet'Coln'in is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Set_Coln_in ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"; @kore_fevar _ _ _ SortSet "K1"⟩ )) )) \/

  (* LblSetItem is functional *)
  (exists R, pat = existT R (kore_exists SortSet (( kore_bevar (In_nil) ) =k{R} ( SetItem ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"⟩ )) )) \/

  (* Lbl'UndsAnd-'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( UndsAnd__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'UndsStar'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( UndsStar_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'UndsPlus'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( UndsPlus_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'UndsCommUndsUnds'TREE'Unds'IntList'Unds'Int'Unds'IntList is functional *)
  (exists R, pat = existT R (kore_exists SortIntList (( kore_bevar (In_nil) ) =k{R} ( UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortIntList "K1"⟩ )) )) \/

  (* Lbl'Unds'-Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( Unds__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map is functional *)
  (exists R, pat = existT R (kore_exists SortMap (( kore_bevar (In_nil) ) =k{R} ( Unds__Map_UndsUnds_MAP_Unds_Map_Unds_Map_Unds_Map ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"; @kore_fevar _ _ _ SortMap "K1"⟩ )) )) \/

  (* Lbl'Unds-LT-Eqls'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_LT_Eqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_LT_Eqls_Map_UndsUnds_MAP_Unds_Bool_Unds_Map_Unds_Map ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"; @kore_fevar _ _ _ SortMap "K1"⟩ )) )) \/

  (* Lbl'Unds-LT-Eqls'Set'UndsUnds'SET'Unds'Bool'Unds'Set'Unds'Set is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_LT_Eqls_Set_UndsUnds_SET_Unds_Bool_Unds_Set_Unds_Set ⋅ ⟨@kore_fevar _ _ _ SortSet "K0"; @kore_fevar _ _ _ SortSet "K1"⟩ )) )) \/

  (* Lbl'Unds-LT-'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_LT__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'UndsEqlsSlshEqls'Bool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsSlshEqls_Bool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

  (* Lbl'UndsEqlsSlshEqls'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsSlshEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'UndsEqlsSlshEqls'K'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsSlshEqls_K_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortK "K0"; @kore_fevar _ _ _ SortK "K1"⟩ )) )) \/

  (* Lbl'UndsEqlsEqls'Bool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsEqls_Bool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

  (* Lbl'UndsEqlsEqls'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsEqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'UndsEqlsEqls'K'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( UndsEqlsEqls_K_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortK "K0"; @kore_fevar _ _ _ SortK "K1"⟩ )) )) \/

  (* Lbl'Unds-GT-Eqls'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_GT_Eqls_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'Unds-GT-'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_GT__Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'Unds'List'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortList (( kore_bevar (In_nil) ) =k{R} ( Unds_List_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortList "K0"; @kore_fevar _ _ _ SortList "K1"⟩ )) )) \/

  (* Lbl'UndsLSqBUnds-LT-'-undef'RSqB' is functional *)
  (exists R, pat = existT R (kore_exists SortMap (( kore_bevar (In_nil) ) =k{R} ( UndsLSqBUnds_LT___undef_RSqB_ ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"; @kore_fevar _ _ _ SortKItem "K1"⟩ )) )) \/

  (* Lbl'Unds'andBool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_andBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

  (* Lbl'Unds'andThenBool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_andThenBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

  (* Lbl'Unds'impliesBool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_impliesBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

  (* Lbl'Unds'inList'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_inList_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"; @kore_fevar _ _ _ SortList "K1"⟩ )) )) \/

  (* Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_in_Unds_keys_LParUndsRParUnds_MAP_Unds_Bool_Unds_KItem_Unds_Map ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"; @kore_fevar _ _ _ SortMap "K1"⟩ )) )) \/

  (* Lbl'Unds'orBool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_orBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

  (* Lbl'Unds'orElseBool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_orElseBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

  (* Lbl'Unds'xorBool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( Unds_xorBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"; @kore_fevar _ _ _ SortBool "K1"⟩ )) )) \/

  (* Lbl'Unds'xorInt'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( Unds_xorInt_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'UndsPipe'-'-GT-Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortMap (( kore_bevar (In_nil) ) =k{R} ( UndsPipe____GT_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"; @kore_fevar _ _ _ SortKItem "K1"⟩ )) )) \/

  (* Lbl'UndsPipe'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( UndsPipe_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* Lbl'UndsPipe'Set'UndsUnds'SET'Unds'Set'Unds'Set'Unds'Set is functional *)
  (exists R, pat = existT R (kore_exists SortSet (( kore_bevar (In_nil) ) =k{R} ( UndsPipe_Set_UndsUnds_SET_Unds_Set_Unds_Set_Unds_Set ⋅ ⟨@kore_fevar _ _ _ SortSet "K0"; @kore_fevar _ _ _ SortSet "K1"⟩ )) )) \/

  (* LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( absInt_LParUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"⟩ )) )) \/

  (* LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( freshInt_LParUndsRParUnds_INT_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"⟩ )) )) \/

  (* LblintersectSet'LParUndsCommUndsRParUnds'SET'Unds'Set'Unds'Set'Unds'Set is functional *)
  (exists R, pat = existT R (kore_exists SortSet (( kore_bevar (In_nil) ) =k{R} ( intersectSet_LParUndsCommUndsRParUnds_SET_Unds_Set_Unds_Set_Unds_Set ⋅ ⟨@kore_fevar _ _ _ SortSet "K0"; @kore_fevar _ _ _ SortSet "K1"⟩ )) )) \/

  (* LblisBool is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isBool ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* LblisInt is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isInt ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* LblisIntList is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isIntList ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* LblisK is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isK ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* LblisKItem is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isKItem ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* LblisList is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isList ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* LblisMap is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isMap ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* LblisSet is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isSet ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* LblisTree is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( isTree ⋅ ⟨@kore_fevar _ _ _ SortK "K0"⟩ )) )) \/

  (* Lblkeys'LParUndsRParUnds'MAP'Unds'Set'Unds'Map is functional *)
  (exists R, pat = existT R (kore_exists SortSet (( kore_bevar (In_nil) ) =k{R} ( keys_LParUndsRParUnds_MAP_Unds_Set_Unds_Map ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"⟩ )) )) \/

  (* LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( maxInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( minInt_LParUndsCommUndsRParUnds_INT_COMMON_Unds_Int_Unds_Int_Unds_Int ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"; @kore_fevar _ _ _ SortInt "K1"⟩ )) )) \/

  (* LblnotBool'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortBool (( kore_bevar (In_nil) ) =k{R} ( notBool_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortBool "K0"⟩ )) )) \/

  (* LblpushList is functional *)
  (exists R, pat = existT R (kore_exists SortList (( kore_bevar (In_nil) ) =k{R} ( pushList ⋅ ⟨@kore_fevar _ _ _ SortKItem "K0"; @kore_fevar _ _ _ SortList "K1"⟩ )) )) \/

  (* LblremoveAll'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Set is functional *)
  (exists R, pat = existT R (kore_exists SortMap (( kore_bevar (In_nil) ) =k{R} ( removeAll_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Set ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"; @kore_fevar _ _ _ SortSet "K1"⟩ )) )) \/

  (* Lblsize'LParUndsRParUnds'SET'Unds'Int'Unds'Set is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( size_LParUndsRParUnds_SET_Unds_Int_Unds_Set ⋅ ⟨@kore_fevar _ _ _ SortSet "K0"⟩ )) )) \/

  (* LblsizeList is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( sizeList ⋅ ⟨@kore_fevar _ _ _ SortList "K0"⟩ )) )) \/

  (* LblsizeMap is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( sizeMap ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"⟩ )) )) \/

  (* LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map is functional *)
  (exists R, pat = existT R (kore_exists SortMap (( kore_bevar (In_nil) ) =k{R} ( updateMap_LParUndsCommUndsRParUnds_MAP_Unds_Map_Unds_Map_Unds_Map ⋅ ⟨@kore_fevar _ _ _ SortMap "K0"; @kore_fevar _ _ _ SortMap "K1"⟩ )) )) \/

  (* Lbl'Tild'Int'Unds' is functional *)
  (exists R, pat = existT R (kore_exists SortInt (( kore_bevar (In_nil) ) =k{R} ( Tild_Int_Unds_ ⋅ ⟨@kore_fevar _ _ _ SortInt "K0"⟩ )) ))
  ).

      End TheorySyntax.
      Module TheorySemantics.
        Import TheorySyntax.

      Inductive SortK_carrier : Set :=
 | c_dotk
 | c_kseq(lcxgs:SortKItem_carrier) (ekbcw:SortK_carrier)
with SortKItem_carrier : Set :=
 | c_inj_SortBool_SortKItem (b : SortBool_carrier)
 | c_inj_SortInt_SortKItem (b : SortInt_carrier)
 | c_inj_SortIntList_SortKItem (b : SortIntList_carrier)
 | c_inj_SortList_SortKItem (b : SortList_carrier)
 | c_inj_SortMap_SortKItem (b : SortMap_carrier)
 | c_inj_SortSet_SortKItem (b : SortSet_carrier)
 | c_inj_SortTree_SortKItem (b : SortTree_carrier)
with SortTree_carrier : Set :=
 | c_Empty_Unds_TREE_Unds_Tree
 | c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree(fqagr:SortInt_carrier) (ixazv:SortInt_carrier) (ksplp:SortTree_carrier) (mktdv:SortTree_carrier)
with SortMap_carrier : Set :=
c_dv_SortMap(v:list (SortKItem_carrier * SortKItem_carrier))
with SortInt_carrier : Set :=
c_dv_SortInt(v:Z)
with SortSet_carrier : Set :=
c_dv_SortSet(v:list SortKItem_carrier)
with SortList_carrier : Set :=
c_dv_SortList(v:list SortKItem_carrier)
with SortIntList_carrier : Set :=
 | c__Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList
 | c__UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList(nfjau:SortInt_carrier) (zbcmm:SortIntList_carrier)
with SortBool_carrier : Set :=
c_dv_SortBool(v:bool)
.

      Definition carrier (s : Ksorts) : Set := match s with
      SortK => SortK_carrier
|SortKItem => SortKItem_carrier
|SortTree => SortTree_carrier
|SortMap => SortMap_carrier
|SortInt => SortInt_carrier
|SortSet => SortSet_carrier
|SortList => SortList_carrier
|SortIntList => SortIntList_carrier
|SortBool => SortBool_carrier
      end.

      Scheme Boolean Equality for SortK_carrier.
      Definition retr_SortKItem_SortList x := match x with 
  | c_inj_SortList_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortMap x := match x with 
  | c_inj_SortMap_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortTree x := match x with 
  | c_inj_SortTree_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortSet x := match x with 
  | c_inj_SortSet_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortInt x := match x with 
  | c_inj_SortInt_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortIntList x := match x with 
  | c_inj_SortIntList_SortKItem x => Some x
  | _ => None end.

Definition retr_SortKItem_SortBool x := match x with 
  | c_inj_SortBool_SortKItem x => Some x
  | _ => None end.

      Definition _19729cf (x0:SortTree_carrier) : option SortBool_carrier
   := match x0 with  _Gen0 => Some (c_dv_SortBool false)  end
.
Arguments _19729cf /.
Definition _7fa9c19 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  _Gen0 => Some c_Empty_Unds_TREE_Unds_Tree  end
.
Arguments _7fa9c19 /.
Definition _c385138 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  _Gen0 => Some c_Empty_Unds_TREE_Unds_Tree  end
.
Arguments _c385138 /.
Definition _c620995 (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Empty_Unds_TREE_Unds_Tree => Some (c_dv_SortInt 0)
  | _ => None  end
.
Arguments _c620995 /.
Definition _d5d5965 (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree V _Gen0 _Gen1 _Gen2 => Some V
  | _ => None  end
.
Arguments _d5d5965 /.
Definition _54f8b2b (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 H _Gen1 _Gen2 => Some H
  | _ => None  end
.
Arguments _54f8b2b /.
Definition _7e746e2 (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Empty_Unds_TREE_Unds_Tree => Some (c_dv_SortInt 0)
  | _ => None  end
.
Arguments _7e746e2 /.
Definition _aa256d5 (x0:SortTree_carrier) : option SortBool_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 _Gen1 _Gen2 _Gen3 => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _aa256d5 /.
Definition _42dba6c (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 _Gen1 L _Gen2 => Some L
  | _ => None  end
.
Arguments _42dba6c /.
Definition _e56be4f (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  _Gen0 => Some (c_dv_SortInt 0)  end
.
Arguments _e56be4f /.
Definition _62d53c4 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 _Gen1 _Gen2 R => Some R
  | _ => None  end
.
Arguments _62d53c4 /.
Definition _f205bc4 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortSet_SortKItem VarSet) c_dotk => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _f205bc4 /.
Definition _cf2cb8f (x0:SortInt_carrier) : option SortInt_carrier
   := match x0 with  i => Some i  end
.
Arguments _cf2cb8f /.
Definition _5352e22 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortTree_SortKItem Tree) c_dotk => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _5352e22 /.
Definition _16ff77c (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool true)  end
.
Arguments _16ff77c /.
Definition _92664aa (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortInt_SortKItem Int) c_dotk => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _92664aa /.
Definition _495da55 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false)  end
.
Arguments _495da55 /.
Definition _9a9489a (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false)  end
.
Arguments _9a9489a /.
Definition _83812b6 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false)  end
.
Arguments _83812b6 /.
Definition _c0705f1 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => Some T  end
.
Arguments _c0705f1 /.
Definition _cdf99a2 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false)  end
.
Arguments _cdf99a2 /.
Definition _2b5aadc (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false)  end
.
Arguments _2b5aadc /.
Definition _41e0b3a (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false)  end
.
Arguments _41e0b3a /.
Definition _6fb2c05 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortIntList_SortKItem IntList) c_dotk => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _6fb2c05 /.
Definition _4879c0f (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortMap_SortKItem Map) c_dotk => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _4879c0f /.
Definition _6f30a20 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false)  end
.
Arguments _6f30a20 /.
Definition _105572a (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  K => Some (c_dv_SortBool false)  end
.
Arguments _105572a /.
Definition _7d4dddf (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortList_SortKItem List) c_dotk => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _7d4dddf /.
Definition _dadad71 (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq (c_inj_SortBool_SortKItem Bool) c_dotk => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _dadad71 /.
Definition _ed3c25a (x0:SortK_carrier) : option SortBool_carrier
   := match x0 with  c_kseq KItem c_dotk => Some (c_dv_SortBool true)
  | _ => None  end
.
Arguments _ed3c25a /.
Definition _5615d55 (x0:SortInt_carrier) (x1:SortInt_carrier) : option SortInt_carrier
   := match x0,x1 with  i1, i2 => 
    _Val0 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.ltb x) y))) i1 i2 ;
    match _Val0 with (c_dv_SortBool b) => if b then (Some (i1 )) else None end end
.
Arguments _5615d55 /.
Definition height____TREE_Int_Tree (x0 : SortTree_carrier) : option SortInt_carrier := (_54f8b2b x0) <|> (_7e746e2 x0) 
.

Definition isNode____TREE_Bool_Tree (x0 : SortTree_carrier) : option SortBool_carrier := (_aa256d5 x0) <|> (_19729cf x0) 
.

Definition leftT____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := (_42dba6c x0) <|> (_c385138 x0) 
.

Definition value____TREE_Int_Tree (x0 : SortTree_carrier) : option SortInt_carrier := (_d5d5965 x0) <|> (_e56be4f x0) 
.

Definition rightT____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := (_62d53c4 x0) <|> (_7fa9c19 x0) 
.

Definition freshInt____INT_Int_Int (x0 : SortInt_carrier) : option SortInt_carrier := _cf2cb8f x0 
.

Definition isK (x0 : SortK_carrier) : option SortBool_carrier := _16ff77c x0 
.
Arguments isK /.
Definition _e1effea (x0:SortInt_carrier) (x1:SortInt_carrier) : option SortInt_carrier
   := match x0,x1 with  i1, i2 => 
    _Val0 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.geb x) y))) i1 i2 ;
    match _Val0 with (c_dv_SortBool b) => if b then (Some (i2 )) else None end end
.
Arguments _e1effea /.
Definition _f6efc09 (x0:SortTree_carrier) : option SortList_carrier
   := match x0 with  c_Empty_Unds_TREE_Unds_Tree => 
    _Val0 ← (Some (c_dv_SortList [])) ;
    mret _Val0
  | _ => None  end
.
Arguments _f6efc09 /.
Definition isTree (x0 : SortK_carrier) : option SortBool_carrier := (_5352e22 x0) <|> (_cdf99a2 x0) 
.
Arguments isTree /.

Definition _147fc15 (x0:SortInt_carrier) (x1:SortInt_carrier) (x2:SortInt_carrier) : option SortInt_carrier
   := match x0,x1,x2 with  i, IDX, LEN => 
    _Val0 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftr x) y))) i IDX ;
    _Val1 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y))) (c_dv_SortInt 1) LEN ;
    _Val2 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ emod x) y))) _Val0 _Val1 ;
    mret _Val2  end
.

Definition isSet (x0 : SortK_carrier) : option SortBool_carrier := (_f205bc4 x0) <|> (_2b5aadc x0) 
.
Arguments isSet /.

Definition _fd8faca (x0:SortInt_carrier) (x1:SortInt_carrier) : option SortBool_carrier
   := match x0,x1 with  i1, i2 => 
    _Val0 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.rem x) y))) i2 i1 ;
    _Val1 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.eqb x) y))) _Val0 (c_dv_SortInt 0) ;
    mret _Val1  end
.

Definition isIntList (x0 : SortK_carrier) : option SortBool_carrier := (_6fb2c05 x0) <|> (_41e0b3a x0) 
.
Arguments isIntList /.
Definition isMap (x0 : SortK_carrier) : option SortBool_carrier := (_4879c0f x0) <|> (_6f30a20 x0) 
.
Arguments isMap /.
Definition isInt (x0 : SortK_carrier) : option SortBool_carrier := (_92664aa x0) <|> (_105572a x0) 
.
Arguments isInt /.
Definition isList (x0 : SortK_carrier) : option SortBool_carrier := (_7d4dddf x0) <|> (_9a9489a x0) 
.
Arguments isList /.
Definition isBool (x0 : SortK_carrier) : option SortBool_carrier := (_dadad71 x0) <|> (_495da55 x0) 
.
Arguments isBool /.
Definition isKItem (x0 : SortK_carrier) : option SortBool_carrier := (_ed3c25a x0) <|> (_83812b6 x0) 
.
Arguments isKItem /.

Definition _780a187 (x0:SortInt_carrier) (x1:SortTree_carrier) (x2:SortTree_carrier) : option SortTree_carrier
   := match x0,x1,x2 with  V, L, R => 
    _Val0 ← height____TREE_Int_Tree L ;
    _Val1 ← height____TREE_Int_Tree R ;
    _Val2 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.max x) y))) _Val0 _Val1 ;
    _Val3 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.add x) y))) (c_dv_SortInt 1) _Val2 ;
    mret (c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree V _Val3 L R)  end
.
Arguments _780a187 /.

Definition _533014b (x0:SortTree_carrier) : option SortInt_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree _Gen0 _Gen1 L R => 
    _Val0 ← height____TREE_Int_Tree L ;
    _Val1 ← height____TREE_Int_Tree R ;
    _Val2 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y))) _Val0 _Val1 ;
    mret _Val2
  | _ => None  end
.
Arguments _533014b /.

Definition minInt______INT_COMMON_Int_Int_Int (x0 : SortInt_carrier) (x1 : SortInt_carrier) : option SortInt_carrier := (_5615d55 x0 x1) <|> (_e1effea x0 x1) 
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
  | _ => None  end in
 (_f6efc09 x0) <|> (_fdf0244 x0) 
.
Definition bitRangeInt________INT_COMMON_Int_Int_Int_Int (x0 : SortInt_carrier) (x1 : SortInt_carrier) (x2 : SortInt_carrier) : option SortInt_carrier := _147fc15 x0 x1 x2 
.

Definition _dividesInt__INT_COMMON_Bool_Int_Int (x0 : SortInt_carrier) (x1 : SortInt_carrier) : option SortBool_carrier := _fd8faca x0 x1 
.

Definition node________TREE_Tree_Int_Tree_Tree (x0 : SortInt_carrier) (x1 : SortTree_carrier) (x2 : SortTree_carrier) : option SortTree_carrier := _780a187 x0 x1 x2 
.

Definition balanceFactor____TREE_Int_Tree (x0 : SortTree_carrier) : option SortInt_carrier := (_533014b x0) <|> (_c620995 x0) 
.

Definition _3b67f4b (x0:SortInt_carrier) (x1:SortInt_carrier) (x2:SortInt_carrier) : option SortInt_carrier
   := match x0,x1,x2 with  i, IDX, LEN => 
    _Val0 ← (fun x y z => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ bitRange x) y) z))) i IDX LEN ;
    _Val1 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y))) LEN (c_dv_SortInt 1) ;
    _Val2 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y))) (c_dv_SortInt 1) _Val1 ;
    _Val3 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.add x) y))) _Val0 _Val2 ;
    _Val4 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y))) (c_dv_SortInt 1) LEN ;
    _Val5 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ emod x) y))) _Val3 _Val4 ;
    _Val6 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y))) LEN (c_dv_SortInt 1) ;
    _Val7 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y))) (c_dv_SortInt 1) _Val6 ;
    _Val8 ← (fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y))) _Val5 _Val7 ;
    mret _Val8  end
.

Arguments _3b67f4b /.

Definition _1a74dc5 (x0:SortTree_carrier) (x1:SortInt_carrier) : option SortTree_carrier
   := match x0,x1 with  c_Empty_Unds_TREE_Unds_Tree, V => 
    _Val0 ← node________TREE_Tree_Int_Tree_Tree V c_Empty_Unds_TREE_Unds_Tree c_Empty_Unds_TREE_Unds_Tree ;
    mret _Val0
  | _, _ => None  end
.
Arguments _1a74dc5 /.

Definition _f76f624 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree X _Gen0 A (c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree Y _Gen1 B C) => 
    _Val0 ← node________TREE_Tree_Int_Tree_Tree X A B ;
    _Val1 ← node________TREE_Tree_Int_Tree_Tree Y _Val0 C ;
    mret _Val1
  | _ => None  end
.
Arguments _f76f624 /.

Definition _bd2ae08 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree Y _Gen0 (c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree X _Gen1 A B) C => 
    _Val0 ← node________TREE_Tree_Int_Tree_Tree Y B C ;
    _Val1 ← node________TREE_Tree_Int_Tree_Tree X A _Val0 ;
    mret _Val1
  | _ => None  end
.
Arguments _bd2ae08 /.

Definition signExtendBitRangeInt________INT_COMMON_Int_Int_Int_Int (x0 : SortInt_carrier) (x1 : SortInt_carrier) (x2 : SortInt_carrier) : option SortInt_carrier := _3b67f4b x0 x1 x2 
.

Definition rotateLeft____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := _f76f624 x0 
.

Definition rotateRight____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := _bd2ae08 x0 
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
    match _Val5 with (c_dv_SortBool b) => if b then (Some (_Val6 )) else None end end
.
Arguments _a4ef7ef/.

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
    match _Val1 with (c_dv_SortBool b) => if b then (Some (_Val7 )) else None end end
.
Arguments _15d45ab /.

Definition _143cf23 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => 
    _Val0 ← balanceFactor____TREE_Int_Tree T ;
    _Val1 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.gtb x) y))) _Val0 (c_dv_SortInt 1) ;
    _Val2 ← leftT____TREE_Tree_Tree T ;
    _Val3 ← balanceFactor____TREE_Int_Tree _Val2 ;
    _Val4 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.geb x) y))) _Val3 (c_dv_SortInt 0) ;
    _Val5 ← (fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y))) _Val1 _Val4 ;
    _Val6 ← rotateRight____TREE_Tree_Tree T ;
    match _Val5 with (c_dv_SortBool b) => if b then (Some (_Val6 )) else None end end
.
Arguments _143cf23 /.

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
    match _Val1 with (c_dv_SortBool b) => if b then (Some (_Val7 )) else None end end
.
Arguments _b647727 /.

Definition rotateRightLeft____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := _15d45ab x0 
.

Definition rotateLeftRight____TREE_Tree_Tree (x0 : SortTree_carrier) : option SortTree_carrier := _b647727 x0 
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
    match _Val5 with (c_dv_SortBool b) => if b then (Some (_Val6 )) else None end end
.
Arguments _db49e2d /.

Definition _d5a13c7 (x0:SortTree_carrier) : option SortTree_carrier
   := match x0 with  T => 
    _Val0 ← balanceFactor____TREE_Int_Tree T ;
    _Val1 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.gtb x) y))) _Val0 (c_dv_SortInt 1) ;
    _Val2 ← leftT____TREE_Tree_Tree T ;
    _Val3 ← balanceFactor____TREE_Int_Tree _Val2 ;
    _Val4 ← (fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.ltb x) y))) _Val3 (c_dv_SortInt 0) ;
    _Val5 ← (fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y))) _Val1 _Val4 ;
    _Val6 ← rotateLeftRight____TREE_Tree_Tree T ;
    match _Val5 with (c_dv_SortBool b) => if b then (Some (_Val6 )) else None end end
.
Arguments _d5a13c7 /.

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
  end |  _, _  => None end in
let _edaaa1f (x0:SortTree_carrier) (x1:SortInt_carrier) : option SortTree_carrier
   := match x0,x1 with  c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree X _Gen0 L R, V => 
    _Val0 ← insert______TREE_Tree_Tree_Int R V ;
    _Val1 ← node________TREE_Tree_Int_Tree_Tree X L _Val0 ;
    _Val2 ← balance____TREE_Tree_Tree _Val1 ;
    mret _Val2
  | _, _ => None  end in
 (_1a74dc5 x0 x1) <|> (_2fb2b0c x0 x1) <|> (_edaaa1f x0 x1) 
. 

      Definition parser (s : Ksorts) : string -> option (carrier s) :=
            match s with
             | SortInt => map_parser c_dv_SortInt Z_parser
             | SortBool => map_parser c_dv_SortBool bool_parser
             | _ => None_parser
            end.

      Definition P (σ : symbol) := foldr (λ c a, carrier c -> a) (option (carrier (ret_sort σ))) (arg_sorts σ).

      Program Definition Model : @Model TheorySignature :=
        mkModel_partial
          carrier (* (Ksorts_rect _ SortK_carrier SortKItem_carrier SortTree_carrier SortMap_carrier SortInt_carrier SortSet_carrier SortList_carrier SortIntList_carrier SortBool_carrier) *)
          (Ksyms_rect P (fun x0 x1 => Some (c_kseq x0 x1))
(Some c_dotk)
(fun xs ys => Some ((fix append xs ys := match xs with c_dotk => ys | c_kseq x xs => c_kseq x (append xs ys) end) xs ys))(*append*)
(Some (c_dv_SortList []))(*.List*)
(Some c__Stop_List_LBraQuotUndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList_QuotRBraUnds_IntList)
(Some (c_dv_SortMap []))(*.Map*)
(Some (c_dv_SortSet []))(*.Set*)
(Some c_Empty_Unds_TREE_Unds_Tree)
(fun xs x => SortInt_carrier_rect (fun _ => option SortKItem_carrier) (SortList_carrier_rect (fun _ => Z -> option SortKItem_carrier) List_get xs) x)(*List:get*)
(fun xs x y => Some (c_dv_SortList (SortInt_carrier_rect (fun _ => list SortKItem_carrier) (SortInt_carrier_rect (fun _ => Z -> list SortKItem_carrier) (SortList_carrier_rect _ List_range xs) x) y)))(*List:range*)
(fun xs x y => c_dv_SortList <$> SortInt_carrier_rect (fun _ => SortKItem_carrier -> option (list SortKItem_carrier)) (SortList_carrier_rect (fun _ => Z -> SortKItem_carrier -> _) List_set xs) x y)(*List:set*)
(fun x => Some (c_dv_SortList [x]))(*ListItem*)
(fun m => SortMap_carrier_rect _ MMap.choice m)(*Map:choice*)
(fun m x => (SortMap_carrier_rect (fun _ => SortKItem_carrier -> option SortKItem_carrier) (MMap.lookup SortKItem_carrier_beq) m) x)(*Map:lookup*)
(fun m x d => Some ((SortMap_carrier_rect (fun _ => SortKItem_carrier -> SortKItem_carrier -> SortKItem_carrier) (MMap.lookupOrDefault SortKItem_carrier_beq) m) x d))(*Map:lookupOrDefault*)
(fun m k v => Some (c_dv_SortMap ((SortMap_carrier_rect (fun _ => SortKItem_carrier -> SortKItem_carrier -> _) (MMap.update SortKItem_carrier_beq) m) k v)))(*Map:update*)
(fun x0 x1 x2 x3 => Some (c_Node_LParUndsCommUndsCommUndsCommUndsRParUnds_TREE_Unds_Tree_Unds_Int_Unds_Int_Unds_Tree_Unds_Tree x0 x1 x2 x3))
(fun s => SortSet_carrier_rect _ SSet.choice s)(*Set:choice*)
(fun xs ys => Some (c_dv_SortSet (SortSet_carrier_rect (fun _ => list SortKItem_carrier) (SortSet_carrier_rect _ (SSet.difference SortKItem_carrier_beq) xs) ys)))(*Set:difference*)
(fun x xs => Some (c_dv_SortBool (SortSet_carrier_rect (fun _ => bool) (fun s => SSet.in_ SortKItem_carrier_beq x s) xs)))(*Set:in*)
(fun x => Some (c_dv_SortSet (setitem x)))(*SetItem*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.rem x) y)))(*_%Int_*)
(fun z1 z2 => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.rem z1) z2)))(*_&Int_*)
(fun z1 z2 => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.mul z1) z2)))(*_*Int_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.add x) y)))(*_+Int_*)
(fun x0 x1 => Some (c__UndsCommUndsUnds_TREE_Unds_IntList_Unds_Int_Unds_IntList x0 x1))
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.sub x) y)))(*_-Int_*)
(fun m1 m2 => Some (c_dv_SortMap (SortMap_carrier_rect _ (SortMap_carrier_rect (fun _ => Map SortKItem_carrier SortKItem_carrier -> Map SortKItem_carrier SortKItem_carrier) (MMap.difference SortKItem_carrier_beq SortKItem_carrier_beq) m1) m2)))(*_-Map__MAP_Map_Map_Map*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.quot x) y)))(*_/Int_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.shiftl x) y)))(*_<<Int_*)
(fun x y => Some (c_dv_SortBool (SortInt_carrier_rect (fun _ => bool) (SortInt_carrier_rect _ Z.leb x) y)))(*_<=Int_*)
(fun m1 m2 => Some (c_dv_SortBool (SortMap_carrier_rect _ (SortMap_carrier_rect (fun _ => Map SortKItem_carrier SortKItem_carrier -> bool) (MMap.inclusion SortKItem_carrier_beq SortKItem_carrier_beq) m1) m2)))(*_<=Map__MAP_Bool_Map_Map*)
(fun s1 s2 => Some (c_dv_SortBool (SortSet_carrier_rect _ (SortSet_carrier_rect (fun _ => SSet SortKItem_carrier -> bool) (SSet.inclusion SortKItem_carrier_beq) s1) s2)))(*_<=Set__SET_Bool_Set_Set*)
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
(fun m1 m2 => c_dv_SortMap <$> (SortMap_carrier_rect (fun _ => option (MMap.Map SortKItem_carrier SortKItem_carrier)) (SortMap_carrier_rect _ (MMap.concat SortKItem_carrier_beq SortKItem_carrier_beq) m1) m2))(*_Map_*)
(fun xs ys => c_dv_SortSet <$> (SortSet_carrier_rect (fun _ => option (list SortKItem_carrier)) (SortSet_carrier_rect _ (SSet.concat SortKItem_carrier_beq) xs) ys))(*_Set_*)
(fun m x => Some (c_dv_SortMap ((SortMap_carrier_rect (fun _ => SortKItem_carrier -> MMap.Map SortKItem_carrier SortKItem_carrier) (MMap.remove SortKItem_carrier_beq) m) x)))(*_[_<-undef]*)
(fun z1 z2 z3 => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ modPow z1) z2) z3)))(*_^%Int__*)
(fun z1 z2 => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.pow z1) z2)))(*_^Int_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y)))(*_andBool_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ andb x) y)))(*_andThenBool_*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ ediv x) y)))(*_divInt_*)
_dividesInt__INT_COMMON_Bool_Int_Int
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ implb x) y)))(*_impliesBool_*)
(fun x xs => Some (c_dv_SortBool (SortList_carrier_rect (fun _ => bool) (List.List_in SortKItem_carrier_beq x) xs)))(*_inList_*)
(fun x m => Some (c_dv_SortBool (SortMap_carrier_rect _ (MMap.in_keys SortKItem_carrier_beq x) m)))(*_in_keys(_)_MAP_Bool_KItem_Map*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ emod x) y)))(*_modInt_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ orb x) y)))(*_orBool_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ orb x) y)))(*_orElseBool_*)
(fun (x y: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect (fun _ => bool) (SortBool_carrier_rect _ xorb x) y)))(*_xorBool_*)
(fun z1 z2 => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.lxor z1) z2)))(*_xorInt_*)
(fun k v => Some (c_dv_SortMap (element k v)))(*_|->_*)
(fun z1 z2 => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.lor z1) z2)))(*_|Int_*)
(fun xs ys => Some (c_dv_SortSet (SortSet_carrier_rect (fun _ => list SortKItem_carrier) (SortSet_carrier_rect _ (SSet.union SortKItem_carrier_beq) xs) ys)))(*_|Set__SET_Set_Set_Set*)
(fun x => Some (c_dv_SortInt (SortInt_carrier_rect _ Z.abs x)))(*absInt(_)_INT-COMMON_Int_Int*)
balance____TREE_Tree_Tree
balanceFactor____TREE_Int_Tree
(fun x y z => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ bitRange x) y) z)))(*bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int*)
freshInt____INT_Int_Int
height____TREE_Int_Tree
inorder____TREE_List_Tree
insert______TREE_Tree_Tree_Int
(fun xs ys => Some (c_dv_SortSet (SortSet_carrier_rect (fun _ => list SortKItem_carrier) (SortSet_carrier_rect _ (SSet.intersection SortKItem_carrier_beq) xs) ys)))(*intersectSet(_,_)_SET_Set_Set_Set*)
isBool
isInt
isIntList
isK
isKItem
isList
isMap
isNode____TREE_Bool_Tree
isSet
isTree
(fun m => Some (c_dv_SortSet (SortMap_carrier_rect (fun _ => list SortKItem_carrier) MapSet.keys m)))(*keys(_)_MAP_Set_Map*)
(fun m => Some (c_dv_SortList (SortMap_carrier_rect (fun _ => list SortKItem_carrier) MapSet.keys_list m)))(*keys_list(_)_MAP_List_Map*)
leftT____TREE_Tree_Tree
(fun z => Some (c_dv_SortInt (SortInt_carrier_rect _ Z.log2 z)))(*log2Int(_)_INT-COMMON_Int_Int*)
(fun z v => Some (c_dv_SortList ((SortInt_carrier_rect (fun _ => SortKItem_carrier -> list SortKItem_carrier) (List_make) z) v)))(*makeList(_,_)_LIST_List_Int_KItem*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.max x) y)))(*maxInt(_,_)_INT-COMMON_Int_Int_Int*)
(fun x y => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect _ Z.min x) y)))(*minInt(_,_)_INT-COMMON_Int_Int_Int*)
node________TREE_Tree_Int_Tree_Tree
(fun (x: SortBool_carrier) => Some (c_dv_SortBool (SortBool_carrier_rect _ negb x)))(*notBool_*)
(fun x xs => Some (c_dv_SortList (SortList_carrier_rect _ (fun xs => x :: xs) xs)))(*pushList*)
(fun m x => Some (c_dv_SortMap ((SortSet_carrier_rect _ (SortMap_carrier_rect (fun _ => SSet SortKItem_carrier -> MMap.Map SortKItem_carrier SortKItem_carrier) (MapSet.removeAll SortKItem_carrier_beq) m) x))))(*removeAll(_,_)_MAP_Map_Map_Set*)
rightT____TREE_Tree_Tree
rotateLeft____TREE_Tree_Tree
rotateLeftRight____TREE_Tree_Tree
rotateRight____TREE_Tree_Tree
rotateRightLeft____TREE_Tree_Tree
(fun z1 z2 z3 => Some (c_dv_SortInt (SortInt_carrier_rect (fun _ => Z) (SortInt_carrier_rect (fun _ => Z -> Z) (SortInt_carrier_rect _ signExtendBitRange z1) z2) z3)))(*signExtendBitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int*)
(fun x => Some (c_dv_SortInt (SortSet_carrier_rect _ (SSet.size) x)))(*size(_)_SET_Int_Set*)
(fun x => Some (c_dv_SortInt (Z.of_nat (SortList_carrier_rect _ length x))))(*sizeList*)
(fun x => Some (c_dv_SortInt (SortMap_carrier_rect _ (MMap.size) x)))(*sizeMap*)
(fun xs z ys => c_dv_SortList <$> (SortList_carrier_rect (fun _ => option (list SortKItem_carrier)) (SortInt_carrier_rect (fun _ => list SortKItem_carrier -> option (list SortKItem_carrier)) (SortList_carrier_rect (fun _ => Z -> list SortKItem_carrier -> option (list SortKItem_carrier)) List_update xs) z) ys))(*updateList(_,_,_)_LIST_List_List_Int_List*)
(fun m1 m2 => Some (c_dv_SortMap ((SortMap_carrier_rect _ (SortMap_carrier_rect (fun _ => MMap.Map SortKItem_carrier SortKItem_carrier -> MMap.Map SortKItem_carrier SortKItem_carrier) (MMap.updateAll SortKItem_carrier_beq) m1) m2))))(*updateMap(_,_)_MAP_Map_Map_Map*)
value____TREE_Int_Tree
(fun m => Some (c_dv_SortList (SortMap_carrier_rect (fun _ => list SortKItem_carrier) MMap.values m)))(*values(_)_MAP_List_Map*)
(fun z => Some (c_dv_SortInt (SortInt_carrier_rect _ Z.lnot z)))(*~Int_*))
          _ _ (parser).
      Next Obligation.
        destruct s; repeat constructor.
      Defined.
      Final Obligation.
        intros s1 s2 H x; inversion H; subst.
      * exact (c_inj_SortList_SortKItem x).
* exact (c_inj_SortMap_SortKItem x).
* exact (c_inj_SortTree_SortKItem x).
* exact (c_inj_SortSet_SortKItem x).
* exact (c_inj_SortInt_SortKItem x).
* exact (c_inj_SortIntList_SortKItem x).
* exact (c_inj_SortBool_SortKItem x).
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
  land_rem_abs,
  shift_rem
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

  Ltac unfold_dvs :=
    repeat match goal with
    | [n : SortInt_carrier |- _] => destruct n
    | [n : SortBool_carrier |- _] => destruct n
    | [n : SortList_carrier |- _] => destruct n
    | [n : SortMap_carrier |- _] => destruct n
    | [n : SortSet_carrier |- _] => destruct n
    end.
  Ltac solve_injection :=
    match goal with
    | [H : ¬ ∃ _, c_kseq _ _ = c_kseq _ c_dotk |- _] =>
      repeat case_match; simpl; try reflexivity;
        unfold_dvs;
        exfalso;
        apply H;
        eexists;
        reflexivity
    end.
  Ltac find_contra :=
  match goal with
  | [H : ¬ ∃ _, _ |- _] =>
    unfold_dvs;
    exfalso;
    apply H;
    repeat eexists;
    reflexivity
  end.
  Ltac rewrite_evar_val :=
  repeat match goal with
    | [H : _ = evar_valuation ?ρ ?x |- _] => rewrite <- H in *; clear H
    | [H : evar_valuation ?ρ ?x = _ |- _] => rewrite -> H in *; clear H
    end.
  Ltac simplification_solver :=
    try reflexivity;
    try classicize;
    intros;
    destruct_and?; subst;
    rewrite_evar_val;
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
    try solve_injection;
    try find_contra.
    Ltac app_ext_empty :=
    rewrite app_ext_singleton_empty;
    [app_ext_empty || idtac (* for some reason, this idtac is needed here *);cbn; set_solver
      |
    ].
  Ltac destruct_oapps :=
  repeat (match goal with
  | [H : context [oapp singleton ∅ ?x] |- _] =>
    let P := fresh "P" in
    destruct x eqn:P; simpl in *
  | |- context [oapp singleton ∅ ?x] =>
    let P := fresh "P" in
    destruct x eqn:P; simpl in *
  end;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton));
  repeat app_ext_empty.
  Ltac destruct_solver :=
    destruct_oapps;
    classicize;
    intros;
    destruct_and?;
    rewrite_evar_val;
    simplify_eq;
    try set_solver;
    repeat destruct_evar_val_hyp;
    cbn in *;
    unfold mbind, option_bind, mret, option_ret in *;
    cbn in *; try congruence;
    simplify_eq;
    try set_solver;
    repeat case_match;
    unfold mbind, option_bind, mret, option_ret in *;
    cbn in *;
    unfold mbind, option_bind, mret, option_ret in *;
    cbn in *;
    simplify_eq;
    repeat f_equal;
    try set_solver.
  Ltac solver_macro AX :=
    simplify_krule;
    ((by simplification_solver) ||
    (by timeout 100 destruct_solver));
    tryif done then idtac else (idtac "failed to prove: "; let X := eval cbn in AX in idtac X; admit).

      Goal satT Theory_functional Model.
      Proof.
        unfold satT, satM, Theory_functional. intros.
        unfold_elem_of; destruct_or?; destruct_ex?; subst; cbn.
        all: try (solve_functional_axiom_option_sym; cbn; clear; repeat dependent destruction l; cbv; try congruence; repeat case_match; congruence).
      Defined.

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
* admit.
* simplify_krule.
  destruct_oapps;
  classicize;
  intros;
  destruct_and?;
  rewrite_evar_val;
  simplify_eq;
  try set_solver;
  repeat destruct_evar_val_hyp;
  cbn in *;
  unfold mbind, option_bind, mret, option_ret in *;
  cbn in *; try congruence;
  simplify_eq;
  try set_solver;
  repeat case_match;
  cbn in *;
  simplify_eq;
  try set_solver.
  all: admit. (* TODO *)
* simplify_krule.
  destruct_oapps;
  classicize;
  intros;
  destruct_and?;
  rewrite_evar_val;
  simplify_eq;
  try set_solver;
  repeat destruct_evar_val_hyp;
  cbn in *;
  unfold mbind, option_bind, mret, option_ret in *;
  cbn in *; try congruence;
  simplify_eq;
  try set_solver;
  repeat case_match;
  cbn in *;
  simplify_eq;
  try set_solver.
  all: admit. (* TODO *)
* simplify_krule.
  destruct_oapps;
  classicize;
  intros;
  destruct_and?;
  rewrite_evar_val;
  simplify_eq;
  try set_solver;
  repeat destruct_evar_val_hyp;
  cbn in *;
  unfold mbind, option_bind, mret, option_ret in *;
  cbn in *; try congruence;
  simplify_eq;
  try set_solver;
  repeat case_match;
  cbn in *;
  simplify_eq;
  try set_solver.
  all: admit. (* TODO *)
* simplify_krule.
  destruct_oapps;
  classicize;
  intros;
  destruct_and?;
  rewrite_evar_val;
  simplify_eq;
  try set_solver;
  repeat destruct_evar_val_hyp;
  cbn in *;
  unfold mbind, option_bind, mret, option_ret in *;
  cbn in *; try congruence;
  simplify_eq;
  try set_solver;
  repeat case_match;
  cbn in *;
  simplify_eq;
  try set_solver.
  all: admit. (* TODO *)
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* admit.
* simplify_krule.
  clear AXIOM.



  Check @evar_valuation.
  Ltac unfold_dvs2 :=
    repeat match goal with
    | [n : SortInt_carrier |- _] => destruct n
    | [n : SortBool_carrier |- _] => destruct n
    | [n : SortList_carrier |- _] => destruct n
    | [n : SortMap_carrier |- _] => destruct n
    | [n : SortSet_carrier |- _] => destruct n
    | |- context [@evar_valuation ?Σ ?M ?ρ SortInt ?x] =>
      destruct (@evar_valuation Σ M ρ SortInt x) eqn:H;
      try rewrite -> H in *;
      clear H
    | |- context [@evar_valuation ?Σ ?M ?ρ SortBool ?x] =>
      destruct (@evar_valuation Σ M ρ SortBool x) eqn:H;
      try rewrite -> H in *;
      clear H
    | |- context [@evar_valuation ?Σ ?M ?ρ SortList ?x] =>
      destruct (@evar_valuation Σ M ρ SortList x) eqn:H;
      try rewrite -> H in *;
      clear H
    | |- context [@evar_valuation ?Σ ?M ?ρ SortMap ?x] =>
      destruct (@evar_valuation Σ M ρ SortMap x) eqn:H;
      try rewrite -> H in *;
      clear H
    | |- context [@evar_valuation ?Σ ?M ?ρ SortSet ?x] =>
      destruct (@evar_valuation Σ M ρ SortSet x) eqn:H;
      try rewrite -> H in *;
      clear H
    end.
  unfold_dvs2; simpl in *.
  classicize;
  intros;
  destruct_and?;
  rewrite_evar_val;
  cbn in *;
  simplify_eq;
  rewrite H0.
  unfold mbind, option_bind, mret, option_ret in *;
  simpl.
  repeat case_match;
  cbn in *;
  simplify_eq;
  repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
  repeat app_ext_empty;
  try set_solver;
  destruct_oapps; simplify_eq;
  try set_solver.

  destruct_oapps;
    classicize;
    intros;
    destruct_and?;
    rewrite_evar_val;
    cbn in *;
    simplify_eq;
    try set_solver;
    unfold mbind, option_bind, mret, option_ret in *;
    repeat case_match;
    cbn in *;
    simplify_eq.
    all: try set_solver.
    Arguments node________TREE_Tree_Int_Tree_Tree /.
    - repeat destruct_evar_val_hyp;
      cbn in *;
      try set_solver.
      unfold mbind, option_bind, mret, option_ret in *;
      repeat case_match;
      cbn in *;
      simplify_eq;
      try set_solver.
      all: admit.
    - repeat destruct_evar_val_hyp;
      cbn in *;
      try set_solver.
      unfold mbind, option_bind, mret, option_ret in *;
      repeat case_match;
      cbn in *;
      simplify_eq;
      try set_solver.
      all: cbn in *; simplify_eq.
      all: admit.
    
    all: unfold node________TREE_Tree_Int_Tree_Tree, _780a187 in *;
    simpl in *.
    
    
    all: repeat destruct_evar_val_hyp;
    cbn in *;
    try set_solver.
    rewrite -> H0 in *.

    unfold mbind, option_bind, mret, option_ret in *.
    cbn in *; try congruence;
    simplify_eq;
    try set_solver.
    4: {
    repeat case_match
    unfold mbind, option_bind, mret, option_ret in *;
    cbn in *;
    unfold mbind, option_bind, mret, option_ret in *;
    cbn in *;
    simplify_eq;
    repeat f_equal;
    try set_solver
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
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.
* solver_macro AXIOM.

      Defined.

      End TheorySemantics.

