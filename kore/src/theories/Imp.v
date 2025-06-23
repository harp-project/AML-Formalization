(* From Equations Require Import Equations. *)
From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.

Open Scope string_scope.

Ltac autorewrite_set :=
  repeat (
    rewrite intersection_top_l_L +
    rewrite intersection_top_r_L +
    rewrite union_empty_l_L +
    rewrite union_empty_r_L +
    rewrite propset_difference_neg +
    rewrite propset_union_simpl +
    rewrite propset_intersection_simpl +
    rewrite singleton_subseteq_l
  ).

Ltac basic_simplify_krule :=
  simpl;
  eval_helper;
  repeat rewrite_app_ext;
  autorewrite_set.
Ltac simplify_krule :=
  basic_simplify_krule;
  apply propset_top_elem_of_2;
  intro;
  apply elem_of_PropSet;
  repeat rewrite elem_of_PropSet;
  repeat rewrite singleton_subseteq;
  repeat rewrite singleton_eq.


Ltac abstract_var := 
  match goal with
    | [|- context [evar_valuation ?σ ?s]] =>
      let x := fresh "var" in
      let Hx := fresh "Hvar" in
        remember (evar_valuation σ s) as x eqn:Hx (*;
        clear Hx;
        revert x *)
    end.

Module ImpSyntax.

  Inductive Ksorts :=
  | Kbool
  | Kint
  | Klist
  | Kitem
  | K.


  Instance Ksorts_eq_dec : EqDecision Ksorts.
  Proof. solve_decision. Defined.


  Program Instance Ksorts_finite : finite.Finite Ksorts := {
    enum := [Kbool; Kint; Klist; Kitem; K];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined.

  Inductive Ksyms :=
  (* Kbool *)
  | Ktrue
  | Kfalse
  | KnotBool
  | KandBool
  | KandThenBool
  | KxorBool
  | KorBool
  | KorElseBool
  | KimpliesBool
  | KeqBool
  | KneqBool
  (* Kint *)
  | KintVal (z : Z)
  | Kstderr_K_IO_Int
    (* Lbl'Hash'stderr'Unds'K-IO'Unds'Int{}() : SortInt{} *)
  | Kstdin_K_IO_Int
    (* Lbl'Hash'stdin'Unds'K-IO'Unds'Int{}() : SortInt{} *)
  | Kstdout_K_IO_Int
    (* Lbl'Hash'stdout'Unds'K-IO'Unds'Int{}() : SortInt{} *)
  | KtimeLParRPar_K_IO_Int
    (* Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int{}() : SortInt{} *)
  | KtmodInt
    (* Lbl'UndsPerc'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KandInt
    (* Lbl'UndsAnd-'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KmultInt
    (* Lbl'UndsStar'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KplusInt
    (* Lbl'UndsPlus'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KsubInt
    (* Lbl'Unds'-Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KtdivInt
    (* Lbl'UndsSlsh'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KltltInt
    (* Lbl'Unds-LT--LT-'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KleInt
    (* Lbl'Unds-LT-Eqls'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} *)
  | KltInt
    (* Lbl'Unds-LT-'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} *)
  | KneqInt
    (* Lbl'UndsEqlsSlshEqls'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} *)
  | KeqInt
    (* Lbl'UndsEqlsEqls'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} *)
  | KgeInt
    (* Lbl'Unds-GT-Eqls'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} *)
  | KgtgtInt
    (* Lbl'Unds-GT--GT-'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KgtInt
    (* Lbl'Unds-GT-'Int'Unds'{}(SortInt{}, SortInt{}) : SortBool{} *)
  | KpowmodInt
    (* Lbl'UndsXor-Perc'Int'UndsUnds'{}(SortInt{}, SortInt{}, SortInt{}) : SortInt{} *)
  | KpowInt
    (* Lbl'UndsXor-'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KdivInt
    (* Lbl'Unds'divInt'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KdividesInt
    (* Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortBool{} *)
  | KmodInt
    (* Lbl'Unds'modInt'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KxorInt
    (* Lbl'Unds'xorInt'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KorInt
    (* Lbl'UndsPipe'Int'Unds'{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KabsInt
    (* LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int{}(SortInt{}) : SortInt{} *)
  | KbitRangeInt
    (* LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}, SortInt{}) : SortInt{} *)
  | KfreshInt
    (* LblfreshInt'LParUndsRParUnds'INT'Unds'Int'Unds'Int{}(SortInt{}) : SortInt{} *)
  | Klog2Int 
    (* Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int{}(SortInt{}) : SortInt{} *)
  | KmaxInt
    (* LblmaxInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KminInt
    (* LblminInt'LParUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}) : SortInt{} *)
  | KrandInt
    (* LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int{}(SortInt{}) : SortInt{} *)
  | KsignExtendBitRangeInt (* LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int{}(SortInt{}, SortInt{}, SortInt{}) : SortInt{} *)
  | KnotInt
    (* Lbl'Tild'Int'Unds'{}(SortInt{}) : SortInt{} *)


  (* list *)
  | KNil (* hooked-symbol Lbl'Stop'List{}() : SortList{} *)
  | KgetList (* hooked-symbol LblList'Coln'get{}(SortList{}, SortInt{}) : SortKItem{} *)
  | KrangeList (* hooked-symbol LblList'Coln'range{}(SortList{}, SortInt{}, SortInt{}) : SortList{} *)
  | KsetList (* hooked-symbol LblList'Coln'set{}(SortList{}, SortInt{}, SortKItem{}) : SortList{} *)
  | KlistItem (* hooked-symbol LblListItem{}(SortKItem{}) : SortList{} *)
  | KconcatList (* hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{} *)
  | KinList (* hooked-symbol Lbl'Unds'inList'Unds'{}(SortKItem{}, SortList{}) : SortBool{} *)
  | KisList (* symbol LblisList{}(SortK{}) : SortBool{} *)


  (* kitem *)

  (* K *)
  | dotK
  | Kseq
  | Kappend
  .

  Instance Ksyms_eq_dec : EqDecision Ksyms.
  Proof. solve_decision. Defined.
  Print Ksyms.

  (* Program Instance Ksyms_finite : finite.Finite Ksyms := {
    enum := [   Ktrue
  ; Kfalse
  ; KnotBool
  ; KandBool
  ; KandThenBool
  ; KxorBool
  ; KorBool
  ; KorElseBool
  ; KimpliesBool
  ; KeqBool
  ; KneqBool
  ; KintVal
  ; Kstderr_K_IO_Int
  ; Kstdin_K_IO_Int
  ; Kstdout_K_IO_Int
  ; KtimeLParRPar_K_IO_Int
  ; KtmodInt
  ; KandInt
  ; KmultInt
  ; KplusInt
  ; KsubInt
  ; KtdivInt
  ; KltltInt
  ; KleInt
  ; KltInt
  ; KneqInt
  ; KeqInt
  ; KgeInt
  ; KgtgtInt
  ; KgtInt
  ; KpowmodInt
  ; KpowInt
  ; KdivInt
  ; KdividesInt
  ; KmodInt
  ; KxorInt
  ; KorInt
  ; KabsInt
  ; KbitRangeInt
  ; KfreshInt
  ; Klog2Int
  ; KmaxInt
  ; KminInt
  ; KrandInt
  ; KsignExtendBitRangeInt
  ; KnotIntl;
  ; KNil
  ; KgetList
  ; KrangeList
  ; KsetList
  ; KlistItem
  ; KconcatList
  ; KinList
  ; KisList];
  }.
  Next Obligation. compute_done. Defined.
  Final Obligation. destruct x; set_solver. Defined. *)

  Check inj_countable.

  Local Definition Ksyms_to_gen_tree (σ : Ksyms) : gen_tree (nat + Z) :=
  match σ with
   | Ktrue => GenLeaf (inl 0)
   | Kfalse => GenLeaf (inl 1)
   | KnotBool => GenLeaf (inl 2)
   | KandBool => GenLeaf (inl 3)
   | KandThenBool => GenLeaf (inl 4)
   | KxorBool => GenLeaf (inl 5)
   | KorBool => GenLeaf (inl 6)
   | KorElseBool => GenLeaf (inl 7)
   | KimpliesBool => GenLeaf (inl 8)
   | KeqBool => GenLeaf (inl 9)
   | KneqBool => GenLeaf (inl 10)
   | KintVal z => GenLeaf (inr z)
   | Kstderr_K_IO_Int => GenLeaf (inl 11)
   | Kstdin_K_IO_Int => GenLeaf (inl 12)
   | Kstdout_K_IO_Int => GenLeaf (inl 13)
   | KtimeLParRPar_K_IO_Int => GenLeaf (inl 14)
   | KtmodInt => GenLeaf (inl 15)
   | KandInt => GenLeaf (inl 16)
   | KmultInt => GenLeaf (inl 17)
   | KplusInt => GenLeaf (inl 18)
   | KsubInt => GenLeaf (inl 19)
   | KtdivInt => GenLeaf (inl 20)
   | KltltInt => GenLeaf (inl 21)
   | KleInt => GenLeaf (inl 22)
   | KltInt => GenLeaf (inl 23)
   | KneqInt => GenLeaf (inl 24)
   | KeqInt => GenLeaf (inl 25)
   | KgeInt => GenLeaf (inl 26)
   | KgtgtInt => GenLeaf (inl 27)
   | KgtInt => GenLeaf (inl 28)
   | KpowmodInt => GenLeaf (inl 29)
   | KpowInt => GenLeaf (inl 30)
   | KdivInt => GenLeaf (inl 31)
   | KdividesInt => GenLeaf (inl 32)
   | KmodInt => GenLeaf (inl 33)
   | KxorInt => GenLeaf (inl 34)
   | KorInt => GenLeaf (inl 35)
   | KabsInt => GenLeaf (inl 36)
   | KbitRangeInt => GenLeaf (inl 37)
   | KfreshInt => GenLeaf (inl 38)
   | Klog2Int => GenLeaf (inl 39)
   | KmaxInt => GenLeaf (inl 40)
   | KminInt => GenLeaf (inl 41)
   | KrandInt => GenLeaf (inl 42)
   | KsignExtendBitRangeInt => GenLeaf (inl 43)
   | KnotInt => GenLeaf (inl 44)
   | KNil => GenLeaf (inl 45)
   | KgetList => GenLeaf (inl 46)
   | KrangeList => GenLeaf (inl 47)
   | KsetList => GenLeaf (inl 48)
   | KlistItem => GenLeaf (inl 49)
   | KconcatList => GenLeaf (inl 50)
   | KinList => GenLeaf (inl 51)
   | KisList => GenLeaf (inl 52)
   | dotK => GenLeaf (inl 53)
   | Kseq => GenLeaf (inl 54)
   | Kappend => GenLeaf (inl 55)
  end.
  Print Ksyms.
  Local Definition gen_tree_to_Ksyms (t : gen_tree (nat + Z)) : option Ksyms :=
  match t with
  | GenLeaf (inl x) => match x with
                       | 0 => Some Ktrue
                       | 1 => Some Kfalse
                       | 2 => Some KnotBool
                       | 3 => Some KandBool
                       | 4 => Some KandThenBool
                       | 5 => Some KxorBool
                       | 6 => Some KorBool
                       | 7 => Some KorElseBool
                       | 8 => Some KimpliesBool
                       | 9 => Some KeqBool
                       | 10 => Some KneqBool
                       | 11 => Some Kstderr_K_IO_Int
                       | 12 => Some Kstdin_K_IO_Int
                       | 13 => Some Kstdout_K_IO_Int
                       | 14 => Some KtimeLParRPar_K_IO_Int
                       | 15 => Some KtmodInt
                       | 16 => Some KandInt
                       | 17 => Some KmultInt
                       | 18 => Some KplusInt
                       | 19 => Some KsubInt
                       | 20 => Some KtdivInt
                       | 21 => Some KltltInt
                       | 22 => Some KleInt
                       | 23 => Some KltInt
                       | 24 => Some KneqInt
                       | 25 => Some KeqInt
                       | 26 => Some KgeInt
                       | 27 => Some KgtgtInt
                       | 28 => Some KgtInt
                       | 29 => Some KpowmodInt
                       | 30 => Some KpowInt
                       | 31 => Some KdivInt
                       | 32 => Some KdividesInt
                       | 33 => Some KmodInt
                       | 34 => Some KxorInt
                       | 35 => Some KorInt
                       | 36 => Some KabsInt
                       | 37 => Some KbitRangeInt
                       | 38 => Some KfreshInt
                       | 39 => Some Klog2Int
                       | 40 => Some KmaxInt
                       | 41 => Some KminInt
                       | 42 => Some KrandInt
                       | 43 => Some KsignExtendBitRangeInt
                       | 44 => Some KnotInt
                       | 45 => Some KNil
                       | 46 => Some KgetList
                       | 47 => Some KrangeList
                       | 48 => Some KsetList
                       | 49 => Some KlistItem
                       | 50 => Some KconcatList
                       | 51 => Some KinList
                       | 52 => Some KisList
                       | 53 => Some dotK
                       | 54 => Some Kseq
                       | 55 => Some Kappend
                       | _ => None
                       end
  | GenLeaf (inr x) => Some (KintVal x)
  | _ => None
  end.


  Instance Ksyms_countable : Countable Ksyms.
  Proof.
    apply inj_countable with (f := Ksyms_to_gen_tree) (g := gen_tree_to_Ksyms).
    intros x. destruct x; try by simpl.
  Defined.


  Program Instance ImpSignature : Signature := {|
    sorts := {|
      sort := Ksorts;
      subsort s1 s2 :=
        match decide (s1 = s2) with
        | left _ => True
        | _ => False
        end
    |};
    variables := StringVariables;
    symbols := {|
      symbol := Ksyms;
      arg_sorts σ :=
        match σ with
        | Ktrue => []
        | Kfalse => []
        | KnotBool => [Kbool]
        | KandBool => [Kbool; Kbool]
        | KandThenBool => [Kbool; Kbool]
        | KxorBool => [Kbool; Kbool]
        | KorBool => [Kbool; Kbool]
        | KorElseBool => [Kbool; Kbool]
        | KimpliesBool => [Kbool; Kbool]
        | KeqBool => [Kbool; Kbool]
        | KneqBool => [Kbool; Kbool]
        | KintVal z => []
        | Kstderr_K_IO_Int => []
        | Kstdin_K_IO_Int => []
        | Kstdout_K_IO_Int => []
        | KtimeLParRPar_K_IO_Int => []
        | KtmodInt => [Kint; Kint]
        | KandInt => [Kint; Kint]
        | KmultInt => [Kint; Kint]
        | KplusInt => [Kint; Kint]
        | KsubInt => [Kint; Kint]
        | KtdivInt => [Kint; Kint]
        | KltltInt => [Kint; Kint]
        | KleInt => [Kint; Kint]
        | KltInt => [Kint; Kint]
        | KneqInt => [Kint; Kint]
        | KeqInt => [Kint; Kint]
        | KgeInt => [Kint; Kint]
        | KgtgtInt => [Kint; Kint]
        | KgtInt => [Kint; Kint]
        | KpowmodInt => [Kint; Kint; Kint]
        | KpowInt => [Kint; Kint]
        | KdivInt => [Kint; Kint]
        | KdividesInt => [Kint; Kint]
        | KmodInt => [Kint; Kint]
        | KxorInt => [Kint; Kint]
        | KorInt => [Kint; Kint]
        | KabsInt => [Kint]
        | KbitRangeInt => [Kint; Kint; Kint]
        | KfreshInt => [Kint]
        | Klog2Int => [Kint]
        | KmaxInt => [Kint; Kint]
        | KminInt => [Kint; Kint]
        | KrandInt => [Kint; Kint; Kint]
        | KsignExtendBitRangeInt => [Kint; Kint; Kint]
        | KnotInt => [Kint]
        | KNil => []
        | KgetList => [Klist; Kint]
        | KrangeList => [Klist; Kint; Kint]
        | KsetList => [Klist; Kint; Kitem]
        | KlistItem => [Kitem]
        | KconcatList => [Klist; Klist]
        | KinList => [Kitem; Klist]
        | KisList => [Kitem]
        | dotK => []
        | Kseq => [Kitem; K]
        | Kappend => [K;K]
        end;
      ret_sort σ :=
        match σ with
         | Ktrue => Kbool
         | Kfalse => Kbool
         | KnotBool => Kbool
         | KandBool => Kbool
         | KandThenBool => Kbool
         | KxorBool => Kbool
         | KorBool => Kbool
         | KorElseBool => Kbool
         | KimpliesBool => Kbool
         | KeqBool => Kbool
         | KneqBool => Kbool
         | KintVal z => Kint
         | Kstderr_K_IO_Int => Kint
         | Kstdin_K_IO_Int => Kint
         | Kstdout_K_IO_Int => Kint
         | KtimeLParRPar_K_IO_Int => Kint
         | KtmodInt => Kint
         | KandInt => Kint
         | KmultInt => Kint
         | KplusInt => Kint
         | KsubInt => Kint
         | KtdivInt => Kint
         | KltltInt => Kint
         | KleInt => Kbool
         | KltInt => Kbool
         | KneqInt => Kbool
         | KeqInt => Kbool
         | KgeInt => Kbool
         | KgtgtInt => Kint
         | KgtInt => Kbool
         | KpowmodInt => Kint
         | KpowInt => Kint
         | KdivInt => Kint
         | KdividesInt => Kbool
         | KmodInt => Kint
         | KxorInt => Kint
         | KorInt => Kint
         | KabsInt => Kint
         | KbitRangeInt => Kint
         | KfreshInt => Kint
         | Klog2Int => Kint
         | KmaxInt => Kint
         | KminInt => Kint
         | KrandInt => Kint
         | KsignExtendBitRangeInt => Kint
         | KnotInt => Kint
         | KNil => Klist
         | KgetList => Kitem
         | KrangeList => Klist
         | KsetList => Klist
         | KlistItem => Klist
         | KconcatList => Klist
         | KinList => Kbool
         | KisList => Kbool
         | dotK => K
         | Kseq => K
         | Kappend => K
        end;
    |};
  |}.
  Final Obligation.
    cbv; intros; destruct s1, s2; try congruence.
  Defined.
(*   Final Obligation.
    cbv.
    apply Build_PartialOrder.
    * apply Build_PreOrder.
      - intro s. cbv; by destruct s.
      - intros s1 s2 s3; by destruct s1, s2, s3.
    * intros s1 s2; intros. destruct s1, s2; try reflexivity; try by contradiction.
  Defined.
 *)
  Open Scope string_scope.
  Open Scope kore_scope.

(*
grep -Eo "\\\\dv{[^}]*}[^\(]*\([^\)]*\)" /tmp/definition.kore > /tmp/matches

dv is only used with the following parameters:
\dv{SortBool{}}("true")
\dv{SortBool{}}("false")
\dv{SortInt{}}("n") (n is a number)
\dv{SortString{}}("s") (s is a string)
\dv{SortKConfigVar{}}("$PGM")
 *)
  Definition Kbool_theory_behavioural : @Theory ImpSignature :=
    PropSet (fun pat =>
      (** negation: *)
      (* not false = true *)
      (exists R, pat =                              (* v-- this should be dv *)
        existT R ((Top{R} and kore_fevar "X" ⊆k{R} Kfalse ⋅ ⟨⟩)
          --->ₖ                               (* v-- this should be dv *)
         (KnotBool ⋅ ⟨kore_fevar "X"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool})))
      ) \/
      (* not true = false *)
      (exists R, pat =
        existT R ((Top{R} and kore_fevar "X" ⊆k{R} Ktrue ⋅ ⟨⟩)
          --->ₖ
        (KnotBool ⋅ ⟨kore_fevar "X"⟩ =k{R} (Kfalse ⋅ ⟨⟩ and Top{Kbool})))
      ) \/
      (** conjunction *)
      (* rule `_andBool_`(#token("false","Bool") #as _Gen1,_Gen0)=>_Gen1 *)
      (exists R, pat =
        existT R ((Top{R} and
                   kore_fevar "X0" ⊆k{R} (Kfalse ⋅ ⟨⟩ and kore_fevar "Gen1") and
                   @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and
                   Top{R})
          --->ₖ
        (KandBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "Gen1" and Top{Kbool})))
      ) \/
      ((* rule `_andBool_`(B,#token("true","Bool"))=>B *)
        exists R, pat =
          existT R (
            Top{R} --->ₖ
            KandBool ⋅ ⟨kore_fevar "B"; Ktrue ⋅ ⟨⟩ ⟩ =k{R} (kore_fevar "B" and Top{Kbool})
          )
      ) \/
      ( (* rule `_andBool_`(_Gen0,#token("false","Bool"))=>#token("false","Bool") *)
        exists R, pat =
          existT R (
            Top{R} --->ₖ
            KandBool ⋅ ⟨kore_fevar "Gen0"; Kfalse ⋅ ⟨⟩ ⟩ =k{R} (Kfalse ⋅ ⟨ ⟩ and Top{Kbool})
        )
      ) \/
      ( (* rule `_andBool_`(#token("true","Bool"),B)=>B *)
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->ₖ
            (KandBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (** andthen *)
      (*rule `_andThenBool_`(#token("false","Bool") #as _Gen1,_Gen0)=>_Gen1*)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} (Kfalse ⋅ ⟨⟩ and kore_fevar "Gen1") and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->ₖ
            (KandThenBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "Gen1" and Top{Kbool}))
          )
      ) \/
      (*rule `_andThenBool_`(K,#token("true","Bool"))=>K*)
      (
        exists R, pat =
          existT R (
            Top{R} --->ₖ
            KandThenBool ⋅ ⟨kore_fevar "K"; Ktrue ⋅ ⟨⟩ ⟩ =k{R} (kore_fevar "K" and Top{Kbool})
          )
      ) \/
      (*rule `_andThenBool_`(_Gen0,#token("false","Bool"))=>#token("false","Bool")*)
      (
        exists R, pat =
          existT R (
            Top{R} --->ₖ
            KandThenBool ⋅ ⟨kore_fevar "Gen0"; Kfalse ⋅ ⟨⟩ ⟩ =k{R} (Kfalse ⋅ ⟨ ⟩ and Top{Kbool})
        )
      ) \/
      (*rule `_andThenBool_`(#token("true","Bool"),K)=>K*)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "K" and Top{R}
            --->ₖ
            (KandThenBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "K" and Top{Kbool}))
          )
      ) \/
      (** xorBool *)
      (* rule `_xorBool_`(B,B)=>#token("false","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and @kore_fevar _ _ _ Kbool "X0" ⊆k{R} kore_fevar "B" and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->ₖ
            (KxorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Kfalse ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_xorBool_`(B,#token("false","Bool"))=>B *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->ₖ
            (KxorBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_xorBool_`(#token("false","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->ₖ
            (KxorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (** orBool *)
      (* rule `_orBool_`(B,#token("false","Bool"))=>B *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->ₖ
            (KorBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->ₖ
            (KorBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(#token("false","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->ₖ
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(#token("true","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->ₖ
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (** orElseBool *)
      (* rule `_orElseBool_`(K,#token("false","Bool"))=>K *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->ₖ
            (KorBool ⋅ ⟨kore_fevar "K"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "K" and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->ₖ
            (KorBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(#token("false","Bool"),K)=>K *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "K" and Top{R}
            --->ₖ
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "K" and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(#token("true","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->ₖ
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (** impliesBool *)
      (* `_impliesBool_`(B,#token("false","Bool"))=>`notBool_`(B) *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->ₖ
            (KimpliesBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (KnotBool ⋅ ⟨kore_fevar "B"⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->ₖ
            (KimpliesBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(#token("false","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->ₖ
            (KimpliesBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(#token("true","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->ₖ
            (KimpliesBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* NOTE: there are no other behavioural axioms about ==Bool and =/=Bool! *)
      ( (* rule `_=/=Bool_`(B1,B2)=>`notBool_`(`_==Bool_`(B1,B2)) *)
        exists R, pat =
          existT R (
            Top{R} and @kore_fevar _ _ _ Kbool "X0" ⊆k{R} kore_fevar "B1" and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B2" and Top{R}
            --->ₖ
            (KneqBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (KnotBool ⋅ ⟨ KeqBool ⋅ ⟨kore_fevar "B1"; kore_fevar "B2"⟩⟩ and Top{Kbool}))
          )
      )
    ).
    (** functional axioms *)
    Definition Kbool_theory_functional : @Theory ImpSignature :=
      PropSet (fun pat =>
      exists R, pat =
        existT R (
          kore_exists Kbool (KandBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
      )) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KandThenBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KimpliesBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KorBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KorElseBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KxorBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KneqBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KeqBool ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar (In_nil)
        ))
      ) \/
      (
      exists R, pat =
        existT R (
          kore_exists Kbool (KnotBool ⋅ ⟨kore_fevar "K0"⟩ =k{R} kore_bevar (In_nil)
        ))
      )
    )
    .
    (* Sometimes, implicit arguments are needed, e.g. if X ⊆ Y, and X and Y are both free variables. However, this might be resolved if X and Y would be bound *)



   (* Questions here:
      - How should we model hooked symbols, which do not have any axioms (not even functional ones)?---in some cases (maybe in all) there is a hook/smt-hook on these.
        These are:
           KtimeLParRPar_K_IO_Int - Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int - hook: IO.time
           KtmodInt - Lbl'UndsPerc'Int'Unds' - hook: INT.tmod
           KtdivInt - Lbl'UndsSlsh'Int'Unds' - hook: INT.tdiv
           KltltInt - Lbl'Unds-LT--LT-'Int'Unds' - hook: INT.shl
           KgtgtInt - Lbl'Unds-GT--GT-'Int'Unds' - hook: INT.shr
           KpowmodInt - Lbl'UndsXor-Perc'Int'UndsUnds' - hook: INT.powmod
           KpowInt - Lbl'UndsXor-'Int'Unds' - hook: INT.pow
           KdivInt - Lbl'Unds'divInt'Unds' - hook: INT.ediv
           KmodInt - Lbl'Unds'modInt'Unds' - hook: INT.emod
           KbitRangeInt - LblbitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int - hook: INT.bitRange
           KsignExtendBitRangeInt - LblsignExtendBitRangeInt'LParUndsCommUndsCommUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int'Unds'Int'Unds'Int - hook: INT.signExtendBitRange
           Klog2Int - Lbllog2Int'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int - hook: INT.log2
           KrandInt - LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int - hook: INT.rand
      - There is a potential issue:
           KdividesInt - Lbl'Unds'dividesInt'UndsUnds'INT-COMMON'Unds'Bool'Unds'Int'Unds'Int
                         THERE IS NO HOOK for this symbol!!!!
                         But there is no functional axiom either. However, there
                         is one behavioural axiom for it.
      - What should we do with the attributes (e.g., total, functional, freshGenerator)? Why is freshInt the identity function?
      - There are axioms for minInt, but none for maxInt?
      - Where are the axioms for INT-SYMBOLIC? Should we also include those in the
        formalisation of the stdlib?
      - Where is the implementation of INT.rand? I could not find it in the compiler.
   *)
   Definition Kint_theory_behavioural : @Theory ImpSignature :=
    PropSet (fun pat =>
      (exists R, pat =
        existT R (Top{R} and Top{R} --->ₖ Kstderr_K_IO_Int ⋅⟨⟩ =k{R} KintVal 2 ⋅ ⟨⟩)
      ) \/
      (exists R, pat =
        existT R (Top{R} and Top{R} --->ₖ Kstdin_K_IO_Int ⋅⟨⟩ =k{R} KintVal 0 ⋅ ⟨⟩)
      ) \/
      (exists R, pat =
        existT R (Top{R} and Top{R} --->ₖ Kstdout_K_IO_Int ⋅⟨⟩ =k{R} KintVal 1 ⋅ ⟨⟩)
      ) \/
      (exists R, pat =
        existT R (
          Top{R} and @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R}
          --->ₖ
          (KneqInt ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (KnotBool ⋅ ⟨KeqInt ⋅ ⟨kore_fevar "I1" ; kore_fevar "I2"⟩ ⟩ and Top{Kbool}))
        )
      ) \/
      (exists R, pat =
        existT R (
          KneqInt ⋅ ⟨kore_fevar "I2"; KintVal 0 ⋅ ⟨⟩ ⟩ =k{R} Ktrue ⋅ ⟨⟩ and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R} --->ₖ
          KdivInt ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (KtdivInt ⋅ ⟨KsubInt ⋅ ⟨kore_fevar "I1" ; KmodInt ⋅ ⟨kore_fevar "I1"; kore_fevar "I2"⟩ ⟩; kore_fevar "I2"⟩ and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          Top{R} and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R} --->ₖ
          KdividesInt ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (KeqInt ⋅ ⟨KtmodInt ⋅ ⟨kore_fevar "I2" ; kore_fevar "I1" ⟩; KintVal 0 ⋅ ⟨⟩⟩ and Top{Kbool})
        )
      ) \/
      (exists R, pat =
        existT R (
          KneqInt ⋅ ⟨kore_fevar "I2"; KintVal 0 ⋅ ⟨⟩⟩ =k{R} Ktrue ⋅ ⟨⟩ --->ₖ
          KmodInt ⋅ ⟨kore_fevar "I1"; kore_fevar "I2"⟩ =k{R}
            (KtmodInt ⋅ ⟨KplusInt ⋅
                         ⟨KtmodInt ⋅ ⟨kore_fevar "I1";
                                      KabsInt ⋅⟨kore_fevar "I2"⟩⟩;
                          KabsInt ⋅ ⟨kore_fevar "I2"⟩ ⟩;
                        KabsInt ⋅ ⟨kore_fevar "I2"⟩ ⟩ and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "IDX" and
          @kore_fevar _ _ _ Kint "X2" ⊆k{R} kore_fevar "LEN" and Top{R} --->ₖ
          KbitRangeInt ⋅⟨ kore_fevar "X0"; kore_fevar "X1"; kore_fevar "X2"⟩ =k{R}
            (KmodInt ⋅ ⟨KgtgtInt ⋅ ⟨kore_fevar "I"; kore_fevar "IDX"⟩;
                        KltltInt ⋅ ⟨KintVal 1 ⋅ ⟨⟩; kore_fevar "LEN"⟩⟩ and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          Top{R} and @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I" and Top{R} --->ₖ
          KfreshInt ⋅ ⟨ kore_fevar "X0" ⟩ =k{R} (kore_fevar "I" and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          KltInt ⋅ ⟨kore_fevar "I1"; kore_fevar "I2"⟩ =k{R} Ktrue ⋅ ⟨⟩ and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R} --->ₖ
          KminInt⋅⟨ kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "I1" and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          KgeInt ⋅ ⟨kore_fevar "I1"; kore_fevar "I2"⟩ =k{R} Ktrue ⋅ ⟨⟩ and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R} --->ₖ
          KminInt⋅⟨ kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "I2" and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          Top{R} and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "IDX" and
          @kore_fevar _ _ _ Kint "X2" ⊆k{R} kore_fevar "LEN" and Top{R} --->ₖ
          KsignExtendBitRangeInt ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"; kore_fevar "X2"⟩ =k{R}
            (KsubInt ⋅ ⟨KmodInt ⋅ ⟨KplusInt ⋅ ⟨KbitRangeInt ⋅ ⟨kore_fevar "I";kore_fevar "IDX"; kore_fevar "LEN"⟩; KltltInt ⋅ ⟨KintVal 1 ⋅⟨⟩; KsubInt ⋅ ⟨kore_fevar "LEN" ; KintVal 1 ⋅⟨⟩⟩⟩⟩;
                                   KltltInt ⋅ ⟨KintVal 1 ⋅⟨⟩; KsubInt ⋅ ⟨kore_fevar "LEN" ; KintVal 1 ⋅⟨⟩⟩⟩⟩;
                        KltltInt ⋅ ⟨KintVal 1 ⋅⟨⟩; KsubInt ⋅ ⟨kore_fevar "LEN" ; KintVal 1 ⋅⟨⟩⟩⟩⟩
              and Top{Kint})
        )
      )
    ).

   Definition Kint_theory_functional : @Theory ImpSignature :=
    PropSet (fun pat =>
      (
        exists R, pat = existT R (
          kore_exists Kint (Kstderr_K_IO_Int ⋅ ⟨⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (Kstdin_K_IO_Int ⋅ ⟨⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (Kstdout_K_IO_Int ⋅ ⟨⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KandInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KmultInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KplusInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KsubInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kbool (KleInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kbool (KltInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kbool (KneqInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kbool (KeqInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kbool (KgeInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kbool (KgtInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KxorInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KorInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KabsInt ⋅ ⟨kore_fevar "K0"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KfreshInt ⋅ ⟨kore_fevar "K0"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KmaxInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KminInt ⋅ ⟨kore_fevar "K0"; kore_fevar "K1"⟩ =k{R} kore_bevar In_nil)
        )
      ) \/
      (
        exists R, pat = existT R (
          kore_exists Kint (KnotInt ⋅ ⟨kore_fevar "K0"⟩ =k{R} kore_bevar In_nil)
        )
      )
    ).

  Definition Ktheory_behavioural : @Theory ImpSignature :=
    PropSet (fun pat =>
      (
        exists R, pat = existT R (
          (Top{R} and (kore_fevar "X0" ⊆k{R} dotK ⋅⟨⟩) and
          kore_fevar "X1" ⊆k{R} @kore_fevar _ _ _ K "TAIL")
          --->ₖ
          (Kappend ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R}
          (kore_fevar "TAIL" and Top{K}))
        )
      ) \/
      (
        exists R, pat = existT R (
          (Top{R} and (kore_fevar "X0" ⊆k{R} Kseq ⋅⟨kore_fevar "K"; kore_fevar "KS"⟩) and
          kore_fevar "X1" ⊆k{R} @kore_fevar _ _ _ K "TAIL")
          --->ₖ
          Kappend ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R}
          (Kseq ⋅⟨kore_fevar "K"; Kappend ⋅ ⟨kore_fevar "KS"; kore_fevar "TAIL"⟩ and Top{K} ⟩ )
        )
      )
    ).

  Definition KList_theory_functional : @Theory ImpSignature :=
    PropSet (fun pat =>
      (
        exists R, pat = existT R (
          
        )
      )
    ).

  Definition KList_theory_behavioural : @Theory ImpSignature :=
    PropSet (fun pat =>
      (
        exists R, pat = existT R (
          
        )
      )
    ).



End ImpSyntax.

(* Tactic Notation "deconstruct_elem_of_Theory" :=
  repeat match goal with
  | [ H : _ ∈ ?Γ |- _ ] => destruct H
  end; (* clear; *) simpl. *)

(* Lemma propset_full_or_empty :
  forall (P : Prop),
    {[_ | P]} = ⊤ \/ {[_ | P]} = ⊥. *)

Module ImpSemantics.

  Import ImpSyntax.

  Definition neqbB (b1 b2 : bool) : bool :=
    negb (Bool.eqb b1 b2).
  Arguments neqbB /.
  Definition neqbZ (b1 b2 : Z) : bool :=
    negb (Z.eqb b1 b2).
  Arguments neqbZ /.

  Open Scope Z_scope.


  (* NOTE: Beware the difference between mod and rem
     (and quot and div) *)
  (*
    Following defs are taken from: https://github.com/runtimeverification/k/blob/eff6bea3f2118bb02c185888d1b369c5c2a59ec3/k-frontend/src/main/java/org/kframework/compile/ConstantFolding.java#L552
  *)
  (* TODO: Java throws an exception if idx or length is not unsigned *)
  Definition bitRange (i idx len : Z) : Z :=
    Z.shiftr
      (Z.land i (Z.shiftl (Z.shiftl 1 len - 1) idx))
      idx.
  Arguments bitRange /.

  (* TODO: Java throws an exception if idx or length is not unsigned *)
  Definition signExtendBitRange (i idx len : Z) : Z :=
  match len with
  | 0 => 0
  | _ =>
    if Z.testbit i (idx + len - 1)
    then
      let max := Z.shiftl 1 (len - 1) in
        let tmp := bitRange i idx len in
          bitRange (tmp + max) 0 len - max
    else bitRange i idx len
  end.
  Arguments signExtendBitRange /.

  Definition emod (a b : Z) : Z :=
    let rem := Z.rem a b in
    if rem <? 0
    then rem + Z.abs b
    else rem.
  Arguments emod /.

  Definition ediv (a b : Z) : Z :=
    Z.quot (a - emod a b) b.
  Arguments ediv /.

  (* REPORT modPow:
     This is how the Java code works, but every other
     operations is relying on rem, and not mod!
     Are we sure, that all backends understand mod and
     div as rem and quot?
   *)
  Definition modPow (a b c : Z) : Z :=
    Z.modulo (Z.pow a b) c.
  Arguments modPow /.

  Compute modPow (-7) 3 20.

  (* BEWARE the order of arguments! *)
  Definition divides (a b : Z) : bool :=
    Z.rem b a =? 0.
  Arguments divides /.

  (* Program Definition ImpModel : @Model ImpSignature :=
    mkModel (* _singleton *)
      (Ksorts_rect _ bool Z)
      (Ksyms_rect _ {[true]}
                    {[false]}
                    (fun x => singleton (negb x))
                    (fun x y => singleton (andb x y))
                    (fun x y => singleton (andb x y))
                    (fun x y => singleton (xorb x y))
                    (fun x y => singleton (orb x y))
                    (fun x y => singleton (orb x y))
                    (fun x y => singleton (implb x y))
                    (fun x y => singleton (eqb x y))
                    (fun x y => singleton (neqbB x y))
                    (fun x => {[x]})
                    {[2]}
                    {[0]}
                    {[1]}
                    {[0]} (* unsure about this *)
                    (fun x y => singleton (Z.rem x y))
                    (fun x y => singleton (Z.land x y)) (* unsure about this *)
                    (fun x y => singleton (Z.mul x y))
                    (fun x y => singleton (Z.add x y))
                    (fun x y => singleton (Z.sub x y))
                    (fun x y => singleton (Z.quot x y))
                    (fun x y => singleton (Z.shiftl x y))
                    (fun x y => singleton (Z.leb x y))
                    (fun x y => singleton (Z.ltb x y))
                    (fun x y => singleton (neqbZ x y))
                    (fun x y => singleton (Z.eqb x y))
                    (fun x y => singleton (Z.geb x y))
                    (fun x y => singleton (Z.shiftr x y))
                    (fun x y => singleton (Z.gtb x y))
                    (fun x y z => singleton (modPow x y z)) (* powmod *)
                    (fun x y => singleton (Z.pow x y)) (* pow *)
                    (fun x y => singleton (ediv x y)) (* div *)
                    (fun x y => singleton (divides x y)) (* divides *)
                    (fun x y => singleton (emod x y)) (* mod *)
                    (fun x y => singleton (Z.lxor x y)) (* xor *)
                    (fun x y => singleton (Z.lor x y))  (* or *)
                    (singleton ∘ Z.abs) (* abs *)
                    (fun x y z => singleton (bitRange x y z)) (* bitRange *)
                    (fun x => singleton x) (* fresh *)
                    (fun x => singleton (Z.log2 x)) (* log2 *)
                    (fun x y => singleton (Z.max x y))
                    (fun x y => singleton (Z.min x y))
                    (fun x y z => ⊤) (* rand - how should we model random generation? I could not find the corresponding implementation! *)
                    (fun x y z => singleton (signExtendBitRange x y z)) (* signExtendBitRangeInt *)
                    (singleton ∘ Z.lnot)) (* not *)
      ltac:(intros []; auto with typeclass_instances). *)
  Program Definition ImpModel : @Model ImpSignature :=
    mkModel_singleton
      (Ksorts_rect _ _ _ bool Z)
      (Ksyms_rect _ true
                    false
                    negb
                    andb
                    andb
                    xorb
                    orb
                    orb
                    implb
                    eqb
                    neqbB
                    id
                    2
                    0
                    1
                    0 (* unsure about this *)
                    Z.rem
                    Z.land (* unsure about this *)
                    Z.mul
                    Z.add
                    Z.sub
                    Z.quot
                    Z.shiftl
                    Z.leb
                    Z.ltb
                    neqbZ
                    Z.eqb
                    Z.geb
                    Z.shiftr
                    Z.gtb
                    modPow (* powmod *)
                    Z.pow (* pow *)
                    ediv (* div *)
                    divides (* divides *)
                    emod (* mod *)
                    Z.lxor (* xor *)
                    Z.lor (* or *)
                    Z.abs (* abs *)
                    bitRange (* bitRange *)
                    (id : Z -> Z) (* fresh *)
                    Z.log2 (* log2 *)
                    Z.max
                    Z.min
                    _ (* rand - how should we model random generation? I could not find the corresponding implementation! *)
                    signExtendBitRange (* signExtendBitRangeInt *)
                    Z.lnot) (* not *)
      ltac:(intros []; auto with typeclass_instances)
      _. (* Inhabited proof *)
  Final Obligation.
    simpl. intros x y z. exact (x + y + z).
  Defined.

  Goal satT Kint_theory_functional ImpModel.
  Proof.
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst; simpl.
    all: solve_functional_axiom.
  Qed.

  Goal satT Kbool_theory_functional ImpModel.
  Proof.
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst; simpl.
    all: solve_functional_axiom.
  Qed.

  Goal satT Kbool_theory_behavioural ImpModel.
  Proof.
    (* unfold sat defs *)
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst.

    all:
      simplify_krule;
      repeat destruct_evar_val;
      try timeout 1 set_solver.
  Qed.

(*   Definition nary_comp {R T : Type} {M} {l : list sort}
    (g : R -> T)
    (f : foldr (λ c a, M c -> a) R l) :
      hlist M l -> T.
  Proof.
    revert f g.
    induction l; intros.
    * simpl in *. exact (g f).
    * simpl in *.
      dependent destruction X.
      apply f in m.
      apply IHl; assumption.
  Defined.

  Lemma functional_symbol_is_functional :
    forall (σ : symbol) (R : sort) (vars : hlist evar (arg_sorts σ)),
      forall (M : Model),
        (exists (f : foldr (λ c a, M c -> a) (M (ret_sort σ)) (arg_sorts σ)), app M σ = nary_comp singleton f) ->
        satM (functional_symbol σ R vars) M.
  Proof.
    intros.
    apply functional_symbol_is_functional.
    destruct H. rewrite H.
    exists (uncurry_n x).
    
  Admitted.

  Ltac solve_functional_axiom :=
  match goal with
  | [ |- @eval _ ?M _ _ _ ?ρ (kore_exists _
                  (kore_equals ?s (kore_app ?σ ?l)
                               (kore_bevar In_nil))) = ⊤]
                               (* ^- NOTE: this is a restriction on db index 0!!! This pattern checks whether the axiom is a functional axiom *) =>
    let H := fresh "H" in
    epose proof (functional_symbol_is_functional σ s (hmap (fun s p =>
      match p with
      | kore_fevar x => x
      | _ => "_"
      end) l) M);
    apply H;
    eexists;
    reflexivity
  end. *)

  Goal satT Kint_theory_behavioural ImpModel.
  Proof.
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst.

    (* 7 axioms are automatically proved by Coq's lia tactic *)
    1-4, 9-11: simplify_krule; try set_solver by lia.
    (* However, lia is not capable of handling bit operations and
       division, therefore the following proofs are challenginf: *)
    * simplify_krule.
      repeat abstract_var. clear.
      repeat rewrite negb_true_iff.
      repeat rewrite Z.eqb_neq.
      apply Classical_Prop.imply_to_or. intros.
      destruct_and?; subst. lia.
    * simplify_krule.
      repeat abstract_var.
      apply Classical_Prop.imply_to_or. intros [].
      subst. rewrite H0. rewrite H. reflexivity.
    * simplify_krule.
      repeat abstract_var.
      repeat rewrite negb_true_iff.
      repeat rewrite Z.eqb_neq.
      apply Classical_Prop.imply_to_or. intros.
      clear -H.
      repeat rewrite -> Z.rem_abs_r by assumption.
      Search (Z.rem (_ + _) _).
      Search Z.rem Z.abs.
      Search Z.rem Z.mul.
      Search (Z.rem _ _ + _).
      repeat rewrite -> Z.rem_mod by assumption.
      destruct Z.sgn eqn:P; cbn.
      - rewrite Z.mul_0_l. simpl.
        rewrite Z.add_0_l.
        rewrite Z.abs_idemp. rewrite Z_mod_same_full. lia.
      - admit.
      - admit.
    * simplify_krule.
      repeat abstract_var.
      repeat rewrite negb_true_iff.
      repeat rewrite Z.eqb_neq.
      apply Classical_Prop.imply_to_or. intros.
      destruct_and?. rewrite H H2 H1.
      simpl in *. clear.
      admit.
    * simplify_krule.
      repeat abstract_var.
      repeat rewrite negb_true_iff.
      repeat rewrite Z.eqb_neq.
      apply Classical_Prop.imply_to_or. intros.
      destruct_and?. rewrite H H1 H2. clear.
      destruct (decide (var4 = 0)).
      - subst. admit.
      - admit.
  Admitted.


(*   Goal satT Kbool_theory_functional ImpModel.
  Proof.
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst; simpl.
    
    * epose proof (functional_symbol_is_functional KandBool x
        (hmap (fun s p =>
      match p with
      | kore_fevar x => x
      | _ => "_"
      end) ⟨ kore_fevar "K0"; kore_fevar "K1" ⟩) ImpModel).
      Opaque uncurry_n.
      simpl in H.
      (* cbn in H. *)
      apply H. clear H.
      
      simpl app.
      eexists.
      simpl.
      repeat apply functional_extensionality. reflexivity.
    
    all: solve_functional_axiom.
(*     * simpl.
      Check @eval.
      Check hmap.
      match goal with
      | [ |- @eval _ ?M _ _ _ ?ρ (kore_exists _
                      (kore_equals ?s (kore_app ?σ ?l)
                                   (kore_bevar In_nil))) = ⊤] (* <- NOTE: this is a restriction on db index 0!!! *) =>
        let H := fresh "H" in
        epose proof (functional_symbol_is_functional σ s (hmap (fun s p =>
          match p with
          | kore_fevar x => x
          | _ => "_"
          end) l) M);
        apply H;
        eexists;
        reflexivity
      end.
    
      pose proof (functional_symbol_is_functional KandBool x (hcons "K0" (hcons "K1" hnil)) ImpModel). (* just apply does not work for some reason *)
      apply H.
      simpl. eexists. reflexivity. *)
  Qed. *)

  Goal satT Ktheory_behavioural ImpModel.
  Proof.
  
  Qed.

  Goal satT KList_theory_functional ImpModel.
  Proof.
  
  Qed.

  Goal satT KList_theory_behavioural ImpModel.
  Proof.
  
  Qed.

End BoolSemantics.

