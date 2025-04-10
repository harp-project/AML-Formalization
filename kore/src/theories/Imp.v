(* From Equations Require Import Equations. *)
From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.

Open Scope kore_scope.


Module ImpSyntax.

  Inductive Ksorts :=
  | Kbool
  | Kint.


  Instance Ksorts_eq_dec : EqDecision Ksorts.
  Proof. solve_decision. Defined.


  Program Instance Ksorts_finite : finite.Finite Ksorts := {
    enum := [Kbool; Kint];
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
    (* Lbl'Tild'Int'Unds'{}(SortInt{}) : SortInt{} *).

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
  ; KnotIntl];
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
        end;
    |};
  |}.

  Open Scope hlist_scope.
  Open Scope string_scope.

(*
grep -Eo "\\\\dv{[^}]*}[^\(]*\([^\)]*\)" /tmp/definition.kore > /tmp/matches

dv is only used with the following parameters:
\dv{SortBool{}}("true")
\dv{SortBool{}}("false")
\dv{SortInt{}}("n") (n is a number)
\dv{SortString{}}("s") (s is a string)
\dv{SortKConfigVar{}}("$PGM")

  axiom{R} \implies{R} (
    \and{R}(
      \top{R}(),
      \and{R} (
          \in{SortBool{}, R} (
            X0:SortBool{},
            \dv{SortBool{}}("false")
          ),
          \top{R} ()
        )),
    \equals{SortBool{},R} (
      LblnotBool'Unds'{}(X0:SortBool{}),
     \and{SortBool{}} (
       \dv{SortBool{}}("true"),
        \top{SortBool{}}())))

  axiom{R} \implies{R} (
    \and{R}(
      \top{R}(),
      \and{R} (
          \in{SortBool{}, R} (
            X0:SortBool{},
            \dv{SortBool{}}("true")
          ),
          \top{R} ()
        )),
    \equals{SortBool{},R} (
      LblnotBool'Unds'{}(X0:SortBool{}),
     \and{SortBool{}} (
       \dv{SortBool{}}("false"),
        \top{SortBool{}}())))

  axiom{R} \implies{R} (
    \and{R}(
      \top{R}(),
      \and{R} (
          \in{SortBool{}, R} (
            X0:SortBool{},
            \and{SortBool{}}(\dv{SortBool{}}("false"),Var'Unds'Gen1:SortBool{})
          ),\and{R} (
          \in{SortBool{}, R} (
            X1:SortBool{},
            Var'Unds'Gen0:SortBool{}
          ),
          \top{R} ()
        ))),
    \equals{SortBool{},R} (
      Lbl'Unds'andBool'Unds'{}(X0:SortBool{},X1:SortBool{}),
     \and{SortBool{}} (
       Var'Unds'Gen1:SortBool{},
        \top{SortBool{}}())))
 *)

  Definition Kbool_theory_behavioural : @Theory ImpSignature :=
    PropSet (fun pat =>
      (** negation: *)
      (* not false = true *)
      (exists R, pat =                              (* v-- this should be dv *)
        existT R ((Top{R} and kore_fevar "X" ⊆k{R} Kfalse ⋅ ⟨⟩)
          --->                               (* v-- this should be dv *)
         (KnotBool ⋅ ⟨kore_fevar "X"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool})))
      ) \/
      (* not true = false *)
      (exists R, pat =
        existT R ((Top{R} and kore_fevar "X" ⊆k{R} Ktrue ⋅ ⟨⟩)
          --->
        (KnotBool ⋅ ⟨kore_fevar "X"⟩ =k{R} (Kfalse ⋅ ⟨⟩ and Top{Kbool})))
      ) \/
      (** conjunction *)
      (* rule `_andBool_`(#token("false","Bool") #as _Gen1,_Gen0)=>_Gen1 *)
      (exists R, pat =
        existT R ((Top{R} and
                   kore_fevar "X0" ⊆k{R} (Kfalse ⋅ ⟨⟩ and kore_fevar "Gen1") and
                   @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and
                   Top{R})
          --->
        (KandBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "Gen1" and Top{Kbool})))
      ) \/
      ((* rule `_andBool_`(B,#token("true","Bool"))=>B *)
        exists R, pat =
          existT R (
            Top{R} --->
            KandBool ⋅ ⟨kore_fevar "B"; Ktrue ⋅ ⟨⟩ ⟩ =k{R} (kore_fevar "B" and Top{Kbool})
          )
      ) \/
      ( (* rule `_andBool_`(_Gen0,#token("false","Bool"))=>#token("false","Bool") *)
        exists R, pat =
          existT R (
            Top{R} --->
            KandBool ⋅ ⟨kore_fevar "Gen0"; Kfalse ⋅ ⟨⟩ ⟩ =k{R} (Kfalse ⋅ ⟨ ⟩ and Top{Kbool})
        )
      ) \/
      ( (* rule `_andBool_`(#token("true","Bool"),B)=>B *)
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
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
            --->
            (KandThenBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "Gen1" and Top{Kbool}))
          )
      ) \/
      (*rule `_andThenBool_`(K,#token("true","Bool"))=>K*)
      (
        exists R, pat =
          existT R (
            Top{R} --->
            KandThenBool ⋅ ⟨kore_fevar "K"; Ktrue ⋅ ⟨⟩ ⟩ =k{R} (kore_fevar "K" and Top{Kbool})
          )
      ) \/
      (*rule `_andThenBool_`(_Gen0,#token("false","Bool"))=>#token("false","Bool")*)
      (
        exists R, pat =
          existT R (
            Top{R} --->
            KandThenBool ⋅ ⟨kore_fevar "Gen0"; Kfalse ⋅ ⟨⟩ ⟩ =k{R} (Kfalse ⋅ ⟨ ⟩ and Top{Kbool})
        )
      ) \/
      (*rule `_andThenBool_`(#token("true","Bool"),K)=>K*)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "K" and Top{R}
            --->
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
            --->
            (KxorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Kfalse ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_xorBool_`(B,#token("false","Bool"))=>B *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KxorBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_xorBool_`(#token("false","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
            (KxorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (** orBool *)
      (* rule `_orBool_`(B,#token("false","Bool"))=>B *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(#token("false","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* rule `_orBool_`(#token("true","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (** orElseBool *)
      (* rule `_orElseBool_`(K,#token("false","Bool"))=>K *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "K"; Kfalse ⋅ ⟨⟩⟩ =k{R} (kore_fevar "K" and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(#token("false","Bool"),K)=>K *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "K" and Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "K" and Top{Kbool}))
          )
      ) \/
      (* rule `_orElseBool_`(#token("true","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->
            (KorBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (** impliesBool *)
      (* `_impliesBool_`(B,#token("false","Bool"))=>`notBool_`(B) *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KimpliesBool ⋅ ⟨kore_fevar "B"; Kfalse ⋅ ⟨⟩⟩ =k{R} (KnotBool ⋅ ⟨kore_fevar "B"⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(_Gen0,#token("true","Bool"))=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R}
            --->
            (KimpliesBool ⋅ ⟨kore_fevar "Gen0"; Ktrue ⋅ ⟨⟩⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(#token("false","Bool"),_Gen0)=>#token("true","Bool") *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Kfalse ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "Gen0" and Top{R}
            --->
            (KimpliesBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (Ktrue ⋅ ⟨⟩ and Top{Kbool}))
          )
      ) \/
      (* rule `_impliesBool_`(#token("true","Bool"),B)=>B *)
      (
        exists R, pat =
          existT R (
            Top{R} and kore_fevar "X0" ⊆k{R} Ktrue ⋅ ⟨⟩ and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B" and Top{R}
            --->
            (KimpliesBool ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "B" and Top{Kbool}))
          )
      ) \/
      (* NOTE: there are no other behavioural axioms about ==Bool and =/=Bool! *)
      ( (* rule `_=/=Bool_`(B1,B2)=>`notBool_`(`_==Bool_`(B1,B2)) *)
        exists R, pat =
          existT R (
            Top{R} and @kore_fevar _ _ _ Kbool "X0" ⊆k{R} kore_fevar "B1" and
            @kore_fevar _ _ _ Kbool "X1" ⊆k{R} kore_fevar "B2" and Top{R}
            --->
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
      - How should we model hooked symbols, which do not have any axioms (not even functional ones)?---in some cases (maybe in all) there is an smt-hook on these.
        These are: KtimeLParRPar_K_IO_Int, KtmodInt, KtdivInt, KltltInt, KgtgtInt, KpowmodInt, KpowInt, KdivInt, KdividesInt, KmodInt, KbitRangeInt, Klog2Int, KrandInt
      - What should we do with the attributes (e.g., total, functional, freshgenerator)?
      - There are axioms for minInt, but none for maxInt?
   *)
   Definition Kint_theory_behavioural : @Theory ImpSignature :=
    PropSet (fun pat =>
      (exists R, pat =
        existT R (Top{R} and Top{R} ---> Kstderr_K_IO_Int ⋅⟨⟩ =k{R} KintVal 2 ⋅ ⟨⟩)
      ) \/
      (exists R, pat =
        existT R (Top{R} and Top{R} ---> Kstdin_K_IO_Int ⋅⟨⟩ =k{R} KintVal 0 ⋅ ⟨⟩)
      ) \/
      (exists R, pat =
        existT R (Top{R} and Top{R} ---> Kstdin_K_IO_Int ⋅⟨⟩ =k{R} KintVal 1 ⋅ ⟨⟩)
      ) \/
      (exists R, pat =
        existT R (
          Top{R} and @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R}
          --->
          (KneqInt ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (KnotBool ⋅ ⟨KeqInt ⋅ ⟨kore_fevar "I1" ; kore_fevar "I2"⟩ ⟩ and Top{Kbool}))
        )
      ) \/
      (exists R, pat =
        existT R (
          KneqInt ⋅ ⟨kore_fevar "I2"; KintVal 0 ⋅ ⟨⟩ ⟩ =k{R} Ktrue ⋅ ⟨⟩ and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R} --->
          KdivInt ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (KtdivInt ⋅ ⟨KsubInt ⋅ ⟨kore_fevar "I1" ; KmodInt ⋅ ⟨kore_fevar "I1"; kore_fevar "I2"⟩ ⟩; kore_fevar "I2"⟩ and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          Top{R} and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R} --->
          KdividesInt ⋅ ⟨kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (KeqInt ⋅ ⟨KtmodInt ⋅ ⟨kore_fevar "I2" ; kore_fevar "I1" ⟩; KintVal 0 ⋅ ⟨⟩⟩ and Top{Kbool})
        )
      ) \/
      (exists R, pat =
        existT R (
          KneqInt ⋅ ⟨kore_fevar "I2"; KintVal 0 ⋅ ⟨⟩⟩ =k{R} Ktrue ⋅ ⟨⟩ --->
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
          @kore_fevar _ _ _ Kint "X2" ⊆k{R} kore_fevar "LEN" and Top{R} --->
          KbitRangeInt ⋅⟨ kore_fevar "X0"; kore_fevar "X1"; kore_fevar "X2"⟩ =k{R}
            (KmodInt ⋅ ⟨KgtgtInt ⋅ ⟨kore_fevar "I"; kore_fevar "IDX"⟩;
                        KltltInt ⋅ ⟨KintVal 1 ⋅ ⟨⟩; kore_fevar "LEN"⟩⟩ and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          Top{R} and @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I" and Top{R} --->
          KfreshInt ⋅ ⟨ kore_fevar "X0" ⟩ =k{R} (kore_fevar "I" and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          KltInt ⋅ ⟨kore_fevar "I1"; kore_fevar "I2"⟩ =k{R} Ktrue ⋅ ⟨⟩ and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R} --->
          KminInt⋅⟨ kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "I1" and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          KgeInt ⋅ ⟨kore_fevar "I1"; kore_fevar "I2"⟩ =k{R} Ktrue ⋅ ⟨⟩ and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I1" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "I2" and Top{R} --->
          KminInt⋅⟨ kore_fevar "X0"; kore_fevar "X1"⟩ =k{R} (kore_fevar "I2" and Top{Kint})
        )
      ) \/
      (exists R, pat =
        existT R (
          Top{R} and
          @kore_fevar _ _ _ Kint "X0" ⊆k{R} kore_fevar "I" and
          @kore_fevar _ _ _ Kint "X1" ⊆k{R} kore_fevar "IDX" and
          @kore_fevar _ _ _ Kint "X2" ⊆k{R} kore_fevar "LEN" and Top{R} --->
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
End ImpSyntax.

(* Tactic Notation "deconstruct_elem_of_Theory" :=
  repeat match goal with
  | [ H : _ ∈ ?Γ |- _ ] => destruct H
  end; (* clear; *) simpl. *)

(* Lemma propset_full_or_empty :
  forall (P : Prop),
    {[_ | P]} = ⊤ \/ {[_ | P]} = ⊥. *)

Module BoolSemantics.

  Import BoolSyntax.

  Definition neqb (b1 b2 : bool) : bool :=
    negb (eqb b1 b2).

  Definition BoolModel : @Model BoolSignature :=
    mkModel_singleton
      (Ksorts_rect _ bool)
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
                    neqb)
      ltac:(intros []; auto with typeclass_instances).

  Ltac unfold_elem_of :=
  match goal with
  | [H : _ ∈ _ |- _]  => destruct H
  end.

  Ltac destruct_evar_val :=
  match goal with
  | [ |- context [evar_valuation ?ρ ?x] ] =>
    let H := fresh "Val" in
      destruct (evar_valuation ρ x) eqn:H
  end.

  Ltac solve_dep_prods :=
    match goal with
    | [ |- ()] => exact tt
    | [ |- prod (sigT _) _] =>
      apply pair; [
        eapply existT; reflexivity
      |
        solve_dep_prods
      ]
    end.

  Ltac solve_all_singleton :=
  match goal with
  | [ |- all_singleton _] => cbn; solve_dep_prods
  end.

  (* For some reason, this tac does not work outside this file *)
  Ltac autorewrite_set :=
    repeat (
      rewrite intersection_top_l_L +
      rewrite intersection_top_r_L +
      rewrite union_empty_l_L +
      rewrite union_empty_r_L +
      rewrite propset_difference_neg
    ).

  (* This would be much more simple, if rewrite_stat innermost worked... *)
  Ltac rewrite_app_ext_innnermost G :=
  match G with
  | context [app_ext ?σ ?args] =>
    rewrite_app_ext_innnermost args (* This step is just to reach
                                        the innermost app_ext *)
    (* idtac "match" σ args *)
  | context [app_ext ?σ ?args] => (* This branch fails, if there is no
                                     more app_exts, therefore
                                     it succeeds for the last (innermost)
                                     app_ext *)
    (* idtac "last1" σ args; *)
    (* let H := fresh "H" in
    (* we explicitly rewrite: *)
    unshelve (epose proof (@app_ext_singleton _ BoolModel σ args ltac:(solve_all_singleton)) as H);
    (* idtac "last2" σ args; *)
    rewrite H; (* erewrite does not work here, for some reason *)
    clear H *)
    rewrite (@app_ext_singleton _ BoolModel σ args ltac:(solve_all_singleton))
  end.

  Ltac rewrite_app_ext :=
  match goal with
  | |- ?G => rewrite_app_ext_innnermost G; cbn
  end.

  Goal satT Kbool_theory_behavioural BoolModel.
  Proof.
    (* unfold sat defs *)
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst.

    all:
      simpl;
      eval_helper;
      autorewrite_set;
      repeat rewrite_app_ext;
      repeat destruct_evar_val;
      set_solver.
  Qed.

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
  end.

  Goal satT Kbool_theory_functional BoolModel.
  Proof.
    unfold satT, satM. intros.

    (* Generate a goal for each axiom: *)
    unfold Kbool_theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst; simpl.
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
    
      pose proof (functional_symbol_is_functional KandBool x (hcons "K0" (hcons "K1" hnil)) BoolModel). (* just apply does not work for some reason *)
      apply H.
      simpl. eexists. reflexivity. *)
  Qed.

End BoolSemantics.

