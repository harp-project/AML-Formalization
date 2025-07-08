From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.

From Coq Require Import ZArith.
From stdpp Require Import bitvector.

Open Scope kore_scope.
Open Scope hlist_scope.
Open Scope string_scope.

(**
   This is copied from the other file.
 *)
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
  repeat ;
  simpl sort_inj;
  repeat (rewrite_app_ext; try rewrite fmap_propset_singleton);
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

Module MInt.

  Import bitvector.

  Definition MInt (n : nat) : Set := bv (N.of_nat n).

  Definition neg {n : nat} : MInt n -> MInt n := bv_opp.

  Definition natvalue {n : nat} (x : MInt n) : nat := Z.to_nat (bv_unsigned x).

  Definition natural {n : nat} (x : nat) : MInt n := Z_to_bv (N.of_nat n) (Z.of_nat x).

  Definition uvalue {n : nat} : MInt n -> Z := bv_unsigned.
  Definition svalue {n : nat} : MInt n -> Z := bv_signed.

  Goal let x : MInt 3 := 7%bv in uvalue x = 7%Z /\ svalue x = (-1)%Z.
  Proof. auto. Qed.

  (**
     I'm not sure how exactly the hooked version of this works. Z_to_bv
     wraps its argument.
   *)
  Definition integer {n : nat} : Z -> MInt n := Z_to_bv (N.of_nat n).

  Instance bv_wf_zero (n : N) : BvWf n 0.
  Proof.
    apply bv_wf_in_range. split.
    apply Z.le_refl. apply bv_modulus_pos.
  Defined.

  (**
     Find more operations in this module.
   *)
  (* Search _ in definitions. *)
End MInt.

Module T.

  Import CRelationClasses.

  Inductive Sorts : Set :=
    | SortNat
    | SortBool
    | SortInt
    | SortString
    | SortMInt (n : nat)
  .

  (**
     I made this tactic to try to make EqDecision faster and it seems to
     work, but I've seen times vary wildly, so please check this against
     the large examples.
   *)
  Lemma eqdec_fequal {A B : Type} {_ : EqDecision A} (f : A -> B) (x y : A) : (forall x y, f x = f y -> x = y) -> {f x = f y} + {f x ≠ f y}.
  Proof.
    intro.
    destruct (decide (x = y)) as [-> |].
    left. reflexivity.
    right. intro. apply n, H, H0.
  Defined.

  Tactic Notation "solve_decision_with_match" :=
    unfold EqDecision, Decision; intros [] [];
    match goal with
    | [ |- context[?x = ?x] ] => left; reflexivity
    | [ |- context[?f ?x = ?f ?y] ] => apply (eqdec_fequal f x y); inversion 1; reflexivity
    | _ => right; discriminate
    end.

  Instance Sorts_eqdecision : EqDecision Sorts.
  Proof.
    time solve_decision.
    Restart.
    time solve_decision_with_match.
  Defined.

  Inductive Subsort : crelation Sorts := .

  Inductive SortNat_carrier : Set :=
    c_nat (n : nat)
  with SortBool_carrier : Set :=
    c_bool (b : bool)
  with SortInt_carrier : Set :=
    c_int (z : Z)
  with SortString_carrier : Set :=
    c_str (s : string)
  with SortMInt_carrier : nat -> Set :=
    c_mint (n : nat) (x : MInt.MInt n) : SortMInt_carrier n
  .

  Definition carrier (s : Sorts) : Set :=
    match s with
    | SortNat    => SortNat_carrier
    | SortBool   => SortBool_carrier
    | SortInt    => SortInt_carrier
    | SortString => SortString_carrier
    | SortMInt n => SortMInt_carrier n
    end.

  Instance carrier_inhabited : forall s, Inhabited (carrier s).
  Proof.
    intros []; repeat unshelve econstructor.
    apply MInt.bv_wf_zero.
  Defined.

  Inductive Symbols : Set :=
    | SymZero
    | SymSucc
    | SymPlus
    | SymFalse
    | SymTrue
    | SymMIntToSigned (n : nat)
    | SymMIntToUnsigned (n : nat)
    | SymIntToMInt (n : nat)
  .

  Program Instance Sig : Signature := {|
    sorts := {| sort := Sorts; subsort := Subsort |};
    variables := StringVariables;
    symbols := {|
      symbol := Symbols;
      arg_sorts := λ x, match x with
                         | SymZero  => []
                         | SymSucc  => [SortNat]
                         | SymPlus  => [SortNat; SortNat]
                         | SymFalse => []
                         | SymTrue  => []
                         | SymMIntToSigned n => [SortMInt n]
                         | SymMIntToUnsigned n => [SortMInt n]
                         | SymIntToMInt n => [SortInt]
                         end;
      ret_sort := λ x, match x with
                       | SymZero  => SortNat
                       | SymSucc  => SortNat
                       | SymPlus  => SortNat
                       | SymFalse => SortBool
                       | SymTrue  => SortBool
                       | SymMIntToSigned n => SortInt
                       | SymMIntToUnsigned n => SortInt
                       | SymIntToMInt n => SortMInt n
                       end;
    |}
  |}.

  (**
     Some notes about parsers:
     - I use a lot of primitives (eg. let fix in), hopefully these are fast
       and easy to unfold
     - I repeat code, this way the parsers are independent, and we don't
       need to mess with wrapping and unwrapping options
     - There are sections, because to use the "-" notation for
       *characters*, I need char_scope, which is only available if the Ascii
       module is imported, but I don't want to import it at the top level,
       because I'm afraid of name collsions (eg. with eqb).
     - As before, there are minimal checks, see below how "kapa" is a valid
       MInt of width 49
   *)

  Definition SortBool_parser (str : string) : option (carrier SortBool) :=
    match str with
    | "false" => Some (c_bool false)
    | "true"  => Some (c_bool true)
    | _       => None
    end.

  (**
     This is a very hacky ascii-based parser. There is zero validation
     here, it will happily parse any string as a number. But it does work
     for actual numbers. Which funnily enough probably means that this is
     as good of a parser as we'll ever need for generated models.
   *)
  Definition SortNat_parser (str : string) : option (carrier SortNat) := let fix F n s := if s is String x xs then F (10 * n + Ascii.nat_of_ascii x - 48) xs else n in Some (c_nat (F 0 str)).

  Compute SortNat_parser "7".
  Compute SortNat_parser "123".
  Compute SortNat_parser "".
  Compute SortNat_parser "{@}".

  Section charscope.
    Import Ascii.
    Open Scope char_scope.

    Definition SortInt_parser (str : string) : option (carrier SortInt) := let fix F n s := if s is String x xs then F (10 * n + nat_of_ascii x - 48) xs else n in
      match str with
      | String "-" xs => Some (c_int (Z.opp (Z.of_nat (F 0 xs))))
      | String "+" xs => Some (c_int (Z.of_nat (F 0 xs)))
      | _ => Some (c_int (Z.of_nat (F 0 str)))
      end.
  End charscope.

  Definition SortString_parser (str : string) : option (carrier SortString) := Some (c_str str).

  Section charscope.
    Import Ascii.
    Open Scope char_scope.

    Definition SortMInt_parser (m : nat) (str : string) : option (carrier (SortMInt m)) :=
      let fix G n s := if s is String x xs then G (10 * n + nat_of_ascii x - 48) xs else n in
      let fix F f n s :=
        match s with
        | String "p" xs => if Nat.eqb (G 0 xs) m then Some (c_mint m (MInt.integer (f (Z.of_nat n)))) else None
        (**
          Use this for no width check. G may be removed too in this case.
        *)
        (* | String "p" xs => Some (c_mint m (MInt.integer (f (Z.of_nat n)))) *)
        | String x xs => F f (10 * n + nat_of_ascii x - 48) xs
        | _ => None
        end
      in match str with
         | String "-" xs => F Z.opp 0 xs
         | String "+" xs => F id 0 xs
         | _ => F id 0 str
         end.
  End charscope.

  Compute SortMInt_parser 3 "7p3". (* 7 *)
  Compute SortMInt_parser 3 "7p4". (* None *)
  Compute SortMInt_parser 3 "8p3". (* 0 *)
  Compute SortMInt_parser 3 "-1p3". (* 7 *)
  Compute SortMInt_parser 49 "kapa". (* 639 *)
  
  Definition parser (s : sort) : string -> option (carrier s) :=
    match s with
    | SortNat  => SortNat_parser
    | SortBool => SortBool_parser
    | SortInt => SortInt_parser
    | SortString => SortString_parser
    | SortMInt n => SortMInt_parser n
    end.

  Definition Mod : @Model Sig := mkModel_singleton
    carrier
    (λ x, match x with
           | SymZero  => c_nat 0
           | SymSucc  => λ '(c_nat n), c_nat (S n)
           | SymPlus  => λ '(c_nat n) '(c_nat m), c_nat (n + m)
           | SymFalse => c_bool false
           | SymTrue  => c_bool true
           | SymMIntToSigned _ => fun '(c_mint _ x) => c_int (MInt.svalue x)
           | SymMIntToUnsigned _ => fun '(c_mint _ x) => c_int (MInt.uvalue x)
           | SymIntToMInt n => fun '(c_int m) => c_mint n (MInt.integer m)
           end
    )
    _
    (λ s s' H, match H with end)
    parser.

  Definition test : @Theory Sig := PropSet (λ pat,
  (* dv SortBool "false" \/ dv SortBool "true" *)
  pat = existT SortBool (kore_or (kore_dv SortBool "false") (kore_dv SortBool "true")) \/
  (* dv SortNat "123" + dv SortNat "456" = dv SortNat "579" *)
  (exists R, pat = existT R (SymPlus ⋅ ⟨ kore_dv SortNat "123" ; kore_dv SortNat "456" ⟩ =k{R} kore_dv SortNat "579")) \/
  (* MInt2Unsigned (dv (SortMInt 3) "-1p3") = dv SortInt "7" *)
  (exists R, pat = existT R (SymMIntToUnsigned 3 ⋅ ⟨ kore_dv (SortMInt 3) "-1p3" ⟩ =k{R} kore_dv SortInt "7")) \/
  (* MInt2Signed (dv (SortMInt 3) "7p3") = dv SortInt "-1" *)
  (exists R, pat = existT R (SymMIntToSigned 3 ⋅ ⟨ kore_dv (SortMInt 3) "7p3" ⟩ =k{R} kore_dv SortInt "-1"))
  ).

  Goal satT test Mod.
  Proof.
    unfold satT, satM, test. intros.
    (* Generate a goal for each axiom: *)
    unfold_elem_of; destruct_or?; destruct_ex?; subst; cbn.
    - simplify_krule.
      destruct t, b; auto.
    - by simplify_krule.
    - by simplify_krule.
    - by simplify_krule.
  Qed.

End T.
