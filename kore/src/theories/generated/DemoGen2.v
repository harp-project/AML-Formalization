

From MatchingLogic Require Export stdpp_ext.
From Kore Require Export Semantics.
Import Signature.StringVariables.
Import Kore.Syntax.Notations.
Import Btauto.

From Coq Require Import ZArith.

Open Scope kore_scope.
Open Scope string_scope.
Open Scope hlist_scope.

      Module TheorySyntax.


Inductive Ksorts :=
  | SortS1
| SortS3
| SortE
| SortS2
.
      Instance Ksorts_eq_dec : EqDecision Ksorts.
      Proof. solve_decision. Defined.
      Program Instance Ksorts_countable : finite.Finite Ksorts :=
      {
        enum := [SortS1; SortS3; SortE; SortS2]
      }.
      Next Obligation.
        compute_done.
      Defined.
      Final Obligation.
        intros. destruct x; set_solver.
      Defined.



Inductive Ksyms :=
  | syme1
| syme2
| syme3
| symf
| symg
| syms2
| syms3
.
      Instance Ksyms_eq_dec : EqDecision Ksyms.
      Proof. solve_decision. Defined.
      Program Instance Ksyms_countable : finite.Finite Ksyms :=
      {
        enum := [syme1; syme2; syme3; symf; symg; syms2; syms3]
      }.
      Next Obligation.
        compute_done.
      Defined.
      Final Obligation.
        intros. destruct x; set_solver.
      Defined.

        Inductive KSubsort : CRelationClasses.crelation Ksorts :=
|  inj_SortS3_SortS1 : KSubsort SortS3 SortS1
|  inj_SortS2_SortS1 : KSubsort SortS2 SortS1
|  inj_SortS3_SortS2 : KSubsort SortS3 SortS2
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
                | syme1 => []
  | syme2 => []
  | syme3 => []
  | symf => [SortS1]
  | symg => [SortS1]
  | syms2 => []
  | syms3 => []
      end;
    ret_sort σ :=
      match σ with
                | syme1 => SortE
  | syme2 => SortE
  | syme3 => SortE
  | symf => SortE
  | symg => SortE
  | syms2 => SortS2
  | syms3 => SortS3
      end;
  |};
|}.

Definition Theory_behavioural : @Theory TheorySignature :=
  PropSet (fun pat =>

(* symf *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortS1 "X0" ) ⊆k{R} ( @kore_fevar _ _ _ SortS1 "Var'Unds'Gen0" ) ) and ( Top{R} ) ) ) --->ₖ ( ( symf ⋅ ⟨@kore_fevar _ _ _ SortS1 "X0"⟩ ) =k{R} ( ( syme1 ⋅ ⟨⟩ ) and ( Top{SortE} ) ) ) )) \/

(* symf *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortS1 "X0" ) ⊆k{R} ( kore_inj _ inj_SortS2_SortS1 (@kore_fevar _ _ _ SortS2 "Var'Unds'Gen0") ) ) and ( Top{R} ) ) ) --->ₖ ( ( symf ⋅ ⟨@kore_fevar _ _ _ SortS1 "X0"⟩ ) =k{R} ( ( syme1 ⋅ ⟨⟩ ) and ( Top{SortE} ) ) ) )) \/

(* symf *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortS1 "X0" ) ⊆k{R} ( kore_inj _ inj_SortS3_SortS1 (@kore_fevar _ _ _ SortS3 "Var'Unds'Gen0") ) ) and ( Top{R} ) ) ) --->ₖ ( ( symf ⋅ ⟨@kore_fevar _ _ _ SortS1 "X0"⟩ ) =k{R} ( ( syme1 ⋅ ⟨⟩ ) and ( Top{SortE} ) ) ) )) \/

(* symg *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortS1 "X0" ) ⊆k{R} ( kore_inj _ inj_SortS3_SortS1 (syms3 ⋅ ⟨⟩) ) ) and ( Top{R} ) ) ) --->ₖ ( ( symg ⋅ ⟨@kore_fevar _ _ _ SortS1 "X0"⟩ ) =k{R} ( ( syme1 ⋅ ⟨⟩ ) and ( Top{SortE} ) ) ) )) \/

(* symg *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortS1 "X0" ) ⊆k{R} ( kore_inj _ inj_SortS3_SortS1 (syms3 ⋅ ⟨⟩) ) ) and ( Top{R} ) ) ) --->ₖ ( ( symg ⋅ ⟨@kore_fevar _ _ _ SortS1 "X0"⟩ ) =k{R} ( ( syme1 ⋅ ⟨⟩ ) and ( Top{SortE} ) ) ) )) \/

(* symg *)
(exists R, pat = existT R (( ( Top{R} ) and ( ( ( @kore_fevar _ _ _ SortS1 "X0" ) ⊆k{R} ( kore_inj _ inj_SortS3_SortS1 (syms3 ⋅ ⟨⟩) ) ) and ( Top{R} ) ) ) --->ₖ ( ( symg ⋅ ⟨@kore_fevar _ _ _ SortS1 "X0"⟩ ) =k{R} ( ( syme1 ⋅ ⟨⟩ ) and ( Top{SortE} ) ) ) ))
  ).

Definition Theory_functional : @Theory TheorySignature :=
  PropSet (fun pat =>

(* syme1 is functional *)
(exists R, pat = existT R (kore_exists SortE (( kore_bevar (In_nil) ) =k{R} ( syme1 ⋅ ⟨⟩ )) )) \/

(* syme2 is functional *)
(exists R, pat = existT R (kore_exists SortE (( kore_bevar (In_nil) ) =k{R} ( syme2 ⋅ ⟨⟩ )) )) \/

(* syme3 is functional *)
(exists R, pat = existT R (kore_exists SortE (( kore_bevar (In_nil) ) =k{R} ( syme3 ⋅ ⟨⟩ )) )) \/

(* syms2 is functional *)
(exists R, pat = existT R (kore_exists SortS2 (( kore_bevar (In_nil) ) =k{R} ( syms2 ⋅ ⟨⟩ )) )) \/

(* syms3 is functional *)
(exists R, pat = existT R (kore_exists SortS3 (( kore_bevar (In_nil) ) =k{R} ( syms3 ⋅ ⟨⟩ )) ))
  ).

      End TheorySyntax.
      Module TheorySemantics.
        Import TheorySyntax.

      Inductive SortS1_carrier : Set :=
 | c_inj_SortS2_SortS1 (b : SortS2_carrier)
 | c_inj_SortS3_SortS1 (b : SortS3_carrier)
with SortS3_carrier : Set :=
 | c_syms3
with SortE_carrier : Set :=
 | c_syme1
 | c_syme2
 | c_syme3
with SortS2_carrier : Set :=
 | c_syms2
 | c_inj_SortS3_SortS2 (b : SortS3_carrier)
.

      Definition carrier (s : Ksorts) : Set := match s with
      SortS1 => SortS1_carrier
|SortS3 => SortS3_carrier
|SortE => SortE_carrier
|SortS2 => SortS2_carrier
      end.


Definition retr_SortS1_SortS3 x := match x with
  | c_inj_SortS3_SortS1 x => Some x
  | _ => None
end.

Definition retr_SortS1_SortS2 x := match x with
  | c_inj_SortS3_SortS1 x => Some (c_inj_SortS3_SortS2 x)
  | c_inj_SortS2_SortS1 x => Some x
end.

Definition retr_SortS2_SortS3 x := match x with
  | c_inj_SortS3_SortS2 x => Some x
  | _ => None
end.

      Definition _0b14131 : SortS1_carrier -> option SortE_carrier
  := fun x => match x with | c_inj_SortS3_SortS1 c_syms3 => Some c_syme1
  | _ => None end.
Definition _b468026 : SortS1_carrier -> option SortE_carrier
  := fun x => match x with | c_inj_SortS3_SortS1 c_syms3 => Some c_syme1
  | _ => None end.
Definition _c0bcf68 : SortS1_carrier -> option SortE_carrier
  := fun x => match x with | c_inj_SortS3_SortS1 c_syms3 => Some c_syme1
  | _ => None end.
Definition _8ab4f38 : SortS1_carrier -> option SortE_carrier
  := fun x => match x with | _Gen0 => Some c_syme1 end.
Definition _59f3cb7 : SortS1_carrier -> option SortE_carrier
  := fun x => match x with | c_inj_SortS3_SortS1 _Gen0 => Some c_syme1
  | _ => None end.
Definition _4db77ad : SortS1_carrier -> option SortE_carrier
  := fun x => match x with | _Pat0 => match (retr_SortS1_SortS2) _Pat0 with
    | Some _Gen0 => Some c_syme1
    | _ => None end end.
Definition symg (x0 : SortS1_carrier) : option SortE_carrier := (_0b14131 x0) <|> (_b468026 x0) <|> (_c0bcf68 x0).
Definition symf (x0 : SortS1_carrier) : option SortE_carrier := (_4db77ad x0) <|> (_59f3cb7 x0) <|> (_8ab4f38 x0).
      Program Definition Model : @Model TheorySignature :=
        mkModel_partial
          (Ksorts_rect _ SortS1_carrier SortS3_carrier SortE_carrier SortS2_carrier)
          (Ksyms_rect _ (Some c_syme1) (Some c_syme2) (Some c_syme3) symf symg (Some c_syms2) (Some c_syms3))
          _ _ (λ _ _, None).
      Next Obligation.
        destruct s; repeat constructor.
      Defined.
      Final Obligation.
        intros s1 s2 H x; inversion H; subst.
      * exact (c_inj_SortS3_SortS1 x).
* exact (c_inj_SortS2_SortS1 x).
* exact (c_inj_SortS3_SortS2 x).
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

Ltac classicize :=
  apply Classical_Prop.imply_to_or.
  Ltac app_ext_rewrite C :=
  lazymatch C with
  | context [propset_fa_union ?Cnew] =>
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

  Ltac find_contra :=
  match goal with
  | [H : ¬ ∃ _, _ |- _] =>
    exfalso;
    apply H;
    repeat eexists;
    reflexivity
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
    try reflexivity;
    try congruence;
    try btauto;
    try tauto;
    try lia;
    try find_contra.

  Ltac destruct_solver :=
    simpl in *;
    classicize;
    intros;
    destruct_and?;
    rewrite_evar_val;
    cbn in *;
    simplify_eq;
    unfold mbind, option_bind, mret, option_ret in *;
    simpl;
    repeat case_match;
    destruct_oapps;
    cbn in *;
    simplify_eq;
    repeat (rewrite_app_ext; repeat rewrite fmap_propset_singleton);
    repeat app_ext_empty;
    bool_to_prop;
    try lia;
    try set_solver;
    repeat destruct_evar_val_hyp;
    cbn in *;
    unfold mbind, option_bind, mret, option_ret in *;
    repeat case_match;
    simplify_eq;
    bool_to_prop;
    try lia;
    try set_solver.

  Ltac simplify_premise :=
    destruct_oapp_hyp; [
       repeat rewrite_app_ext_in_single;
       simpl in *
     | try app_ext_empty_hyp
  ].

  Ltac smart_solver :=
    simpl in *;
    classicize;
    intros;
    destruct_and?;
    rewrite_evar_val;
    repeat simplify_premise;
    simplify_eq;
    cbn in *;
    bool_to_prop;
    destruct_and?;
    (* TODO: this is very fragile: *)
    match goal with
    | |- oapp singleton ∅ (?sym _) = _ => unfold sym
    end;
    (**)
    repeat (rewrite_in_goal; simpl);
    cbn in *; simplify_eq;
    simpl;
    repeat destruct_evar_val;
    repeat (rewrite_in_goal; simpl);
    cbn in *; simplify_eq;
    repeat (rewrite_in_goal; simpl);
    repeat (destruct_Z_compares; cbn);
    repeat (rewrite_in_goal; simpl);
    repeat rewrite simpl_none_bind;
    repeat rewrite simpl_none_orelse;
    unfold mbind, option_bind;
    try case_match; try reflexivity;
    repeat match goal with
    | [H : _ && _ = false |- _] =>
      apply andb_false_iff in H as [|]
    end;
    all_to_prop;
    try lia.


  Ltac solver_macro :=
    simplify_krule;
    ((by smart_solver) ||
     (by simplification_solver) ||
     (by timeout 1000 destruct_solver)).


  Goal satT Theory_behavioural Model.
  Proof.
    unfold satT, satM. intros.
    unfold Theory_behavioural in H.
    unfold_elem_of; destruct_or?; destruct_ex?; subst.
    * solver_macro.
    * solver_macro.
    * solver_macro.
    * simplify_krule.
      destruct_evar_val.
      - simpl. left.
        intro.
        apply singleton_subseteq_l in H.
        destruct H. destruct H. inversion H.
      - right. by destruct b.
    * simplify_krule.
      destruct_evar_val.
      - simpl. left.
        intro.
        apply singleton_subseteq_l in H.
        destruct H. destruct H. inversion H.
      - right. by destruct b.
    * simplify_krule.
      destruct_evar_val.
      - simpl. left.
        intro.
        apply singleton_subseteq_l in H.
        destruct H. destruct H. inversion H.
      - right. by destruct b.
  Defined.

      End TheorySemantics.

