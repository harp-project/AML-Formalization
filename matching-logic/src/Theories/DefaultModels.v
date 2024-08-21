From Equations Require Import Equations.

From MatchingLogic Require Import Logic.
Import MatchingLogic.Logic.Notations.
From MatchingLogic.Utils Require Import Lattice stdpp_ext extralibrary.

From stdpp Require Import base propset countable.

Import extralibrary.

From MatchingLogic.Theories Require Import Definedness_Syntax
                                           Sorts_Syntax
                                           Bool_Syntax
                                           Definedness_Semantics
                                           Sorts_Semantics
                                           Bool_Semantics
                                           Nat_Syntax
.
Import Definedness_Syntax.Notations.
Import MatchingLogic.Semantics.Notations.

Set Default Proof Mode "Classic".

Open Scope ml_scope.
Open Scope list_scope.

(*
  Subtasks:
  - eval/app_ext automatic simplification

*)

Section Definedness.

  Context {Σ : Signature} {M : Model}
          {string_vars : variables = StringMLVariables}.


  (*
    Option 2: use only a single-symbol signature for definedness, which will be
    glued to other theories/specs
  *)
  Instance definedness_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols (@symbols (@ml_symbols Σ) + Definedness_Syntax.Symbols) _ _;
  }.
  Instance definedness_syntax : Definedness_Syntax.Syntax := {
     inj := inr;
  }.

  Definition definedness_carrier : Type := Domain M + unit.
  Definition definedness_sym_interp (m : @symbols (@ml_symbols Σ) + Definedness_Syntax.Symbols)
    : propset definedness_carrier :=
  match m with
  | inl x => inl <$> (sym_interp M x)
  | inr x => {[ inr () ]}
  end.

  Definition definedness_app_interp (m1 m2 : definedness_carrier)
    : propset definedness_carrier :=
  match m1 with
  | inr () => ⊤
  | inl x1 =>
     match m2 with
     | inl x2 => inl <$> app_interp M x1 x2
     | inr () => ∅
     end
  end.

  Definition DefinednessModel : Model := {|
    Domain := definedness_carrier;
    app_interp := definedness_app_interp;
    sym_interp := definedness_sym_interp;
  |}.

  Theorem DefinednessModel_satisfies_theory :
    DefinednessModel ⊨ᵀ Definedness_Syntax.theory.
  Proof.
    unfold Definedness_Syntax.theory. unfold Definedness_Syntax.named_axioms.
    unfold theory_of_NamedAxioms. simpl.
    unfold satisfies_theory. intros.
    rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
    cbn. unfold satisfies_model. intros.
    unfold patt_defined. unfold p_x, ev_x. simp eval.
    unfold sym_interp, app_ext. simpl.
    eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ DefinednessModel).
    apply set_equiv. intros. split; intros.
    * clear. set_solver.
    * rewrite elem_of_PropSet. exists (inr ()), (evar_valuation ρ (evar_fresh [])).
      set_solver.
  Qed.

End Definedness.

(* This is independent of ModelExtension.v, but it is very similar to it *)
Section Sorts.
  Context {Σ : Signature} {M : Model}
          {string_vars : variables = StringMLVariables}
          {sort_interp : Domain M -> propset M}.

  Instance sorts_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols (@symbols (@ml_symbols (definedness_Σ)) + Sorts_Syntax.Symbols) _ _;
  }.

  Instance sorts_syntax : @Sorts_Syntax.Syntax sorts_Σ := {
     inj := inr;
     imported_definedness := {|
        Definedness_Syntax.inj :=
          λ x : Definedness_Syntax.Symbols,
            match x with
            | definedness => inl (inr definedness)
            end
      |};
  }.

  Definition sorts_carrier : Type := Domain (@DefinednessModel Σ M) + unit.
  Definition sorts_sym_interp (m : @symbols (@ml_symbols (@definedness_Σ Σ)) + Sorts_Syntax.Symbols)
    : propset sorts_carrier :=
  match m with
  | inl x => inl <$> (sym_interp (@DefinednessModel Σ M) x)
  | inr x => {[ inr () ]}
  end.

  Definition sorts_app_interp (m1 m2 : sorts_carrier)
    : propset sorts_carrier :=
  match m1, m2 with
  | inr (), inr ()       => ∅ (* inh ⋅ inh *)
  | inr (), inl (inr ()) => ∅ (* inh ⋅ def *)
  | inr (), inl (inl x)  =>   (* inh ⋅ x *)
        (inl ∘ inl) <$> (sort_interp x)
  | inl (inr _), inr _   => ⊤ (* ⌈ ⌉ ⋅ inh <- Notion of definedness has to be extended *)
  | inl (inr _), inl _   => ⊤ (* ⌈ ⌉ ⋅ x <- Notion of definedness has to be extended *)
  | inl (inl _), inr _   => ∅ (* x ⋅ inh *)
  | inl x1, inl x2       =>   (* x ⋅ y*)
        inl <$> app_interp DefinednessModel x1 x2
  end.

  Definition SortsModel : Model := {|
    Domain := sorts_carrier;
    app_interp := sorts_app_interp;
    sym_interp := sorts_sym_interp;
  |}.

  Theorem SortsModel_satisfies_theory :
    SortsModel ⊨ᵀ Definedness_Syntax.theory.
  Proof.
    unfold Definedness_Syntax.theory. unfold Definedness_Syntax.named_axioms.
    unfold theory_of_NamedAxioms. simpl.
    unfold satisfies_theory. intros.
    rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
    cbn. unfold satisfies_model. intros.
    unfold patt_defined. unfold p_x, ev_x. simp eval.
    unfold sym_interp, app_ext. simpl.
    eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ SortsModel).
    apply set_equiv. intros. split; intros.
    * rewrite elem_of_PropSet in H. destruct H as [le [re [Hle [Hre Hx] ] ] ].
      destruct Hle. destruct Hre. by simpl in Hx.
    * rewrite elem_of_PropSet.
      exists (inl (inr ())), (evar_valuation ρ (evar_fresh [])).
      cbn. case_match; set_solver.
  Qed.
End Sorts.

Ltac eval_simpl :=
  try simp eval;
  try rewrite eval_not_simpl;
  try rewrite eval_and_simpl;
  try rewrite eval_or_simpl;
  try rewrite eval_top_simpl;
  try rewrite eval_iff_simpl;
  try rewrite eval_all_simpl;
(*  TODO:   try rewrite eval_nu_simpl; *)
  try unshelve (erewrite eval_forall_of_sort);
  try unshelve (erewrite eval_exists_of_sort);
  try apply propset_fa_union_full.

Ltac eval_simpl_in H :=
  try simp eval in H;
  try rewrite eval_not_simpl in H;
  try rewrite eval_and_simpl in H;
  try rewrite eval_or_simpl in H;
  try rewrite eval_top_simpl in H;
  try rewrite eval_iff_simpl in H;
  try rewrite eval_all_simpl in H;
(*  TODO:   try rewrite eval_nu_simpl; *)
  try unshelve (erewrite eval_forall_of_sort in H);
  try unshelve (erewrite eval_exists_of_sort in H);
  try apply propset_fa_union_full in H.

Section Bool.
  (* NOTE - INVESTIGATE:
    When we automatically generate carriers, should the partial
    operations use Coq standard types, or use the generated core
    symbols?
   *)
  Print Bool_Syntax.Symbols.
  Inductive bool_carrier :=
  | coreBoolSym (s : Bool_Syntax.Symbols)
  (* TODO: the next two should not be part of the signature/symbols but they are
     elements of the model's carrier *)
  | partialAnd (b : bool)
  | partialAndThen (b : option bool)
  (**)
  | defBool
  | inhBool
  .

  #[global]
  Instance bool_carrier_EqDec : EqDecision bool_carrier.
  Proof.
    solve_decision.
  Defined.

  #[global]
  Program Instance bool_carrier_finite : finite.Finite bool_carrier.
  Next Obligation.
    exact (fmap coreBoolSym [sBool; sTrue; sFalse; sAnd; sNeg; sAndThen] ++ 
           [partialAnd true; partialAnd false;
            partialAndThen (Some true); partialAndThen (Some false); partialAndThen None; defBool; inhBool]).
  Defined.
  Next Obligation.
    compute_done.
  Defined.
  Next Obligation.
    destruct x; try destruct s; try destruct b; try compute_done.
    cbn. destruct b; compute_done.
  Defined.

  Global Instance bool_carrier_countable : countable.Countable bool_carrier.
  Proof. apply finite.finite_countable. Defined.

  (* TODO: if partial ops are removed from the symbols, this has to be
           adjusted *)
  Instance bools_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols bool_carrier _ _;
  }.

  Program Instance bool_syntax : @Bool_Syntax.Syntax bools_Σ := {
    inj := coreBoolSym;
    imported_sorts := {|
      Sorts_Syntax.inj := fun x => inhBool;
      imported_definedness := {|
        Definedness_Syntax.inj := fun x => defBool;
      |};
    |};
  }.

  Definition bool_sym_interp (m : @symbols (@ml_symbols bools_Σ))
    : propset bool_carrier := {[ m ]}.

  Definition bool_app_interp (m1 m2 : bool_carrier)
    : propset bool_carrier :=
  match m1 with
   | coreBoolSym sAnd =>
     match m2 with
     | coreBoolSym sTrue => {[ partialAnd true ]}
     | coreBoolSym sFalse => {[ partialAnd false ]}
     | _ => ∅
     end
   | coreBoolSym sAndThen =>
     match m2 with
     | coreBoolSym sTrue => {[ partialAndThen (Some true) ]}
     | coreBoolSym sFalse => {[ partialAndThen (Some false) ]}
     | _ => {[ partialAndThen None ]}
     end
   | coreBoolSym sNeg =>
     match m2 with
     | coreBoolSym sTrue => {[ coreBoolSym sFalse ]}
     | coreBoolSym sFalse => {[ coreBoolSym sTrue ]}
     | _ => ∅
     end
   | coreBoolSym _ => ∅
   | partialAnd false =>
     match m2 with
     | coreBoolSym sTrue => {[ coreBoolSym sFalse ]}
     | coreBoolSym sFalse => {[ coreBoolSym sFalse ]}
     | _ => ∅
     end
   | partialAnd true =>
     match m2 with
     | coreBoolSym sTrue => {[ coreBoolSym sTrue ]}
     | coreBoolSym sFalse => {[ coreBoolSym sFalse ]}
     | _ => ∅
     end
   | partialAndThen (Some false) => {[ coreBoolSym sFalse ]}
   | partialAndThen (Some true) =>
     match m2 with
     | coreBoolSym sTrue => {[ coreBoolSym sTrue ]}
     | coreBoolSym sFalse => {[ coreBoolSym sFalse ]}
     | _ => ∅
     end
   | partialAndThen None =>
     match m2 with
     | coreBoolSym sFalse => {[ coreBoolSym sFalse ]}
     | _ => ∅
     end
   (**)
   | defBool => ⊤
   | inhBool =>
     match m2 with
     | coreBoolSym sBool => {[ coreBoolSym sFalse; coreBoolSym sTrue ]}
                            (* type value set *)
     | _ => ∅
     end
  end.

  Global Instance bool_carrier_inhabited : Inhabited bool_carrier.
  Proof.
    constructor. exact defBool.
  Defined.

  Program Definition BoolModel : Model := {|
    Domain := bool_carrier;
    app_interp := bool_app_interp;
    sym_interp := bool_sym_interp;
  |}.

  Theorem indec_bool :
    ∀ ρ s (m : BoolModel),
      Decision (m ∈ Minterp_inhabitant (patt_sym s) ρ).
  Proof.
    intros.
    unfold Minterp_inhabitant.
    simp eval. simpl.
    unfold Sorts_Semantics.sym.
    simp eval. simpl.
    unfold bool_sym_interp.
    destruct s; unfold app_ext.
    1: destruct s.
    2-8: right; intro; destruct H as [le [re [Hle [Hre Ht] ] ] ];
         apply elem_of_singleton_1 in Hle, Hre; subst;
         cbn in Ht; set_solver.
    destruct m.
    destruct s.
    1, 4-12: right; intro; destruct H as [le [re [Hle [Hre Ht] ] ] ];
            apply elem_of_singleton_1 in Hle, Hre; subst;
            cbn in Ht; set_solver.
    1-2: left;
         exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
  Defined.

  Hint Resolve propset_leibniz_equiv : core.

  Print BoolModel.

  Theorem BoolModel_satisfies_theory :
    BoolModel ⊨ᵀ Bool_Syntax.theory.
  Proof.
    assert (BoolModel ⊨ᵀ Definedness_Syntax.theory) as HDef. {
      unfold Bool_Syntax.theory, Definedness_Syntax.theory.
      unfold theory_of_NamedAxioms. simpl.
      unfold satisfies_theory. intros.
      rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
      cbn. unfold satisfies_model. intros.
      unfold patt_defined. unfold p_x, ev_x. simp eval.
      unfold sym_interp, app_ext. simpl.
      eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ BoolModel).
      apply set_equiv. intros. split; intros; set_solver.
    }
    unfold Bool_Syntax.theory, Definedness_Syntax.theory.
    unfold theory_of_NamedAxioms. simpl.
    unfold satisfies_theory. intros.
    rewrite elem_of_union in H. destruct H as [H | H].
    * (* This subgoal uses boiler-plate proof *)
      rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
      cbn. unfold satisfies_model. intros.
      unfold patt_defined. unfold p_x, ev_x. simp eval.
      unfold sym_interp, app_ext. simpl.
      eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ BoolModel).
      apply set_equiv. intros. split; intros; set_solver.
    * rewrite elem_of_PropSet in H. destruct H.
      destruct x;subst;cbn; unfold satisfies_model; intros.
      (* true is functional *)
      - (* TODO: simplification tactic for eval is needed!
           Potentially we could base this on typeclasses too. *)
        eval_simpl; auto.
        1: apply indec_bool.
        intros. mlSimpl. cbn. exists (coreBoolSym sTrue). case_match.
        + remember (fresh_evar (mlTrue =ml b0)) as x. clear Heqx.
          unfold patt_equal, patt_total, patt_defined, mlTrue.
          repeat eval_simpl. cbn. unfold bool_sym_interp.
          rewrite decide_eq_same. unfold app_ext. eapply elem_of_compl.
          (* Unshelve. 2: exact (@propset_leibniz_equiv _ BoolModel). *)
          apply not_elem_of_PropSet. intro. destruct H0 as [le [re [Hle [Hre Ht] ] ] ].
          apply elem_of_singleton_1 in Hle. subst.
          apply (proj1 (elem_of_compl _ _)) in Hre; auto. apply Hre.
          set_solver.
        + unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
          simpl in n. clear H. simp eval in n. exfalso.
          apply n. clear. exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
      (* false is functional *)
      - eval_simpl; auto.
        1: apply indec_bool.
        intros. mlSimpl. cbn. exists (coreBoolSym sFalse). case_match.
        + remember (fresh_evar (mlFalse =ml b0)) as x. clear Heqx.
          unfold patt_equal, patt_total, patt_defined, mlFalse.
          repeat eval_simpl. cbn. unfold bool_sym_interp.
          rewrite decide_eq_same. unfold app_ext. eapply elem_of_compl.
          (* Unshelve. 2: exact (@propset_leibniz_equiv _ BoolModel). *)
          apply not_elem_of_PropSet. intro. destruct H0 as [le [re [Hle [Hre Ht] ] ] ].
          apply elem_of_singleton_1 in Hle. subst.
          apply (proj1 (elem_of_compl _ _)) in Hre; auto. apply Hre.
          set_solver.
        + unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
          simpl in n. clear H. simp eval in n. exfalso.
          apply n. clear. exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
      (* and is functional *)
      - eval_simpl; auto.
        1: apply indec_bool.
        apply propset_fa_intersection_full. intros. case_match. 2: by reflexivity.
        pose proof sorted_forall_binder as BF. destruct BF as [BF].
        pose proof sorted_exists_binder as BE. destruct BE as [BE].
        erewrite (BF _ (evar_open _)); eauto.
        erewrite (BE _ (evar_open _)); eauto.
        mlSimpl. cbn.
        eval_simpl; auto. 1: apply indec_bool.
        eapply propset_fa_intersection_full. intros. case_match. 2: by reflexivity.
        erewrite (BE _ (evar_open _)); eauto.
        mlSimpl. cbn.
        eval_simpl; auto. 1: apply indec_bool.
        remember (fresh_evar _) as X.
        remember (fresh_evar (patt_exists_of_sort mlBool (mlBAnd b1 (patt_free_evar X) =ml b0))) as Y.
        unfold Minterp_inhabitant in *.
        clear H0 H. eval_simpl_in e. eval_simpl_in e0.
        unfold app_ext in *.
        apply elem_of_PropSet in e, e0.
        destruct e as [le1 [re1 [Hle1 [Hre1 Hlere1] ] ] ].
        destruct e0 as [le2 [re2 [Hle2 [Hre2 Hlere2] ] ] ].
        unfold Sorts_Semantics.sym in *.
        simp eval in *. simpl in *.
        unfold bool_sym_interp in *. apply elem_of_singleton in Hle1, Hle2, Hre1, Hre2.
        subst le1 le2 re1 re2.
        unfold bool_app_interp in *.
        assert ((c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) /\
                (c0 = coreBoolSym sFalse \/ c0 = coreBoolSym sTrue)) by set_solver.
        remember (fresh_evar (mlBAnd (patt_free_evar _) (patt_free_evar _) =ml b0))
           as Z.
        assert (X <> Y /\ Y <> Z /\ X <> Z) as [HXY [HYZ HXZ] ]. {
          split_and!.
          * subst Y. clear.
            unfold fresh_evar. pose proof (X_eq_evar_fresh_impl_X_notin_S X (free_evars (patt_exists_of_sort mlBool ((mlBAnd b1 (patt_free_evar X)) =ml b0)))).
            set_solver.
          * subst Z. clear.
            unfold fresh_evar. pose proof (X_eq_evar_fresh_impl_X_notin_S Y (free_evars ((mlBAnd (patt_free_evar Y) (patt_free_evar X)) =ml b0))).
            set_solver.
          * subst Z. clear.
            unfold fresh_evar. pose proof (X_eq_evar_fresh_impl_X_notin_S X (free_evars ((mlBAnd (patt_free_evar Y) (patt_free_evar X)) =ml b0))).
            set_solver.
        }
        clear HeqX HeqY HeqZ.
        destruct H as [ [Hc | Hc] [Hc0 | Hc0] ]; subst c c0.
        (* The proof for the following 4 cases is the same           |   *)
        (* false and false                          except this      v   *)
        + eapply propset_fa_union_full. intros. exists (coreBoolSym sFalse).
          case_match.
          ** clear H e. mlSimpl. cbn.
             unfold mlBAnd, mlsBAnd.
             revert t.
             apply propset_top_elem_of.
             eapply (equal_iff_interpr_same BoolModel HDef). (* explicit model needed *)
             eval_simpl; auto. unfold app_ext. cbn.
             repeat destruct decide; try congruence.
             eapply set_eq. intros. rewrite elem_of_PropSet.
             split.
             -- intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
                unfold bool_sym_interp in *. apply elem_of_singleton in EQ2. subst.
                destruct EQ1 as [? [? [? [? ?] ] ] ].
                apply elem_of_singleton in H, H0. subst.
                unfold bool_app_interp in *.
                apply elem_of_singleton in H1. subst.
                assumption.
             -- intros. do 2 eexists. split. 2: split.
                2: by apply elem_of_singleton.
                apply elem_of_PropSet. do 2 eexists. split_and!.
                all: try by apply elem_of_singleton.
          ** unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
             simpl in n. clear H. simp eval in n. exfalso.
             apply n. clear. exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
        (* false and true *)
        + eapply propset_fa_union_full. intros. exists (coreBoolSym sFalse).
          case_match.
          ** clear H e. mlSimpl. cbn.
             unfold mlBAnd, mlsBAnd.
             revert t.
             apply propset_top_elem_of.
             eapply (equal_iff_interpr_same BoolModel HDef). (* explicit model needed *)
             eval_simpl; auto. unfold app_ext. cbn.
             repeat destruct decide; try congruence.
             eapply set_eq. intros. rewrite elem_of_PropSet.
             split.
             -- intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
                unfold bool_sym_interp in *. apply elem_of_singleton in EQ2. subst.
                destruct EQ1 as [? [? [? [? ?] ] ] ].
                apply elem_of_singleton in H, H0. subst.
                unfold bool_app_interp in *.
                apply elem_of_singleton in H1. subst.
                assumption.
             -- intros. do 2 eexists. split. 2: split.
                2: by apply elem_of_singleton.
                apply elem_of_PropSet. do 2 eexists. split_and!.
                all: try by apply elem_of_singleton.
          ** unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
             simpl in n. clear H. simp eval in n. exfalso.
             apply n. clear. exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
        (* true and false *)
        + eapply propset_fa_union_full. intros. exists (coreBoolSym sFalse).
          case_match.
          ** clear H e. mlSimpl. cbn.
             unfold mlBAnd, mlsBAnd.
             revert t.
             apply propset_top_elem_of.
             eapply (equal_iff_interpr_same BoolModel HDef). (* explicit model needed *)
             eval_simpl; auto. unfold app_ext. cbn.
             repeat destruct decide; try congruence.
             eapply set_eq. intros. rewrite elem_of_PropSet.
             split.
             -- intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
                unfold bool_sym_interp in *. apply elem_of_singleton in EQ2. subst.
                destruct EQ1 as [? [? [? [? ?] ] ] ].
                apply elem_of_singleton in H, H0. subst.
                unfold bool_app_interp in *.
                apply elem_of_singleton in H1. subst.
                assumption.
             -- intros. do 2 eexists. split. 2: split.
                2: by apply elem_of_singleton.
                apply elem_of_PropSet. do 2 eexists. split_and!.
                all: try by apply elem_of_singleton.
          ** unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
             simpl in n. clear H. simp eval in n. exfalso.
             apply n. clear. exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
        (* true and true *)
        + eapply propset_fa_union_full. intros. exists (coreBoolSym sTrue).
          case_match.
          ** clear H e. mlSimpl. cbn.
             unfold mlBAnd, mlsBAnd.
             revert t.
             apply propset_top_elem_of.
             eapply (equal_iff_interpr_same BoolModel HDef). (* explicit model needed *)
             eval_simpl; auto. unfold app_ext. cbn.
             repeat destruct decide; try congruence.
             eapply set_eq. intros. rewrite elem_of_PropSet.
             split.
             -- intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
                unfold bool_sym_interp in *. apply elem_of_singleton in EQ2. subst.
                destruct EQ1 as [? [? [? [? ?] ] ] ].
                apply elem_of_singleton in H, H0. subst.
                unfold bool_app_interp in *.
                apply elem_of_singleton in H1. subst.
                assumption.
             -- intros. do 2 eexists. split. 2: split.
                2: by apply elem_of_singleton.
                apply elem_of_PropSet. do 2 eexists. split_and!.
                all: try by apply elem_of_singleton.
          ** unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
             simpl in n. clear H. simp eval in n. exfalso.
             apply n. clear. exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
      (* not is functional *)
      - eval_simpl; auto.
        1: apply indec_bool.
        apply propset_fa_intersection_full. intros. case_match. 2: by reflexivity.
        pose proof sorted_exists_binder as BE. destruct BE as [BE].
        erewrite (BE _ (evar_open _)); eauto.
        mlSimpl. cbn.
        eval_simpl; auto. 1: apply indec_bool.
        remember (fresh_evar _) as X.
        remember (fresh_evar (mlBNeg (patt_free_evar X) =ml b0)) as Y.
        unfold Minterp_inhabitant in *.
        clear H. eval_simpl_in e.
        unfold app_ext in *.
        apply elem_of_PropSet in e.
        destruct e as [le [re [Hle [Hre Hlere] ] ] ].
        unfold Sorts_Semantics.sym in *.
        simp eval in *. simpl in *.
        unfold bool_sym_interp in *. apply elem_of_singleton in Hre, Hle.
        subst le re.
        unfold bool_app_interp in *.
        assert ((c = coreBoolSym sFalse \/ c = coreBoolSym sTrue)) by set_solver.
        assert (X <> Y) as HXY. {
          subst Y. clear.
          unfold fresh_evar. pose proof (X_eq_evar_fresh_impl_X_notin_S X (free_evars (mlBNeg (patt_free_evar X) =ml b0))).
          set_solver.
        }
        clear HeqX HeqY.
        destruct H; subst c.
        + eapply propset_fa_union_full. intros. exists (coreBoolSym sTrue).
          case_match.
          ** clear H e. mlSimpl. cbn.
             unfold mlBNeg, mlsBNeg.
             revert t.
             apply propset_top_elem_of.
             eapply (equal_iff_interpr_same BoolModel HDef). (* explicit model needed *)
             eval_simpl; auto. unfold app_ext. cbn.
             repeat destruct decide; try congruence.
             eapply set_eq. intros. rewrite elem_of_PropSet.
             split.
             -- intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
                unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
                subst.
                unfold bool_app_interp in *.
                assumption.
             -- intros. do 2 eexists. split. 2: split.
                1-2: by apply elem_of_singleton.
                assumption.
          ** unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
             simpl in n. clear H. simp eval in n. exfalso.
             apply n. clear. exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
        + eapply propset_fa_union_full. intros. exists (coreBoolSym sFalse).
          case_match.
          ** clear H e. mlSimpl. cbn.
             unfold mlBNeg, mlsBNeg.
             revert t.
             apply propset_top_elem_of.
             eapply (equal_iff_interpr_same BoolModel HDef). (* explicit model needed *)
             eval_simpl; auto. unfold app_ext. cbn.
             repeat destruct decide; try congruence.
             eapply set_eq. intros. rewrite elem_of_PropSet.
             split.
             -- intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
                unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
                subst.
                unfold bool_app_interp in *.
                assumption.
             -- intros. do 2 eexists. split. 2: split.
                1-2: by apply elem_of_singleton.
                assumption.
          ** unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
             simpl in n. clear H. simp eval in n. exfalso.
             apply n. clear. exists (inhBool), (coreBoolSym sBool); split; try split; set_solver.
      (* NoConfusion *)
      - eval_simpl. apply complement_full_iff_empty.
        apply not_equal_iff_not_interpr_same_1. assumption.
        unfold mlTrue, mlFalse. simp eval. cbn. unfold bool_sym_interp.
        assert ((coreBoolSym sFalse) <> (coreBoolSym sTrue)). {
          intro. inversion H.
        }
        intro.
        apply H.
        eapply set_eq with (x := coreBoolSym sTrue) in H0.
        do 2 rewrite elem_of_singleton in H0.
        specialize (proj1 H0 eq_refl). congruence.
      (* Inductive Domain *)
      - apply equal_iff_interpr_same. assumption.
        unfold patt_inhabitant_set, mlTrue, mlFalse, mlBool. simpl.
        eval_simpl. simp eval. simpl. unfold bool_sym_interp.
        unfold app_ext. eapply set_eq.
        intros. rewrite elem_of_PropSet. cbn. unfold Sorts_Syntax.sym.
        simp eval. cbn. unfold bool_sym_interp. split.
        + intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
          apply elem_of_singleton in EQ1, EQ2. subst.
          unfold bool_app_interp in EQ3. set_solver.
        + intros. do 2 eexists. split_and!. 1-2: by apply elem_of_singleton.
          set_solver.
      (* Behavioural axioms *)
      - unfold mlBNeg, mlsBNeg, mlTrue, mlFalse.
        apply equal_iff_interpr_same. assumption.
        eval_simpl. simpl. unfold bool_sym_interp.
        unfold app_ext.
        (* TODO: app_ext for singletons *)
        eapply set_eq. split.
        + intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
          apply elem_of_singleton in EQ1, EQ2. subst.
          unfold bool_app_interp in EQ3. set_solver.
        + intros. do 2 eexists. split_and!. 1-2: by apply elem_of_singleton.
          set_solver.
      - unfold mlBNeg, mlsBNeg, mlTrue, mlFalse.
        apply equal_iff_interpr_same. assumption.
        eval_simpl. simpl. unfold bool_sym_interp.
        unfold app_ext.
        (* TODO: app_ext for singletons *)
        eapply set_eq. split.
        + intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
          apply elem_of_singleton in EQ1, EQ2. subst.
          unfold bool_app_interp in EQ3. set_solver.
        + intros. do 2 eexists. split_and!. 1-2: by apply elem_of_singleton.
          set_solver.
      - unfold mlBAnd, mlsBAnd, mlTrue, mlFalse, mlBool.
        eval_simpl. 1: apply indec_bool.
        apply propset_fa_intersection_full. 2: assumption. intros.
        case_match. 2: reflexivity.
        apply equal_iff_interpr_same. assumption.
        eval_simpl. simpl. unfold bool_sym_interp.
        clear H. unfold Minterp_inhabitant in e. simp eval in e.
        unfold app_ext in e. simpl in e. apply elem_of_PropSet in e.
        destruct e as [le [re [EQ1 [EQ2 EQ3] ] ] ].
        unfold Sorts_Semantics.sym in EQ1. simp eval in EQ1.
        simpl in *. unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
        subst. unfold bool_app_interp in *. simpl in *.
        unfold app_ext.
        (* TODO: app_ext for singletons *)
        eapply set_eq. split.
        + intros. destruct H as [le1 [re1 [EQ1 [EQ2 EQ4] ] ] ].
          apply elem_of_singleton in EQ2. subst.
          apply elem_of_PropSet in EQ1.
          destruct EQ1 as [le2 [re2 [EQ5 [EQ6 EQ7] ] ] ].
          simp eval in EQ6. rewrite update_evar_val_same in EQ6.
          apply elem_of_singleton in EQ5, EQ6. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** eval_simpl. rewrite update_evar_val_same.
             simpl in *. apply elem_of_singleton in EQ7. subst.
             unfold bool_app_interp in EQ4. apply elem_of_singleton in EQ4.
             set_solver.
          ** eval_simpl. rewrite update_evar_val_same.
             simpl in *. apply elem_of_singleton in EQ7. subst.
             unfold bool_app_interp in EQ4. apply elem_of_singleton in EQ4.
             set_solver.
        + intros. eval_simpl_in H.
          rewrite update_evar_val_same in H. apply elem_of_singleton in H. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** do 2 eexists. split_and!. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: by apply elem_of_singleton.
             eval_simpl. rewrite update_evar_val_same. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
          ** do 2 eexists. split_and!. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: by apply elem_of_singleton.
             eval_simpl. rewrite update_evar_val_same. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
      - unfold mlBAnd, mlsBAnd, mlTrue, mlFalse, mlBool.
        eval_simpl. 1: apply indec_bool.
        apply propset_fa_intersection_full. 2: assumption. intros.
        case_match. 2: reflexivity.
        apply equal_iff_interpr_same. assumption.
        eval_simpl. simpl. unfold bool_sym_interp.
        clear H. unfold Minterp_inhabitant in e. simp eval in e.
        unfold app_ext in e. simpl in e. apply elem_of_PropSet in e.
        destruct e as [le [re [EQ1 [EQ2 EQ3] ] ] ].
        unfold Sorts_Semantics.sym in EQ1. simp eval in EQ1.
        simpl in *. unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
        subst. unfold bool_app_interp in *. simpl in *.
        unfold app_ext.
        (* TODO: app_ext for singletons *)
        eapply set_eq. split.
        + intros. destruct H as [le1 [re1 [EQ1 [EQ2 EQ4] ] ] ].
          apply elem_of_singleton in EQ2. subst.
          apply elem_of_PropSet in EQ1.
          destruct EQ1 as [le2 [re2 [EQ5 [EQ6 EQ7] ] ] ].
          simp eval in EQ6. rewrite update_evar_val_same in EQ6.
          apply elem_of_singleton in EQ5, EQ6. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** simpl in *. apply elem_of_singleton in EQ7. subst.
             unfold bool_app_interp in EQ4. apply elem_of_singleton in EQ4.
             set_solver.
          ** simpl in *. apply elem_of_singleton in EQ7. subst.
             unfold bool_app_interp in EQ4. apply elem_of_singleton in EQ4.
             set_solver.
        + intros. eval_simpl_in H. apply elem_of_singleton in H. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** do 2 eexists. split_and!. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: by apply elem_of_singleton.
             eval_simpl. rewrite update_evar_val_same. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
          ** do 2 eexists. split_and!. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: by apply elem_of_singleton.
             eval_simpl. rewrite update_evar_val_same. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
      - unfold mlBAnd, mlsBAnd, mlTrue, mlFalse, mlBool.
        eval_simpl. 1: apply indec_bool.
        apply propset_fa_intersection_full. 2: assumption. intros.
        case_match. 2: reflexivity.
        apply equal_iff_interpr_same. assumption.
        eval_simpl. simpl. unfold bool_sym_interp.
        clear H. unfold Minterp_inhabitant in e. simp eval in e.
        unfold app_ext in e. simpl in e. apply elem_of_PropSet in e.
        destruct e as [le [re [EQ1 [EQ2 EQ3] ] ] ].
        unfold Sorts_Semantics.sym in EQ1. simp eval in EQ1.
        simpl in *. unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
        subst. unfold bool_app_interp in *. simpl in *.
        unfold app_ext.
        (* TODO: app_ext for singletons *)
        eapply set_eq. split.
        + intros. destruct H as [le1 [re1 [EQ1 [EQ2 EQ4] ] ] ].
          apply elem_of_PropSet in EQ1.
          destruct EQ1 as [le2 [re2 [EQ5 [EQ6 EQ7] ] ] ].
          simp eval in *. rewrite update_evar_val_same in EQ2.
          apply elem_of_singleton in EQ5, EQ6, EQ2. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** eval_simpl. rewrite update_evar_val_same.
             simpl in *. apply elem_of_singleton in EQ7. subst.
             unfold bool_app_interp in EQ4. apply elem_of_singleton in EQ4.
             set_solver.
          ** eval_simpl. rewrite update_evar_val_same.
             simpl in *. apply elem_of_singleton in EQ7. subst.
             unfold bool_app_interp in EQ4. apply elem_of_singleton in EQ4.
             set_solver.
        + intros. eval_simpl_in H.
          rewrite update_evar_val_same in H. apply elem_of_singleton in H. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** do 2 eexists. split_and!.
             2: simp eval; rewrite update_evar_val_same. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: by apply elem_of_singleton.
             eval_simpl. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
          ** do 2 eexists. split_and!.
             2: simp eval; rewrite update_evar_val_same. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: by apply elem_of_singleton.
             eval_simpl. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
      - unfold mlBAnd, mlsBAnd, mlTrue, mlFalse, mlBool.
        eval_simpl. 1: apply indec_bool.
        apply propset_fa_intersection_full. 2: assumption. intros.
        case_match. 2: reflexivity.
        apply equal_iff_interpr_same. assumption.
        eval_simpl. simpl. unfold bool_sym_interp.
        clear H. unfold Minterp_inhabitant in e. simp eval in e.
        unfold app_ext in e. simpl in e. apply elem_of_PropSet in e.
        destruct e as [le [re [EQ1 [EQ2 EQ3] ] ] ].
        unfold Sorts_Semantics.sym in EQ1. simp eval in EQ1.
        simpl in *. unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
        subst. unfold bool_app_interp in *. simpl in *.
        unfold app_ext.
        (* TODO: app_ext for singletons *)
        eapply set_eq. split.
        + intros. destruct H as [le1 [re1 [EQ1 [EQ2 EQ4] ] ] ].
          apply elem_of_PropSet in EQ1.
          destruct EQ1 as [le2 [re2 [EQ5 [EQ6 EQ7] ] ] ].
          simp eval in *. rewrite update_evar_val_same in EQ2.
          apply elem_of_singleton in EQ5, EQ6, EQ2. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** simpl in *. apply elem_of_singleton in EQ7. subst.
             unfold bool_app_interp in EQ4. apply elem_of_singleton in EQ4.
             set_solver.
          ** simpl in *. apply elem_of_singleton in EQ7. subst.
             unfold bool_app_interp in EQ4. apply elem_of_singleton in EQ4.
             set_solver.
        + intros. apply elem_of_singleton in H. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** do 2 eexists. split_and!.
             2: simp eval; rewrite update_evar_val_same. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: by apply elem_of_singleton.
             eval_simpl. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
          ** do 2 eexists. split_and!.
             2: simp eval; rewrite update_evar_val_same. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: by apply elem_of_singleton.
             eval_simpl. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
      - unfold mlBAndThen, mlsBAndThen, mlTrue, mlFalse, mlBool.
        eval_simpl. 1: apply indec_bool.
        apply propset_fa_intersection_full. 2: assumption. intros.
        case_match. 2: reflexivity.
        apply equal_iff_interpr_same. assumption.
        eval_simpl. simpl. unfold bool_sym_interp.
        clear H. unfold Minterp_inhabitant in e. simp eval in e.
        unfold app_ext in e. simpl in e. apply elem_of_PropSet in e.
        destruct e as [le [re [EQ1 [EQ2 EQ3] ] ] ].
        unfold Sorts_Semantics.sym in EQ1. simp eval in EQ1.
        simpl in *. unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
        subst. unfold bool_app_interp in *. simpl in *.
        unfold app_ext.
        (* TODO: app_ext for singletons *)
        eapply set_eq. split.
        + intros. destruct H as [le1 [re1 [EQ1 [EQ2 EQ4] ] ] ].
          apply elem_of_singleton in EQ2. subst.
          apply elem_of_PropSet in EQ1.
          destruct EQ1 as [le2 [re2 [EQ5 [EQ6 EQ7] ] ] ].
          simp eval in *. rewrite update_evar_val_same in EQ6.
          simpl in EQ5. unfold bool_sym_interp in EQ5.
          apply elem_of_singleton in EQ5, EQ6. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** eval_simpl. rewrite update_evar_val_same.
             simpl in *.
             set_solver.
          ** eval_simpl. rewrite update_evar_val_same.
             simpl in *.
             set_solver.
        + intros. eval_simpl_in H.
          rewrite update_evar_val_same in H. apply elem_of_singleton in H. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** do 2 eexists. split_and!. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!.
             1: simp eval; by apply elem_of_singleton.
             eval_simpl. rewrite update_evar_val_same. by apply elem_of_singleton.
             simpl. by apply elem_of_singleton. cbn. set_solver.
          ** do 2 eexists. split_and!. 2: by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: simp eval; by apply elem_of_singleton.
             eval_simpl. rewrite update_evar_val_same. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
      - unfold mlBAndThen, mlsBAndThen, mlTrue, mlFalse, mlBool. simpl.
        eval_simpl. simpl.
        eapply propset_fa_intersection_full. intros.
        mlSimpl. cbn. remember (fresh_evar _) as X. clear HeqX.
        apply (@equal_iff_interpr_same _ _ BoolModel HDef).
        eval_simpl. simpl. unfold bool_sym_interp.
        unfold app_ext. case_match. 2: congruence.
        simpl in *.
        (* TODO: app_ext for singletons *)
        eapply set_eq. intros. rewrite elem_of_PropSet. split.
        + intros. destruct H0 as [le1 [re1 [EQ1 [EQ2 EQ4] ] ] ].
          apply elem_of_singleton in EQ2. subst.
          apply elem_of_PropSet in EQ1.
          destruct EQ1 as [le2 [re2 [EQ5 [EQ6 EQ7] ] ] ].
          apply elem_of_singleton in EQ5, EQ6. subst.
          unfold bool_app_interp in *. destruct c. destruct s.
          ** set_solver.
          ** set_solver.
          ** apply elem_of_singleton in EQ7. subst. assumption.
          ** set_solver.
          ** set_solver.
          ** set_solver.
          ** set_solver.
          ** set_solver.
          ** set_solver.
          ** set_solver.
        + intros. apply elem_of_singleton in H0. subst.
          destruct c; try destruct s; do 2 eexists; split_and!. all: try by apply elem_of_singleton.
          all: try apply elem_of_PropSet; try do 2 eexists; try split_and!.
          all: try by apply elem_of_singleton.
          all:unfold bool_app_interp. 3-6: set_solver.
          all: set_solver.
      - unfold mlBAndThen, mlsBAndThen, mlTrue, mlFalse, mlBool.
        eval_simpl. 1: apply indec_bool.
        apply propset_fa_intersection_full. 2: assumption. intros.
        case_match. 2: reflexivity.
        apply equal_iff_interpr_same. assumption.
        eval_simpl. simpl. unfold bool_sym_interp.
        clear H. unfold Minterp_inhabitant in e. simp eval in e.
        unfold app_ext in e. simpl in e. apply elem_of_PropSet in e.
        destruct e as [le [re [EQ1 [EQ2 EQ3] ] ] ].
        unfold Sorts_Semantics.sym in EQ1. simp eval in EQ1.
        simpl in *. unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
        subst. unfold bool_app_interp in *. simpl in *.
        unfold app_ext.
        (* TODO: app_ext for singletons *)
        eapply set_eq. split.
        + intros. destruct H as [le1 [re1 [EQ1 [EQ2 EQ4] ] ] ].
          apply elem_of_PropSet in EQ1. simp eval in *.
          destruct EQ1 as [le2 [re2 [EQ5 [EQ6 EQ7] ] ] ].
          simp eval in *. rewrite update_evar_val_same in EQ2. simpl in *.
          apply elem_of_singleton in EQ5, EQ6, EQ2. subst.
          unfold bool_app_interp in EQ7.
          apply elem_of_singleton in EQ7. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** set_solver.
          ** set_solver.
        + intros. eval_simpl_in H.
          rewrite update_evar_val_same in H. apply elem_of_singleton in H. subst.
          assert (c = coreBoolSym sFalse \/ c = coreBoolSym sTrue) as [|] by set_solver; subst.
          ** do 2 eexists. split_and!.
             2: simp eval; rewrite update_evar_val_same; by apply elem_of_singleton.
             do 2 eexists. split_and!.
             1: simp eval; by apply elem_of_singleton.
             eval_simpl. by apply elem_of_singleton.
             simpl. by apply elem_of_singleton. cbn. set_solver.
          ** do 2 eexists. split_and!.
             2: simp eval; rewrite update_evar_val_same; by apply elem_of_singleton.
             do 2 eexists. split_and!. 1: simp eval; by apply elem_of_singleton.
             eval_simpl. by apply elem_of_singleton.
             by apply elem_of_singleton. cbn. set_solver.
      - unfold mlBAndThen, mlsBAndThen, mlTrue, mlFalse, mlBool. simpl.
        eval_simpl. simpl.
        eapply propset_fa_intersection_full. intros.
        mlSimpl. cbn. remember (fresh_evar _) as X. clear HeqX.
        apply (@equal_iff_interpr_same _ _ BoolModel HDef).
        eval_simpl. simpl. unfold bool_sym_interp.
        unfold app_ext. case_match. 2: congruence.
        simpl in *.
        (* TODO: app_ext for singletons *)
        eapply set_eq. intros. rewrite elem_of_PropSet. split.
        + intros. destruct H0 as [le1 [re1 [EQ1 [EQ2 EQ4] ] ] ].
          apply elem_of_singleton in EQ2. subst.
          apply elem_of_PropSet in EQ1.
          destruct EQ1 as [le2 [re2 [EQ5 [EQ6 EQ7] ] ] ].
          apply elem_of_singleton in EQ5, EQ6. subst.
          unfold bool_app_interp in *. destruct c. destruct s.
          ** set_solver.
          ** set_solver.
          ** apply elem_of_singleton in EQ7. subst. assumption.
          ** set_solver.
          ** set_solver.
          ** set_solver.
          ** set_solver.
          ** set_solver.
          ** set_solver.
          ** set_solver.
        + intros. apply elem_of_singleton in H0. subst.
          destruct c; try destruct s; do 2 eexists; split_and!. all: try by apply elem_of_singleton.
          all: try apply elem_of_PropSet; try do 2 eexists; try split_and!.
          all: try by apply elem_of_singleton.
          all:unfold bool_app_interp. 3-6: set_solver.
          all: set_solver.
  Unshelve.
    all: apply (@propset_leibniz_equiv _ BoolModel).
  Qed.

End Bool. 

Section Nat.

  Print Nat_Syntax.Symbols.
  Inductive nat_carrier :=
  | coreNatSym (s : Nat_Syntax.Symbols)
  (* TODO: these two should not be in the signature, only in the carrier *)
  | partialAdd (s : nat)
  | natVal (n : nat)
  (**)
  | defNat
  | inhNat
  .

  #[global]
  Instance nat_carrier_EqDec : EqDecision nat_carrier.
  Proof.
    solve_decision.
  Defined.

  Global Instance nat_carrier_countable : countable.Countable nat_carrier.
  Proof.
    set (enc := fun (n : nat_carrier) =>
      match n with
      | coreNatSym s =>
        match s with
         | sNat => inl (inl ())
         | sZero => inl (inr (inl ()))
         | sSucc => inl (inr (inr (inl ())))
         | sAddNat => inl (inr (inr (inr (inl ()))))
        end
      | natVal n => inr (inl n)
      | partialAdd n => inr (inr n)
      | defNat => inl (inr (inr (inr (inr (inl ())))))
      | inhNat => inl (inr (inr (inr (inr (inr ())))))
      end).
    set (dec := fun t =>
      match t with
      | inl (inr (inr (inr (inr (inr ()))))) => inhNat
      | inl (inr (inr (inr (inr (inl ()))))) => defNat
      | inl (inr (inr (inr (inl ())))) => coreNatSym sAddNat
      | inl (inr (inr (inl ()))) => coreNatSym sSucc
      | inl (inr (inl ())) => coreNatSym sZero
      | inl (inl ()) => coreNatSym sNat
      | inr (inl n) => natVal n
      | inr (inr n) => partialAdd n
      end
    ).
    apply inj_countable' with (f := enc) (g := dec).
    by destruct x; try destruct s.
  Defined.

  Instance nat_Σ : Signature := {
    variables := StringMLVariables;
    ml_symbols := Build_MLSymbols nat_carrier _ _;
  }.

  Program Instance nat_syntax : @Nat_Syntax.Syntax nat_Σ := {
    inj := coreNatSym;
    imported_sorts := {|
      Sorts_Syntax.inj := fun x => inhNat;
      imported_definedness := {|
        Definedness_Syntax.inj := fun x => defNat;
      |};
    |};
  }.

  Definition nat_sym_interp (m : symbols)
    : propset nat_carrier :=
  match m with
  | coreNatSym sZero => {[ natVal 0 ]}
  | x => {[ x ]}
  end.

  Definition nat_app_interp (m1 m2 : nat_carrier)
    : propset nat_carrier :=
  match m1 with
   | coreNatSym sSucc =>
     match m2 with
     | natVal n => {[ natVal (S n) ]}
     | _ => ∅
     end
   | coreNatSym sAddNat =>
     match m2 with
     | natVal n => {[ partialAdd n ]}
     | _ => ∅
     end
   | coreNatSym _ => ∅
   | partialAdd n =>
     match m2 with
     | natVal m => {[ natVal (n + m) ]}
     | _ => ∅
     end
   (**)
   | natVal _ => ∅
   | defNat => ⊤
   | inhNat =>
     match m2 with
     | coreNatSym sNat => {[ m | exists n, m = natVal n ]}
     | _ => ∅
     end
  end.

  Global Instance nat_carrier_inhabited : Inhabited nat_carrier.
  Proof.
    constructor. exact defNat.
  Defined.

  Program Definition NatModel : Model := {|
    Domain := nat_carrier;
    app_interp := nat_app_interp;
    sym_interp := nat_sym_interp;
  |}.

  Theorem indec_nat :
    ∀ ρ s (m : NatModel),
      Decision (m ∈ Minterp_inhabitant (patt_sym s) ρ).
  Proof.
    intros.
    unfold Minterp_inhabitant.
    simp eval. simpl.
    unfold Sorts_Semantics.sym.
    simp eval. simpl.
    unfold bool_sym_interp.
    destruct s; unfold app_ext.
    1: destruct s.
    2-8: right; intro; destruct H as [le [re [Hle [Hre Ht] ] ] ];
         try apply elem_of_singleton_1 in Hle, Hre; subst;
         cbn in Ht; set_solver.
    destruct m.
    destruct s.
    1-5,7-8: right; intro; destruct H as [le [re [Hle [Hre Ht] ] ] ];
            try apply elem_of_singleton_1 in Hle;
            try apply elem_of_singleton_1 in Hre; subst;
            cbn in Ht; try set_solver.
    all: try destruct re; try set_solver.
    all: try destruct s; try set_solver.
    destruct s0; try set_solver.
    destruct s0; try set_solver.
    left. do 2 eexists. split_and!. 1-2: cbn; by apply elem_of_singleton.
    simpl. set_solver.
  Defined.

  Hint Resolve propset_leibniz_equiv : core.

  Theorem NatModel_satisfies_theory :
    NatModel ⊨ᵀ Nat_Syntax.theory.
  Proof.
    pose proof (@propset_leibniz_equiv _ NatModel) as LEQ.
    assert (NatModel ⊨ᵀ Definedness_Syntax.theory) as HDef. {
      unfold Nat_Syntax.theory, Definedness_Syntax.theory.
      unfold theory_of_NamedAxioms. simpl.
      unfold satisfies_theory. intros.
      rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
      cbn. unfold satisfies_model. intros.
      unfold patt_defined. unfold p_x, ev_x. simp eval.
      unfold sym_interp, app_ext. simpl.
      eapply leibniz_equiv.
      apply set_equiv. intros. split; intros; set_solver.
    }
    unfold Nat_Syntax.theory, Definedness_Syntax.theory.
    unfold theory_of_NamedAxioms. simpl.
    unfold satisfies_theory. intros.
    rewrite elem_of_union in H. destruct H as [H | H].
    * (* This subgoal uses boiler-plate proof *)
      rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
      cbn. unfold satisfies_model. intros.
      unfold patt_defined. unfold p_x, ev_x. simp eval.
      unfold sym_interp, app_ext. simpl.
      eapply leibniz_equiv.
      apply set_equiv. intros. split; intros; set_solver.
    * rewrite elem_of_PropSet in H. destruct H.
      destruct x;subst;cbn; unfold satisfies_model; intros.
      (* zero is functional - same as for true/false *)
      - eval_simpl; auto. apply indec_nat.
        intros. mlSimpl. cbn. exists (natVal 0).
        case_match.
        2: { unfold Minterp_inhabitant in n.
             unfold Sorts_Semantics.sym in n. clear H.
             eval_simpl_in n. cbn in n.
             unfold app_ext in n. rewrite elem_of_PropSet in n.
             exfalso. apply n. do 2 eexists. split_and!.
             1-2: by apply elem_of_singleton.
             cbn. apply elem_of_PropSet. by eexists.
           }
        remember (fresh_evar (Zero =ml b0)) as x. clear Heqx.
        unfold patt_equal, patt_total, patt_defined, mlFalse.
        repeat eval_simpl. cbn.
        rewrite decide_eq_same. unfold app_ext. eapply elem_of_compl.
        (* Unshelve. 2: exact (@propset_leibniz_equiv _ BoolModel). *)
        apply not_elem_of_PropSet. intro. destruct H0 as [le [re [Hle [Hre Ht] ] ] ].
        apply elem_of_singleton_1 in Hle. subst.
        apply (proj1 (elem_of_compl _ _)) in Hre; auto. apply Hre.
        set_solver.
      (* succ is functional - essentially same as for bnot *)
      - eval_simpl; auto.
        1: apply indec_nat.
        apply propset_fa_intersection_full. intros. case_match. 2: by reflexivity.
        pose proof sorted_exists_binder as BE. destruct BE as [BE].
        erewrite (BE _ (evar_open _)); eauto.
        mlSimpl. cbn.
        eval_simpl; auto. 1: apply indec_nat.
        remember (fresh_evar _) as X.
        remember (fresh_evar (Succ ⋅ patt_free_evar X =ml b0)) as Y.
        unfold Minterp_inhabitant in *.
        clear H. eval_simpl_in e.
        unfold app_ext in *.
        apply elem_of_PropSet in e.
        destruct e as [le [re [Hle [Hre Hlere] ] ] ].
        unfold Sorts_Semantics.sym in *.
        simp eval in *. simpl in *.
        unfold bool_sym_interp in *. apply elem_of_singleton in Hre, Hle.
        subst le re.
        assert (exists n, c = natVal n) by set_solver.
        assert (X <> Y) as HXY. {
          subst Y. clear.
          unfold fresh_evar. pose proof (X_eq_evar_fresh_impl_X_notin_S X (free_evars (Succ ⋅ patt_free_evar X =ml b0))).
          set_solver.
        }
        clear HeqX HeqY.
        destruct H; subst c.
        intros. exists (natVal (S x)).
        case_match.
        ** clear H e. mlSimpl. cbn.
           unfold Succ.
           revert t.
           apply propset_top_elem_of.
           eapply (equal_iff_interpr_same NatModel HDef). (* explicit model needed *)
           eval_simpl; auto. unfold app_ext. cbn.
           repeat destruct decide; try congruence.
           eapply set_eq. intros. rewrite elem_of_PropSet.
           split.
           -- intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
              unfold bool_sym_interp in *. apply elem_of_singleton in EQ1, EQ2.
              subst.
              unfold bool_app_interp in *.
              assumption.
           -- intros. do 2 eexists. split. 2: split.
              1-2: by apply elem_of_singleton.
              assumption.
        ** unfold Minterp_inhabitant, Sorts_Semantics.sym in n.
           simpl in n. clear H. simp eval in n. exfalso.
           apply n. clear. exists (inhNat), (coreNatSym sNat); split; try split.
           all: simpl; set_solver.
      (* no confusion *)
      - eval_simpl. apply indec_nat. 2: assumption.
        apply propset_fa_intersection_full. intros. case_match. 2: reflexivity.
        mlSimpl. cbn. remember (fresh_evar _) as x. clear Heqx.
        eval_simpl. eapply complement_full_iff_empty.
        apply (not_equal_iff_not_interpr_same_1 _ HDef).
        unfold Zero, Succ. simp eval. cbn. unfold app_ext.
        intro.
        assert (exists n, c = natVal n). {
          unfold Minterp_inhabitant, Sorts_Semantics.sym in e.
          clear H.
          simp eval in e. set_solver.
        }
        destruct H1. subst.
        eapply set_eq with (x := natVal 0) in H0.
        rewrite elem_of_singleton in H0.
        specialize (proj1 H0 eq_refl). clear.
        intro. apply elem_of_PropSet in H.
        destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
        rewrite decide_eq_same in EQ2. apply elem_of_singleton in EQ1, EQ2.
        subst. simpl in EQ3. set_solver.
      (* injectivity of succ *)
      - eval_simpl. apply indec_nat. 2: assumption.
        apply propset_fa_intersection_full. intros. case_match. 2: reflexivity.
        clear H.
        assert (exists n, c = natVal n) as [n ?]. {
          unfold Minterp_inhabitant, Sorts_Semantics.sym in e.
          eval_simpl_in e. set_solver.
        }
        clear e. subst. remember (fresh_evar _) as x. clear Heqx.
        mlSortedSimpl. mlSimpl. cbn.
        eval_simpl. 1: apply indec_nat. 2: assumption.
        eapply propset_fa_intersection_full. intros. case_match. 2: reflexivity.
        clear H.
        assert (exists n, c = natVal n) as [m ?]. {
          unfold Minterp_inhabitant, Sorts_Semantics.sym in e.
          eval_simpl_in e. set_solver.
        }
        clear e. subst. remember (fresh_evar _) as y.
        assert (x <> y). {
          subst y. clear.
          unfold fresh_evar. pose proof (X_eq_evar_fresh_impl_X_notin_S x (free_evars (Succ ⋅ patt_free_evar x =ml Succ ⋅ b0 ---> patt_free_evar x =ml b0))).
          set_solver.
        }
        clear Heqy. mlSimpl. cbn. unfold Succ.
        repeat eval_simpl.
        unfold patt_equal, patt_total, patt_defined.
        repeat eval_simpl.
        repeat rewrite update_evar_val_same.
        rewrite update_evar_val_neq. 2: auto.
        rewrite update_evar_val_same.
        (* These are manual steps *)
        assert (forall n, app_ext (sym_interp NatModel (inj sSucc)) {[natVal n]} = {[natVal (S n)]}). {
          intros. unfold app_ext.
          apply set_eq. intros. rewrite elem_of_PropSet. split; intro.
          + destruct H0 as [le [re [EQ1 [EQ2 EQ3] ] ] ].
            cbn in *.
            apply elem_of_singleton in EQ1, EQ2. subst.
            by cbn in EQ3.
          + do 2 eexists. cbn. split_and!. 1-2: by apply elem_of_singleton.
            by cbn.
        }
        do 2 rewrite H0.
        (* helper to rewrite: *)
        assert (forall (S1 S2 : propset NatModel), S2 = ∅ -> app_ext S1 S2 = ∅) as E.
        {
          intros. subst. apply app_ext_bot_r.
        }
        destruct (decide (n = m)).
        + subst.
          rewrite 2!E.
          (* TODO for some reason, set_solver won't work here *)
          2: {
            rewrite union_with_complement. clear.
            erewrite (subseteq_intersection_1_L ⊤ ⊤). 2: set_solver.
            erewrite difference_diag_L. reflexivity.
          }
          2: {
            rewrite union_with_complement. clear.
            erewrite (subseteq_intersection_1_L ⊤ ⊤). 2: set_solver.
            erewrite difference_diag_L. reflexivity.
          }
          rewrite difference_empty_L, difference_diag_L, union_empty_l_L.
          reflexivity.
        + rewrite 2! definedness_app_ext_not_empty; try assumption.
          all: set_solver.
      (* inductive domain *)
      - unfold patt_inhabitant_set, Sorts_Syntax.sym, Nat, Zero, Succ.
        apply equal_iff_interpr_same. 1: assumption.
        eval_simpl.
        remember (fresh_svar _) as X. simpl. unfold app_ext. clear HeqX.
        (* NOTE: reasoning about LeastFixpointOf is needed here *)
        rewrite set_eq_subseteq.
        split.
        {
          (* EQ3 is less than the LeastFixpoint *)
          apply elem_of_subseteq.
          intros. apply elem_of_PropSet in H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
          apply elem_of_singleton in EQ1, EQ2. subst. simpl in *.
          mlSimpl. cbn.
          unfold LeastFixpointOf, PrefixpointsOf.
          simpl. unfold propset_Meet.
          apply elem_of_PropSet. intros. destruct EQ3 as [n]. subst.
          apply (proj1 (elem_of_PropSet _ _)) in H. simpl in H.
          repeat eval_simpl_in H. simpl in H.
          rewrite decide_eq_same in H. clear -H.
          (* the key is in meta-induction here: *)
          induction n.
          * set_solver.
          * unfold app_ext in H.
            apply union_subseteq in H as [_ H].
            pose proof proj1 (elem_of_subseteq _ _) H as HEQ.
            apply HEQ.
            do 2 eexists. split_and!. by apply elem_of_singleton.
            exact IHn.
            simpl. set_solver.
        }
        {
          (* EQ3 is a Fixpoint *)
          apply (LeastFixpoint_LesserThanPrefixpoint _ _ (PowersetLattice (@Domain _ NatModel))).
          simpl in *. mlSimpl. cbn.
          repeat eval_simpl. simpl. rewrite decide_eq_same. unfold app_ext.
          apply elem_of_subseteq. intros.
          apply elem_of_union in H as [|]. (* 0 or succ n? *)
          - do 2 eexists. split_and!. 1-2: by apply elem_of_singleton.
            simpl. set_solver.
          - destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
            destruct EQ2 as [le2 [re2 [EQ12 [EQ22 EQ32] ] ] ].
            apply elem_of_singleton in EQ1, EQ12, EQ22. subst.
            simpl in *.
            destruct re. 1-2,4-5: set_solver.
            do 2 eexists. split_and!. 1-2: by apply elem_of_singleton.
            simpl. set_solver.
        }
      (* add is functional *)
      - (* 1st sorted forall *)
        eval_simpl. 1: apply indec_nat. 2: assumption.
        apply propset_fa_intersection_full. intros.
        case_match. 2: reflexivity.
        pose proof sorted_forall_binder as BF. destruct BF as [BF].
        pose proof sorted_exists_binder as BE. destruct BE as [BE].
        erewrite (BF _ (evar_open _)); eauto.
        erewrite (BE _ (evar_open _)); eauto.
        mlSimpl. cbn.
        remember (fresh_evar _) as x. clear Heqx.
        (* 2nd sorted forall *)
        eval_simpl. 1: apply indec_nat. 2: assumption.
        apply propset_fa_intersection_full. intros.
        case_match. 2: reflexivity.
        erewrite (BE _ (evar_open _)); eauto.
        mlSimpl. cbn. remember (fresh_evar _) as y.
        assert (x <> y). {
          subst y. clear.
          pose proof (X_eq_evar_fresh_impl_X_notin_S x (free_evars (patt_exists_of_sort Nat (mlAddNat b1 (patt_free_evar x) =ml b0)))).
          set_solver.
        }
        clear Heqy.
        (* sorted exists *)
        eval_simpl. 1: apply indec_nat. 2: assumption. intros.
        (* For this, we need that c and c0 are nats *)
        clear H H0.
        assert (exists n, c = natVal n). {
          clear -e.
          unfold Minterp_inhabitant, Sorts_Semantics.sym in e.
          eval_simpl_in e. set_solver.
        }
        assert (exists n, c0 = natVal n). {
          clear -e0.
          unfold Minterp_inhabitant, Sorts_Semantics.sym in e0.
          eval_simpl_in e0. set_solver.
        }
        destruct H as [n ?], H0 as [m ?]. subst.
        exists (natVal (m + n)). case_match.
        + clear H e1.
          remember (fresh_evar _) as z.
          assert (z <> x /\ z <> y) as [X2 X3]. {
            subst z. clear.
            pose proof (X_eq_evar_fresh_impl_X_notin_S x (free_evars (mlAddNat (patt_free_evar y) (patt_free_evar x) =ml b0))).
            pose proof (X_eq_evar_fresh_impl_X_notin_S y (free_evars (mlAddNat (patt_free_evar y) (patt_free_evar x) =ml b0))).
            set_solver. (* this is slow for some reason *)
          }
          clear Heqz.
          mlSimpl. cbn.
          unfold mlAddNat, AddNat.
          assert (forall S : propset nat_carrier, S = ⊤ -> forall t, t ∈ S) as HX. {
            set_solver.
          }
          apply HX.
          eapply (@equal_iff_interpr_same _ _ NatModel). assumption.
          eval_simpl. unfold app_ext.
          repeat rewrite update_evar_val_same.
          rewrite update_evar_val_neq. 2: by auto.
          rewrite update_evar_val_same.
          rewrite update_evar_val_neq. 2: by auto.
          rewrite update_evar_val_neq. 2: by auto.
          rewrite update_evar_val_same.
          apply set_eq; split.
          ** intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
             destruct EQ1 as [le2 [re2 [EQ12 [EQ22 EQ32] ] ] ]. simpl in *.
             apply elem_of_singleton in EQ22, EQ2, EQ12. subst.
             simpl in *.
             apply elem_of_singleton in EQ32. subst.
             by simpl in EQ3.
          ** intros. do 2 eexists. split_and!.
             do 2 eexists. split_and!.
             all: cbn.
             all: try by apply elem_of_singleton.
        + clear H. exfalso. apply n0. clear.
          unfold Minterp_inhabitant, Sorts_Semantics.sym. eval_simpl.
          do 2 eexists. split_and!. 1-2: cbn; by apply elem_of_singleton.
          cbn. set_solver.
      (* add rule 1 *)
      - eval_simpl. 1: apply indec_nat. 2: assumption.
        apply propset_fa_intersection_full. intros.
        case_match. 2: reflexivity. clear H.
        assert (exists n, c = natVal n). {
          clear -e.
          unfold Minterp_inhabitant, Sorts_Semantics.sym in e.
          eval_simpl_in e. set_solver.
        }
        destruct H as [n ?]. subst.
        clear e.
        mlSimpl. cbn. remember (fresh_evar _) as x. clear Heqx.
        unfold mlAddNat, AddNat, Zero.
        apply (@equal_iff_interpr_same _ _ NatModel). assumption.
        eval_simpl. simpl. rewrite decide_eq_same.
        unfold app_ext.
        apply set_eq; split.
        ** intros. destruct H as [le [re [EQ1 [EQ2 EQ3] ] ] ].
           destruct EQ1 as [le2 [re2 [EQ12 [EQ22 EQ32] ] ] ]. simpl in *.
           apply elem_of_singleton in EQ22, EQ2, EQ12. subst.
           simpl in *.
           apply elem_of_singleton in EQ32. subst.
           simpl in EQ3.
           (* trick here: *)
           by rewrite Nat.add_0_r in EQ3.
        ** intros. do 2 eexists. split_and!.
           do 2 eexists. split_and!.
           all: cbn.
           all: try by apply elem_of_singleton.
           (* trick here: *)
           simpl. by rewrite Nat.add_0_r.
        (* the tricks above were needed, because Coq's nat operations are defined
           with recursion on the left argument, not the right one -

           Similar tricks are needed in the next subgoal *)
      (* add rule 2 *)
      - eval_simpl. 1: apply indec_nat. 2: assumption.
        apply propset_fa_intersection_full. intros.
        case_match. 2: reflexivity. clear H.
        assert (exists n, c = natVal n). {
          clear -e.
          unfold Minterp_inhabitant, Sorts_Semantics.sym in e.
          eval_simpl_in e. set_solver.
        }
        destruct H as [n ?]. subst.
        clear e.
        remember (fresh_evar _) as x. clear Heqx.
        mlSortedSimpl. mlSimpl. cbn.
        (* 2nd sorted forall *)
        eval_simpl. 1: apply indec_nat. 2: assumption.
        apply propset_fa_intersection_full. intros.
        case_match. 2: reflexivity. clear H.
        assert (exists n, c = natVal n). {
          clear -e.
          unfold Minterp_inhabitant, Sorts_Semantics.sym in e.
          eval_simpl_in e. set_solver.
        }
        destruct H as [m ?]. subst.
        clear e.
        remember (fresh_evar _) as y.
        assert (x <> y). {
          subst y. clear.
          pose proof (X_eq_evar_fresh_impl_X_notin_S x (free_evars (mlAddNat b0 (Succ ⋅ patt_free_evar x) =ml Succ ⋅ mlAddNat b0 (patt_free_evar x)))).
          set_solver.
        }
        clear Heqy.
        mlSimpl. cbn.
        unfold mlAddNat, AddNat, Succ.
        apply (@equal_iff_interpr_same _ _ NatModel). assumption.
        eval_simpl. simpl.
        repeat rewrite decide_eq_same.
        case_match. congruence. unfold app_ext.
        apply set_eq; split; intro X; destruct X as [le [re [EQ1 [EQ2 EQ3] ] ] ];
          simpl in *.
        ** destruct EQ1 as [le2 [re2 [EQ12 [EQ22 EQ32] ] ] ],
                    EQ2 as [le3 [re3 [EQ13 [EQ23 EQ33] ] ] ].
           apply elem_of_singleton in EQ23, EQ13, EQ22, EQ12. subst.
           simpl in *.
           apply elem_of_singleton in EQ32, EQ33. subst.
           simpl in *.
           do 2 eexists. split_and!.
           2: do 2 eexists; split_and!.
           2: do 2 eexists; split_and!.
           all: try by apply elem_of_singleton.
           simpl.
           (* trick *)
           by rewrite PeanoNat.Nat.add_succ_r in EQ3.
        ** destruct EQ2 as [le2 [re2 [EQ12 [EQ22 EQ32] ] ] ].
           destruct EQ12 as [le3 [re3 [EQ13 [EQ23 EQ33] ] ] ].
           apply elem_of_singleton in EQ13, EQ23, EQ22, EQ1. subst.
           simpl in *.
           destruct re. 1-2,4-5: set_solver.
           apply elem_of_singleton in EQ33, EQ3. subst.
           simpl in *.
           do 2 eexists. split_and!.
           1-2: do 2 eexists; split_and!.
           all: simpl; try by apply elem_of_singleton.
           simpl.
           (* trick - although, set_solver also used n1 = m + n -> S n1 = S (m + n)*)
           rewrite PeanoNat.Nat.add_succ_r.
           set_solver.
  Qed.

End Nat.



(*

  Q: What happens to the signatures when importing a theory into another?
  How to handle diamond dependencies in the syntax? For example
  definedness is in Nat and Bool signatures too, how should we handle it
  in the glued signature?

  1. Do nothing, just use union, and add theory-level axioms saying that the
     different definedness symbols are equal/interchangable.
  2. Only define signature specific symbols (e.g., 0, succ, +), and inject
     definedness and others.
  3. Use a binary relation which expresses which symbols are repeated. Then use
     union to express the signature, but tag each symbol (of one of the signatures)
     with a proof based on this relation that it is unique.

 *)
Require Import ModelExtension.

Inductive extend_def_inh {A B : Set} : Set :=
| inj_def
| inj_inh
| fromA (a : A)
| fromB (b : B).

Program Definition signature_fusion
        (Σ1 Σ2 : Signature)
        (* (def1 inh1 : @symbols (@ml_symbols Σ1))
        (def2 inh2 : @symbols (@ml_symbols Σ2)) *)
        (* (R : @symbols (@ml_symbols Σ1) -> @symbols (@ml_symbols Σ2) -> bool) *)
          : Signature :=
{|
  variables := StringMLVariables;
  ml_symbols := {|
    symbols := @extend_def_inh (@symbols (@ml_symbols Σ1)) (@symbols (@ml_symbols Σ2))
  |};
|}
.
Next Obligation.
  intros. solve_decision.
Defined.
Next Obligation.
  intros. admit.
Admitted. (* technical *)


Section BoolNat.

(* common carrier *)
(*   Definition bool_nat_carrier : Set := bool_carrier + nat_carrier.

  #[global]
  Instance bool_nat_carrier_EqDec : EqDecision bool_nat_carrier.
  Proof.
    solve_decision.
  Defined.

  Global Instance bool_nat_carrier_countable : countable.Countable bool_nat_carrier.
  Proof.
    by apply sum_countable.
  Defined.

  Global Instance bool_nat_carrier_inhabited : Inhabited bool_nat_carrier.
  Proof.
    constructor. constructor. constructor. constructor.
  Defined. *)

  (* common signature *)

  Instance nat_bool_Σ : Signature := signature_fusion nat_Σ bools_Σ.

  (*
    Here, we say that we use the new definedness
  *)
  Program Instance nat_bool_syntax_bool_part : @Bool_Syntax.Syntax nat_bool_Σ := {
    inj := fromB ∘ coreBoolSym;
    imported_sorts := {|
      Sorts_Syntax.inj := fun x => inj_inh;
      imported_definedness := {|
        Definedness_Syntax.inj := fun x => inj_def;
      |};
    |};
  }.

  Program Instance nat_bool_syntax_nat_part : @Nat_Syntax.Syntax nat_bool_Σ := {
    inj := fromA ∘ coreNatSym;
    imported_sorts := {|
      Sorts_Syntax.inj := fun x => inj_inh;
      imported_definedness := {|
        Definedness_Syntax.inj := fun x => inj_def;
      |};
    |};
  }.

  Check @patt_defined nat_bool_Σ _ patt_bott.
  Check @patt_defined bools_Σ (@imported_definedness bools_Σ
     (@imported_sorts bools_Σ bool_syntax)) patt_bott.
  Check @patt_defined nat_Σ _ patt_bott.

  (* Model extension's new_sym_interp does not define meaning to new symbols! *)
  Fail Definition nat_bool_sym_interp (s : @symbols (@ml_symbols nat_bool_Σ))
     : propset (Carrier NatModel bool_carrier) :=
   new_sym_interp NatModel bool_carrier.

  Definition nat_bool_app_interp := new_app_interp.

  Print nat_bool_app_interp.

End BoolNat.
