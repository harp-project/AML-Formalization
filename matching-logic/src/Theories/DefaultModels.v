 From Coq Require Import String Ensembles Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import FunctionalExtensionality Eqdep_dec.
From Coq.Classes Require Import Morphisms_Prop.
From Coq.Unicode Require Import Utf8.
From Coq.micromega Require Import Lia.
From Equations Require Import Equations.

From MatchingLogic Require Import Logic.
Import MatchingLogic.Logic.Notations.
From MatchingLogic.Utils Require Import Lattice stdpp_ext extralibrary.

From stdpp Require Import base fin_sets sets propset proof_irrel option list finite.

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

Section Definedness.

  Context {Σ : Signature} {M : Model}
          {string_vars : variables = StringMLVariables}.

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
    * rewrite elem_of_PropSet in H. destruct H as [le [re [Hle [Hre Hx] ] ] ].
      destruct Hle. destruct Hre. by simpl in Hx.
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
  | inr (), inr ()       => ∅ (* inh $ inh *)
  | inr (), inl (inr ()) => ∅ (* inh $ def *)
  | inr (), inl (inl x)  =>   (* inh $ x *)
        (inl ∘ inl) <$> (sort_interp x)
  | inl (inr _), inr _   => ⊤ (* ⌈ ⌉ $ inh <- Notion of definedness has to be extended *)
  | inl (inr _), inl _   => ⊤ (* ⌈ ⌉ $ x <- Notion of definedness has to be extended *)
  | inl (inl _), inr _   => ∅ (* x $ inh *)
  | inl x1, inl x2       =>   (* x $ y*)
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
  Inductive bool_carrier :=
  | coreBoolSym (s : Bool_Syntax.Symbols)
  | partialAnd (b : bool)
  | partialAndThen (b : option bool)
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

  Definition bool_sym_interp (m : symbols)
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
   (* TODO: revise these! Probably they are incorrect *)
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
             assert (forall S : propset bool_carrier, S = ⊤ -> forall t, t ∈ S) as HX. {
               set_solver.
             }
             apply HX. clear HX.
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
             assert (forall S : propset bool_carrier, S = ⊤ -> forall t, t ∈ S) as HX. {
               set_solver.
             }
             apply HX. clear HX.
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
             assert (forall S : propset bool_carrier, S = ⊤ -> forall t, t ∈ S) as HX. {
               set_solver.
             }
             apply HX. clear HX.
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
             assert (forall S : propset bool_carrier, S = ⊤ -> forall t, t ∈ S) as HX. {
               set_solver.
             }
             apply HX. clear HX.
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
             assert (forall S : propset bool_carrier, S = ⊤ -> forall t, t ∈ S) as HX. {
               set_solver.
             }
             apply HX. clear HX.
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
             assert (forall S : propset bool_carrier, S = ⊤ -> forall t, t ∈ S) as HX. {
               set_solver.
             }
             apply HX. clear HX.
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

  Inductive nat_carrier :=
  | coreNatSym (s : Nat_Syntax.Symbols)
  | partialAdd (s : nat)
  | natVal (n : nat)
  | defNat
  | inhNat
  .

  #[global]
  Instance nat_carrier_EqDec : EqDecision nat_carrier.
  Proof.
    solve_decision.
  Defined.

  Global Program Instance nat_carrier_countable : countable.Countable nat_carrier. (* := {
    encode := fun (n : nat_carrier) =>
      match n with
      | coreNatSym s =>
        match s with
         | sNat => 1%positive
         | sZero => 2%positive
         | sSucc => 3%positive
         | sAddNat => 4%positive
        end
      | partialAdd n => (7%positive + @encode _ _ nat_countable n)%positive
      | defNat => 5%positive
      | inhNat => 6%positive
      end;
    decode := fun (p : positive) =>
      if      (Pos.eqb p 1) then Some (coreNatSym sNat)
      else if (Pos.eqb p 2) then Some (coreNatSym sZero)
      else if (Pos.eqb p 3) then Some (coreNatSym sSucc)
      else if (Pos.eqb p 4) then Some (coreNatSym sAddNat)
      else if (Pos.eqb p 5) then Some defNat
      else if (Pos.eqb p 6) then Some inhNat
      else match (@decode _ _ nat_countable (p-7)) with
           | Some n => Some (partialAdd n)
           | _ => None
           end;
  }.
  Next Obligation.
    intros. subst wildcard'. congruence.
  Defined.
  Next Obligation.
    destruct x; simpl; try reflexivity.
    destruct s; simpl; try reflexivity.
  Admitted. *)
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

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
    admit.
  Admitted.

  Hint Resolve propset_leibniz_equiv : core.

  Theorem NatModel_satisfies_theory :
    NatModel ⊨ᵀ Nat_Syntax.theory.
  Proof.
    assert (NatModel ⊨ᵀ Definedness_Syntax.theory) as HDef. {
      unfold Nat_Syntax.theory, Definedness_Syntax.theory.
      unfold theory_of_NamedAxioms. simpl.
      unfold satisfies_theory. intros.
      rewrite elem_of_PropSet in H. destruct H. destruct x. subst.
      cbn. unfold satisfies_model. intros.
      unfold patt_defined. unfold p_x, ev_x. simp eval.
      unfold sym_interp, app_ext. simpl.
      eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ NatModel).
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
      eapply leibniz_equiv. Unshelve. 2: exact (@propset_leibniz_equiv _ NatModel).
      apply set_equiv. intros. split; intros; set_solver.
    * rewrite elem_of_PropSet in H. destruct H.
      destruct x;subst;cbn; unfold satisfies_model; intros.
      (* zero is functional *)
      - eval_simpl; auto. apply indec_nat.
        intros. mlSimpl. cbn. exists (coreNatSym sNat).
        case_match.
        2: { unfold Minterp_inhabitant in n.
             unfold Sorts_Semantics.sym in n.
             
      (* succ is functional *)
      -
      (* no confusion *)
      -
      (* injectivity of succ *)
      -
      (* inductive domain *)
      -
      (* add is functional *)
      -
      (* add rule 1 *)
      -
      (* add rule 2 *)
      -
  Qed.

End Nat.

