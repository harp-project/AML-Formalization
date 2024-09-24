From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Logic.Classical_Prop Coq.Logic.FunctionalExtensionality.

From stdpp
Require Import
    base
    decidable
    propset
    fin_maps
    fin_sets
.

From MatchingLogic
Require Import
    Utils.extralibrary
    Utils.stdpp_ext
    Pattern
    Syntax
    Semantics
    DerivedOperators_Syntax
    DerivedOperators_Semantics
    PrePredicate
    monotonic
    Theories.Definedness_Syntax
    Theories.Definedness_Semantics
    Theories.Sorts_Syntax
    Theories.Sorts_Semantics
.


Import MatchingLogic.Logic.Notations.
Import MatchingLogic.Semantics.Notations.



Section glue_models.

  Context (Σ1 : Signature)
          (Σ2 : Signature)
          {HVars : @variables Σ1 = @variables Σ2}.

  Definition glued_sig_of : Signature :=
  {|
    variables := @variables Σ1;
    ml_symbols := {|
      symbols := @symbols (@ml_symbols Σ1) + @symbols (@ml_symbols Σ2)
    |};
  |}.

  

End glue_models.











Section with_syntax.
    Context
        {Σ : Signature}
        (* TODO: maybe remove and use the imported one from Sorts_Syntax? *)
        {ds : Definedness_Syntax.Syntax}
        {ss : Sorts_Syntax.Syntax}
        (HSortImptDef : imported_definedness = ds)
        (HDefNeqInh : Definedness_Syntax.inj definedness <> Sorts_Syntax.inj inhabitant)
    .
    Open Scope ml_scope.

    Definition is_core_symbol (s : symbols) : Prop
        := s = Definedness_Syntax.inj definedness \/ s = Sorts_Syntax.inj inhabitant.


    Instance is_core_symbol_dec (s : symbols) : Decision (is_core_symbol s).
    Proof. solve_decision. Defined.

    Definition is_not_core_symbol (s : symbols) : Prop
        := ~ is_core_symbol s.

    Instance is_not_core_symbol_dec (s : symbols) : Decision (is_not_core_symbol s).
    Proof. solve_decision. Defined.



    Inductive is_SPredicate
    : Pattern -> Prop :=
    | spred_bott
        : is_SPredicate patt_bott
    | spred_def (ϕ : Pattern)
        : is_SData ϕ -> is_SPredicate (patt_defined ϕ)
    (* note that we have to add equality and subseteq manually,
       since they are usually defined using totality,
       and we do not have totality in the fragment!
     *)
    | spred_eq (ϕ₁ ϕ₂ : Pattern)
        : is_SData ϕ₁ -> is_SData ϕ₂ -> is_SPredicate (patt_equal ϕ₁ ϕ₂)
    | spred_subseteq (ϕ₁ ϕ₂ : Pattern)
        : is_SData ϕ₁ -> is_SData ϕ₂ -> is_SPredicate (patt_subseteq ϕ₁ ϕ₂)
    | spred_imp (ϕ₁ ϕ₂ : Pattern)
        : is_SPredicate ϕ₁ -> is_SPredicate ϕ₂ -> is_SPredicate (patt_imp ϕ₁ ϕ₂)
    | spred_ex (ϕ : Pattern) (s : symbols)
        : is_SPredicate ϕ -> is_not_core_symbol s -> is_SPredicate (patt_exists_of_sort (patt_sym s) ϕ)
    | spred_all (ϕ : Pattern) (s : symbols)
        : is_SPredicate ϕ -> is_not_core_symbol s -> is_SPredicate (patt_forall_of_sort (patt_sym s) ϕ)
    with is_SData
    : Pattern -> Prop :=
    | sdata_bott
        : is_SData patt_bott
    | sdata_fevar (x : evar)
        : is_SData (patt_free_evar x)
    | sdata_fsvar (X : svar)
        : is_SData (patt_free_svar X)
    | sdata_bevar (dbi : db_index)
        : is_SData (patt_bound_evar dbi)
    | sdata_bsvar (dbi : db_index)
        : is_SData (patt_bound_svar dbi)
    | sdata_sym (s : symbols)
        : is_not_core_symbol s -> is_SData (patt_sym s)
    | sdata_inh (s : symbols)
        : is_not_core_symbol s -> is_SData (patt_inhabitant_set (patt_sym s))
    | sdata_sneg (ϕ : Pattern) (s : symbols)
        : is_SData ϕ -> is_not_core_symbol s -> is_SData (patt_sorted_neg (patt_sym s) ϕ)
    | sdata_app (ϕ₁ ϕ₂ : Pattern)
        : is_SData ϕ₁ -> is_SData ϕ₂ -> is_SData (patt_app ϕ₁ ϕ₂)
    | sdata_or (ϕ₁ ϕ₂ : Pattern)
        : is_SData ϕ₁ -> is_SData ϕ₂ -> is_SData (patt_or ϕ₁ ϕ₂)
    | sdata_filter (ϕ ψ : Pattern)
        : is_SData ϕ -> is_SPredicate ψ -> is_SData (patt_and ϕ ψ)
    | sdata_ex (ϕ : Pattern) (s : symbols)
        : is_SData ϕ -> is_not_core_symbol s -> is_SData (patt_exists_of_sort (patt_sym s) ϕ)
    (* This is disabled, because if the sort is empty, then the forall evaluates to full set,
       and that does not get lifted to full set in the extended model.
     *)
    (*
    | sdata_all (ϕ : Pattern) (s : symbols)
        : is_SData ϕ -> is_not_core_symbol s -> is_SData (patt_forall_of_sort (patt_sym s) ϕ)
    *)
    | sdata_mu (ϕ : Pattern)
        : is_SData ϕ -> is_SData (patt_mu ϕ)
    .

    Lemma is_SData_bevar_subst ϕ₁ ϕ₂ dbi:
        is_SData ϕ₁ ->
        is_SData ϕ₂ ->
        is_SData (ϕ₁^[evar: dbi ↦ ϕ₂])
    with is_SPredicate_bevar_subst ψ ϕ₂ dbi:
        is_SPredicate ψ ->
        is_SData ϕ₂ ->
        is_SPredicate (ψ^[evar: dbi ↦ ϕ₂])
    .
    Proof.
        {
            intros H1 H2.
            induction H1; simpl; try constructor; auto.
            {
                case_match.
                { constructor. }
                { assumption. }
                { constructor. }
            }
        }
        {
            intros H1 H2.
            induction H1; try (solve [simpl; try constructor; auto]).
        }
    Qed.

    Lemma is_SData_evar_open x ϕ:
        is_SData ϕ ->
        is_SData (ϕ^{evar: 0 ↦ x}).
    Proof.
        intros H.
        unfold evar_open.
        apply is_SData_bevar_subst.
        { assumption. }
        constructor.
    Qed.

    Lemma is_SPredicate_evar_open x ϕ:
        is_SPredicate ϕ ->
        is_SPredicate (ϕ^{evar: 0 ↦ x}).
    Proof.
        intros H.
        unfold evar_open.
        apply is_SPredicate_bevar_subst.
        { assumption. }
        constructor.
    Qed.

    Lemma is_SData_bsvar_subst ϕ₁ ϕ₂ dbi:
        is_SData ϕ₁ ->
        is_SData ϕ₂ ->
        is_SData (ϕ₁^[svar: dbi ↦ ϕ₂])
    with is_SPredicate_bsvar_subst ψ ϕ₂ dbi:
        is_SPredicate ψ ->
        is_SData ϕ₂ ->
        is_SPredicate (ψ^[svar: dbi ↦ ϕ₂])
    .
    Proof.
        {
            intros H1 H2.
            induction H1; simpl; try constructor; auto.
            {
                case_match.
                { constructor. }
                { assumption. }
                { constructor. }
            }
        }
        {
            intros H1 H2.
            induction H1; try (solve [simpl; try constructor; auto]).
        }
    Qed.

    Lemma is_SData_svar_open x ϕ:
        is_SData ϕ ->
        is_SData (ϕ^{svar: 0 ↦ x}).
    Proof.
        intros H.
        unfold evar_open.
        apply is_SData_bsvar_subst.
        { assumption. }
        constructor.
    Qed.

    Lemma is_SPredicate_svar_open x ϕ:
        is_SPredicate ϕ ->
        is_SPredicate (ϕ^{svar: 0 ↦ x}).
    Proof.
        intros H.
        unfold evar_open.
        apply is_SPredicate_bsvar_subst.
        { assumption. }
        constructor.
    Qed.

    Lemma is_SPredicate_patt_not (ϕ : Pattern) :
        is_SPredicate ϕ ->
        is_SPredicate (patt_not ϕ).
    Proof.
        intros H.
        unfold patt_not.
        apply spred_imp.
        { assumption. }
        { apply spred_bott. }
    Qed.

(*
    Lemma is_SPredicate_forall_of_sort (s : symbols) (ϕ : Pattern)  :
        is_SPredicate (patt_forall_of_sort (patt_sym s) ϕ).
    Proof.
        unfold patt_forall_of_sort,patt_forall.
        apply is_SPredicate_patt_not.
    Qed.
*)
    Section ext.
        Context
            (M : @Model Σ)
            (indec : forall (s : symbols),
              is_not_core_symbol s ->
              forall (m : Domain M) ρ,
              Decision (m ∈ Minterp_inhabitant (patt_sym s) ρ))
            (R : Type)
            (new_sym_interp : @symbols (@ml_symbols Σ) -> propset (Domain M + R)%type)
            (fRM : R -> (Domain M) -> propset (Domain M + R)%type)
            (fMR : (Domain M) -> R -> propset (Domain M + R)%type)
            (fRR : R -> R -> propset (Domain M + R)%type)
            (finh : R -> propset (Domain M + R)%type)
        .

    Inductive Carrier := cdef | cinh | cel (el: (Domain M + R)%type).

    Instance Carrier_inhabited : Inhabited Carrier := populate cdef.

    Definition new_app_interp (x y : Carrier) : propset Carrier :=
        match x with
        | cdef =>
            ⊤
        | cinh =>
            match y with
            | cdef => ∅
            | cinh => ∅
            | cel el =>
                match el with
                | inl m =>
                    cel <$> (@fmap propset _ _ _ inl (@app_ext _ M (sym_interp M (Sorts_Syntax.inj inhabitant)) {[m]}))
                | inr r =>
                    cel <$> finh r
                end
            end
        | cel elx =>
            match y with
            | cdef => ∅
            | cinh => ∅
            | cel ely =>
                match elx,ely with
                | (inl mx),(inl my) =>
                    cel <$> (@fmap propset _ _ _ inl (@app_interp _ M mx my))
                | (inl mx),(inr ry) =>
                    cel <$> (fMR mx ry)
                | (inr rx),(inl my) =>
                    cel <$> (fRM rx my)
                | (inr rx),(inr ry) =>
                    cel <$> (fRR rx ry)
                end
            end
        end.

    Definition new_sym_interp' (s : symbols) : propset Carrier :=
        match (decide (s = Definedness_Syntax.inj definedness)) with
        | left _ => {[ cdef ]}
        | right _ =>
            match (decide (s = Sorts_Syntax.inj inhabitant)) with
            | left _ => {[ cinh ]}
            | right _ => cel <$> new_sym_interp s (* cel <$> (@fmap propset _ _ _ inl (@sym_interp _ M s)) *)
            end
        end.

    (* TODO: why was this polimorphic? *)
    Definition Mext : Model :=
        {|
            Domain := Carrier ;
            Domain_inhabited := Carrier_inhabited ;
            app_interp := new_app_interp ;
            sym_interp := new_sym_interp ;
        |}.

    Lemma Mext_satisfies_definedness : Mext ⊨ᵀ Definedness_Syntax.theory.
    Proof.
        unfold theory.
        apply satisfies_theory_iff_satisfies_named_axioms.
        intros na. destruct na.
        apply single_element_definedness_impl_satisfies_definedness.
        exists cdef.
        simpl. split.
        {
            unfold new_sym_interp'. case_match.
            { reflexivity. }
            contradiction n. reflexivity.
        }
        {
            auto.
        }
    Qed.

    Definition lift_value (x : Domain M) : (Domain Mext)
    := cel (inl x).

    Definition lift_set (xs : propset (Domain M)) : (propset (Domain Mext))
    := cel <$> (@fmap propset _ _ _ inl xs).

    (* Valuations lifted from the original model to the extended model. *)
    Definition lift_val (ρ : @Valuation Σ M) : 
      (@Valuation Σ Mext)
    := {|
         evar_valuation := λ (x : evar), lift_value (evar_valuation ρ x);
         svar_valuation := λ (X : svar), lift_set (svar_valuation ρ X)
       |}.

    Lemma lift_set_mono (xs ys : propset (Domain M)) :
        xs ⊆ ys <->
        lift_set xs ⊆ lift_set ys.
    Proof.
        unfold lift_set,fmap.
        with_strategy transparent [propset_fmap] unfold propset_fmap.
        split.
        {
            intros H.
            clear -H. set_solver.
        }
        {
            intros H.
            rewrite elem_of_subseteq in H.
            rewrite elem_of_subseteq.
            intros x Hx.
            specialize (H (lift_value x)).
            unfold lift_value in H.
            do 2 rewrite elem_of_PropSet in H.
            ospecialize* H.
            {
                exists (inl x).
                split;[reflexivity|].
                rewrite elem_of_PropSet.
                exists x.
                split;[reflexivity|].
                exact Hx.
            }
            destruct H as [a [Ha H] ].
            inversion Ha. clear Ha. subst.
            rewrite elem_of_PropSet in H.
            destruct H as [a [Ha H] ].
            inversion Ha. clear Ha. subst.
            exact H.
        }
    Qed.

    Lemma lift_set_injective (xs ys : propset (Domain M)) :
        xs = ys <-> lift_set xs = lift_set ys.
    Proof.
        split;[congruence|].
        intros H.
        unfold lift_set,fmap in H.
        with_strategy transparent [propset_fmap] unfold propset_fmap in H.
        unfold_leibniz.
        rewrite set_equiv_subseteq in H.
        do 2 rewrite elem_of_subseteq in H.
        destruct H as [H1 H2].
        rewrite set_equiv_subseteq.
        do 2 rewrite elem_of_subseteq.
        split; intros x Hx.
        {
            specialize (H1 (lift_value x)).
            do 2 rewrite elem_of_PropSet in H1.
            ospecialize* H1.
            {
                unfold lift_value.
                exists (inl x).
                split;[reflexivity|].
                rewrite elem_of_PropSet.
                exists x.
                split;[reflexivity|].
                apply Hx.
            }
            destruct H1 as [a [Ha H1] ].
            unfold lift_value in Ha.
            inversion Ha. clear Ha. subst. 
            rewrite elem_of_PropSet in H1.
            destruct H1 as [a [Ha H1] ].
            inversion Ha. clear Ha. subst.
            exact H1.
        }
        {
            specialize (H2 (lift_value x)).
            do 2 rewrite elem_of_PropSet in H2.
            ospecialize* H2.
            {
                unfold lift_value.
                exists (inl x).
                split;[reflexivity|].
                rewrite elem_of_PropSet.
                exists x.
                split;[reflexivity|].
                apply Hx.
            }
            destruct H2 as [a [Ha H2] ].
            unfold lift_value in Ha.
            inversion Ha. clear Ha. subst. 
            rewrite elem_of_PropSet in H2.
            destruct H2 as [a [Ha H2] ].
            inversion Ha. clear Ha. subst.
            exact H2.
        }
    Qed.

    Lemma Mext_indec :
        forall (s : symbols),
            is_not_core_symbol s ->
            forall (m : Domain Mext) ρ,
            Decision (m ∈ @Minterp_inhabitant Σ _ Mext (patt_sym s) (lift_val ρ)).
    Proof.
        intros. unfold Minterp_inhabitant.
        rewrite eval_app_simpl.
        unfold app_ext,lift_val. simpl.
        destruct m.
        {
            right. intros HContra.
            rewrite elem_of_PropSet in HContra.
            destruct HContra as [le [re [HContra1 [HContra2 HContra3] ] ] ].
            rewrite eval_sym_simpl in HContra1.
            rewrite eval_sym_simpl in HContra2.
            simpl in HContra1.
            simpl in HContra2.
            unfold new_sym_interp in HContra1, HContra2.
            unfold new_app_interp in HContra3.
            repeat case_match; subst; auto; try set_solver.
        }
        {
            right. intros HContra.
            rewrite elem_of_PropSet in HContra.
            destruct HContra as [le [re [HContra1 [HContra2 HContra3] ] ] ].
            rewrite eval_sym_simpl in HContra1.
            rewrite eval_sym_simpl in HContra2.
            simpl in HContra1.
            simpl in HContra2.
            unfold new_sym_interp in HContra1, HContra2.
            unfold new_app_interp in HContra3.
            repeat case_match; subst; auto; try set_solver.
        }
        destruct el.
        2: {
            right. intros HContra.
            rewrite elem_of_PropSet in HContra.
            destruct HContra as [le [re [HContra1 [HContra2 HContra3] ] ] ].
            rewrite eval_sym_simpl in HContra1.
            rewrite eval_sym_simpl in HContra2.
            simpl in HContra1.
            simpl in HContra2.
            unfold new_sym_interp in HContra1, HContra2.
            unfold new_app_interp in HContra3.
            repeat case_match; subst; auto; try set_solver.
        }
        destruct (indec _ H d ρ) as [Hin|Hnotin].
        {
            left.
            unfold Minterp_inhabitant in Hin.
            rewrite eval_app_simpl in Hin.
            do 2 rewrite eval_sym_simpl in Hin.
            unfold app_ext in Hin.
            rewrite elem_of_PropSet in Hin.
            destruct Hin as [le [re [Hinle [Hinre Hin] ] ] ].
            rewrite elem_of_PropSet.

            do 2 rewrite eval_sym_simpl.
            simpl.
            unfold new_sym_interp.
            repeat case_match; subst; auto; try contradiction; try congruence;
            unfold lift_value.
            { exfalso. apply H. unfold is_core_symbol. left. reflexivity. }
            { exfalso. apply H. unfold is_core_symbol. right. reflexivity. }

            exists cinh, (lift_value re).
            split;[set_solver|].
            unfold lift_value,new_app_interp.
            split;[set_solver|].
            unfold app_ext.
            clear -Hinle Hinre Hin.
            set_solver.
        }
        {
            right.
            unfold Minterp_inhabitant in Hnotin.
            rewrite eval_app_simpl in Hnotin.
            do 2 rewrite eval_sym_simpl in Hnotin.
            unfold app_ext in Hnotin.
            rewrite elem_of_PropSet in Hnotin.
            rewrite elem_of_PropSet.
            intro HContra. apply Hnotin.
            do 2 rewrite eval_sym_simpl in HContra.
            simpl in HContra. unfold new_sym_interp in HContra.
            destruct HContra as [le [re [Hinle [Hinre Hin] ] ] ].


            repeat case_match; subst; auto; try contradiction; try congruence;
            unfold lift_value.
            { exfalso. apply H. unfold is_core_symbol. left. reflexivity. }
            { exfalso. apply H. unfold is_core_symbol. right. reflexivity. }

            unfold new_app_interp in Hin.
            rewrite elem_of_PropSet in Hinre.
            repeat case_match; subst; auto; try contradiction; try congruence.
            {
                unfold app_ext in Hin.
                rewrite elem_of_PropSet in Hin.
                destruct Hin as [a [Hin1 Hin2] ].
                inversion Hin1. subst. clear Hin1.
                rewrite elem_of_PropSet in Hin2.
                destruct Hin2 as [a [Hin2 Hin3] ].
                inversion Hin2. subst. clear Hin2.
                rewrite elem_of_PropSet in Hin3.
                destruct Hin3 as [le [lre [Hle [Hre HAlmost] ] ] ].
                rewrite elem_of_PropSet in Hre.
                inversion Hre. clear Hre. subst.
                destruct Hinre as [a' [Ha' Ha''] ].
                rewrite elem_of_PropSet in Ha''.
                destruct_and_ex!. subst.
                exists le, x.
                split;[assumption|].
                split;[assumption|].
                inversion Ha'. subst.
                assumption.
            }
            {
                rewrite elem_of_PropSet in Hin.
                destruct Hinre as [a1 [Ja1 Ga1] ].
                destruct Hin as [a2 [Ja2 Ga2] ].
                inversion Ja1; clear Ja1; subst.
                inversion Ja2; clear Ja2; subst.
                rewrite elem_of_PropSet in Ga1.
                destruct Ga1 as [a3 [Ja3 Ga3] ].
                inversion Ja3.
            }
        }
    Qed.

    Section semantic_preservation.
       Context
            (M_def : M ⊨ᵀ Definedness_Syntax.theory)
        .

        Lemma SPred_is_pre_predicate
            (ψ : Pattern)
            :
            is_SPredicate ψ ->
            M_pre_predicate M ψ.
        Proof.
            intros HSPred.
            induction HSPred.
            { apply (@M_pre_pre_predicate_impl_M_pre_predicate _ 0). apply M_pre_pre_predicate_bott. }
            { apply (@M_pre_pre_predicate_impl_M_pre_predicate _ 0). apply T_pre_predicate_defined. exact M_def. }
            { apply (@M_pre_pre_predicate_impl_M_pre_predicate _ 0). apply T_pre_predicate_equal. exact M_def. }
            { apply (@M_pre_pre_predicate_impl_M_pre_predicate _ 0). apply T_pre_predicate_subseteq. exact M_def. }
            { apply M_pre_predicate_imp; assumption. }
            { 
                unfold patt_exists_of_sort.
                apply M_pre_predicate_exists.
                apply M_pre_predicate_and.
                2: { exact IHHSPred. }
                unfold patt_in.
                apply T_pre_predicate_defined.
                rewrite HSortImptDef.
                exact M_def.
            }
            {
                unfold patt_forall_of_sort.
                apply M_pre_predicate_forall.
                apply M_pre_predicate_imp.
                2: { exact IHHSPred. }
                unfold patt_in.
                apply T_pre_predicate_defined.
                rewrite HSortImptDef.
                exact M_def.
            }
        Qed.

        Lemma SPred_is_predicate
            (ψ : Pattern)
            :
            well_formed_closed_ex_aux ψ 0 ->
            is_SPredicate ψ ->
            M_predicate M ψ.
        Proof.
            intros Hwfc Hspred.
            apply SPred_is_pre_predicate in Hspred.
            unfold M_pre_predicate in Hspred.
            specialize (Hspred 0).
            eapply closed_M_pre_pre_predicate_is_M_predicate.
            2: { apply Hspred. }
            apply Hwfc.
        Qed.


        Lemma semantics_preservation_sym (s : symbols)
            (ρ : @Valuation _ M)
            ρ0
            :
            is_not_core_symbol s ->
            @eval Σ Mext ρ0 (patt_sym s) =
            lift_set (@eval Σ M ρ (patt_sym s)).
        Proof.
            intros H.
            do 2 rewrite eval_sym_simpl.
            clear -H. unfold_leibniz.
            unfold is_not_core_symbol,is_core_symbol in H.
            unfold sym_interp at 1. simpl. unfold new_sym_interp.
            repeat case_match; subst.
            { exfalso. tauto. }
            { exfalso. tauto. }
            unfold lift_set,fmap. reflexivity.
        Qed.

        Lemma semantics_preservation_inhabitant_set (s : symbols)
            (ρ : @Valuation _ M)
            ρ0
            :
            is_not_core_symbol s ->
            @eval Σ Mext ρ0 (patt_inhabitant_set (patt_sym s))
            = lift_set (@eval Σ M ρ (patt_inhabitant_set (patt_sym s))).
        Proof.
            intros H.
            rename H into Hnc.
            (* For some reason, the tactic [unfold_leibniz] performed later
               in the proof script does nothing. *)
            unfold_leibniz. 
            unfold patt_inhabitant_set.
            do 2 rewrite eval_app_simpl.
            rewrite (semantics_preservation_sym _ ρ);[assumption|].
            remember (eval ρ (patt_sym s)) as ps.
            unfold Sorts_Syntax.sym.
            do 2 rewrite eval_sym_simpl.
            unfold sym_interp at 1. simpl. unfold new_sym_interp.
            rewrite decide_eq_same.
            destruct (decide (inj inhabitant = Definedness_Syntax.inj definedness)) as [Heq|Hneq] eqn:Hnid.
            { clear -HDefNeqInh Heq. congruence. }
            {
                clear Hneq Hnid.
                unfold app_ext at 1.
                unfold app_interp at 1. simpl. unfold new_app_interp.
                set_unfold. intros x. split.
                {
                    intros [x0 [x1 H] ]. destruct_and!. subst.
                    repeat case_match.
                    { exfalso. clear -H2. set_solver. }
                    { exfalso. clear -H2. set_solver. }
                    { subst. set_solver. }
                    { subst. set_solver. }
                }
                {
                    intros [y H]. destruct_and!. subst.
                    destruct H1 as [y0 H]. destruct_and!. subst.
                    destruct H1 as [x [x0 H] ].
                    clear Heqps.
                    destruct_and!.
                    exists cinh.
                    eexists (cel (inl x0)).
                    split.
                    { reflexivity. }
                    split.
                    {
                        exists (inl x0). split. reflexivity. exists x0. split.
                        reflexivity. assumption.
                    }
                    {
                        unfold fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        set_solver.
                    }
                }
            }
        Qed.

        Lemma update_evar_val_lift_val_comm
            (ρ : @Valuation _ M)
            (x : evar)
            (d : Domain M)
            :
            (@update_evar_val Σ Mext x (cel (inl d)) (lift_val ρ))
            = lift_val (@update_evar_val Σ M x d ρ).
        Proof.
            destruct ρ as [ρₑ ρₛ]. unfold update_evar_val. simpl.
            unfold lift_val. simpl. f_equal.
            apply functional_extensionality.
            intros x'.
            case_match; reflexivity.
        Qed.
 
        Lemma update_svar_val_lift_set_comm
            (ρ : @Valuation _ M)
            (X : svar)
            (D : propset (Domain M))
            :
        (@update_svar_val Σ Mext X (lift_set D) (lift_val ρ))
        = lift_val (@update_svar_val Σ M X D ρ).
        Proof.
            destruct ρ as [ρₑ ρₛ]. unfold update_svar_val. simpl.
            unfold lift_val. simpl. f_equal.
            apply functional_extensionality.
            intros X'.
            case_match; reflexivity.
        Qed.

        Lemma lift_set_fa_union (C : Type) (f : C -> propset (Domain M)) :
            lift_set (stdpp_ext.propset_fa_union f) = stdpp_ext.propset_fa_union (λ k, lift_set (f k)).
        Proof.
            unfold stdpp_ext.propset_fa_union, lift_set.
            unfold lift_set,fmap.
            with_strategy transparent [propset_fmap] unfold propset_fmap.
            clear. unfold_leibniz. set_solver.
        Qed.

        Lemma lift_set_fa_intersection (C : Type) {_ : Inhabited C} (f : C -> propset (Domain M)) :
            lift_set (stdpp_ext.propset_fa_intersection f) = stdpp_ext.propset_fa_intersection (λ k, lift_set (f k)).
        Proof.
            unfold stdpp_ext.propset_fa_intersection, lift_set.
            unfold lift_set,fmap.
            with_strategy transparent [propset_fmap] unfold propset_fmap.
            unfold_leibniz. set_unfold.
            intros x.
            split; intros H.
            {
                destruct_and_ex!.  subst. intros.
                exists (inl x1).
                split;[reflexivity|].
                exists x1.
                split;[reflexivity|].
                apply H2.
            }
            {
                pose proof (Htmp := H (@stdpp.base.inhabitant C X)).
                destruct_and_ex!. subst.
                exists (inl x1).
                split;[reflexivity|].
                exists x1.
                split;[reflexivity|].
                intros x.
                pose proof (Htmp2 := H x).
                destruct_and_ex!. subst.
                inversion H0. subst.
                assumption.
            }
        Qed.

        Lemma semantics_preservation
            (sz : nat)
            :
            (
                forall (ϕ : Pattern) (ρ : @Valuation _ M),
                size' ϕ < sz ->
                is_SData ϕ ->
                well_formed ϕ ->
                @eval Σ Mext (lift_val ρ) ϕ
                = lift_set (@eval Σ M ρ ϕ)
            )
            /\
            (
                forall (ψ : Pattern) (ρ : @Valuation _ M),
                size' ψ < sz ->
                is_SPredicate ψ ->
                well_formed ψ ->
                (@eval Σ Mext (lift_val ρ) ψ = ∅
                <-> @eval Σ M ρ ψ = ∅)
                /\
                (@eval Σ Mext (lift_val ρ) ψ = ⊤
                <-> @eval Σ M ρ ψ = ⊤)
            ).
        Proof.
            induction sz.
            {
                split.
                {
                    intros ϕ Hsz.
                    destruct ϕ; simpl in Hsz; lia.
                }
                {
                    intros ψ Hsz.
                    destruct ψ; simpl in Hsz; lia.
                }
            }
            {
                destruct IHsz as [IHszdata IHszpred].
                split.
                {
                    (* preservation of data patterns *)
                    intros ϕ ρ Hszϕ HSData Hwf.
                    destruct HSData; simpl in Hszϕ.
                    {
                        (* patt_bott *)
                        do 2 rewrite eval_bott_simpl.
                        unfold lift_set.
                        unfold fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear.
                        unfold_leibniz.
                        set_solver.
                    }
                    {
                        (* free_evar x*)
                        do 2 rewrite eval_free_evar_simpl.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear. unfold_leibniz. set_solver.
                    }
                    {
                        (* free_svar X *)
                        do 2 rewrite eval_free_svar_simpl.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear. unfold_leibniz. set_solver.
                    }
                    {
                        (* bound_evar X *)
                        do 2 rewrite eval_bound_evar_simpl.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear. unfold_leibniz. set_solver.
                    }
                    {
                        (* bound_svar X *)
                        do 2 rewrite eval_bound_svar_simpl.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear. unfold_leibniz. set_solver.
                    }
                    {
                        (* sym s *)
                        apply semantics_preservation_sym.
                        { assumption. }
                    }
                    {
                        (* patt_inhabitant_set (patt_sym s) *)
                        apply semantics_preservation_inhabitant_set.
                        { assumption. }
                    }
                    {
                        (* patt_sorted_neg (patt_sym s) ϕ *)
                        unfold patt_sorted_neg.
                        do 2 rewrite eval_and_simpl.
                        rewrite (semantics_preservation_inhabitant_set _ ρ);[assumption|].
                        do 2 rewrite eval_not_simpl.
                        rewrite IHszdata.
                        {
                            lia.
                        }
                        {
                            exact HSData.
                        }
                        {
                            wf_auto2.
                        }
                        remember (eval ρ (patt_inhabitant_set (patt_sym s))) as Xinh.
                        remember (eval ρ ϕ) as Xϕ.
                        clear HeqXinh HeqXϕ IHszpred IHszdata.
                        unfold_leibniz.
                        set_solver.
                    }
                    {
                        (* patt_app ϕ₁ ϕ₂ *)
                        do 2 rewrite eval_app_simpl.
                        rewrite IHszdata.
                        { lia. }
                        { exact HSData1. }
                        { wf_auto2. }
                        rewrite IHszdata.
                        { lia. }
                        { exact HSData2. }
                        { wf_auto2. }
                        unfold app_ext.
                        clear. unfold_leibniz.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        unfold Mext. simpl. unfold new_app_interp.
                        set_unfold.
                        intros x. split.
                        {
                            intros [x0 [x1 H] ].
                            destruct_and!.
                            destruct H0 as [xH0 H0].
                            destruct H as [xH H].
                            destruct_and!. subst.
                            destruct H4 as [xH4 H4].
                            destruct H3 as [xH3 H3].
                            destruct_and!. subst.
                            destruct x.
                            {
                                exfalso.
                                unfold fmap in H2.
                                with_strategy transparent [propset_fmap] unfold propset_fmap in H2.
                                clear -H2. set_solver.
                            }
                            {
                                exfalso.
                                unfold fmap in H2.
                                with_strategy transparent [propset_fmap] unfold propset_fmap in H2.
                                clear -H2. set_solver.
                            }
                            {
                                inversion H2. clear H2. destruct_and!. subst.
                                inversion H2. clear H2. destruct_and!. subst.
                                inversion H1. clear H1. subst.
                                exists (inl x0).
                                split;[reflexivity|].
                                exists x0.
                                split;[reflexivity|].
                                exists xH4,xH3.
                                repeat split; assumption.
                            }
                        }
                        {
                            intros H.
                            destruct_and_ex!. subst.
                            exists (cel (inl x2)).
                            exists (cel (inl x3)).
                            split.
                            {
                                exists (inl x2).
                                split;[reflexivity|].
                                exists x2.
                                split;[reflexivity|].
                                assumption.
                            }
                            split.
                            {
                                exists (inl x3).
                                split;[reflexivity|].
                                exists x3.
                                split;[reflexivity|].
                                assumption.
                            }
                            {
                                unfold fmap.
                                with_strategy transparent [propset_fmap] unfold propset_fmap.   
                                set_solver.
                            }  
                        }
                    }
                    {
                        (* patt_or ϕ₁ ϕ₂ *)
                        do 2 rewrite eval_or_simpl.
                        rewrite IHszdata.
                        { lia. }
                        { exact HSData1. }
                        { wf_auto2. }
                        rewrite IHszdata.
                        { lia. }
                        { exact HSData2. }
                        { wf_auto2. }
                        clear.
                        unfold_leibniz.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        set_solver.
                    }
                    {
                        (* patt_and ϕ ψ *)
                        do 2 rewrite eval_and_simpl.

                        rename H into Hspred.
                    
                        destruct (classic (eval ρ ψ = ∅)).
                        {
                            rewrite IHszdata.
                            { lia. }
                            { exact HSData. }
                            { wf_auto2. }
                            clear HSData IHszdata. 
                            unfold_leibniz.
                            specialize (IHszpred ψ ρ ltac:(lia) ltac:(assumption) ltac:(wf_auto2)).
                            destruct IHszpred as [Hsp1 Hsp2].
                            clear Hsp2.
                            destruct Hsp1 as [Hsp11 Hsp12].
                            specialize (Hsp12 H). clear Hsp11.
                            unfold lift_set,fmap.
                            with_strategy transparent [propset_fmap] unfold propset_fmap.
                            set_solver.
                        }
                        {
                            apply predicate_not_empty_iff_full in H.
                            2: {
                                apply SPred_is_predicate.
                                2: { assumption. }
                                {
                                    clear -Hwf.
                                    unfold patt_and,patt_or,patt_not in Hwf.
                                    apply well_formed_imp_proj1 in Hwf.
                                    apply well_formed_imp_proj2 in Hwf.
                                    apply well_formed_imp_proj1 in Hwf.
                                    wf_auto2.
                                }
                            }
                            specialize (IHszpred ψ ρ ltac:(lia) ltac:(assumption) ltac:(wf_auto2)).
                            specialize (IHszdata ϕ ρ ltac:(lia) HSData ltac:(wf_auto2)).

                            destruct IHszpred as [Hsp1 Hsp2].
                            clear Hsp1.
                            destruct Hsp2 as [Hsp21 Hsp22]. clear Hsp21.
                            specialize (Hsp22 H).
                            rewrite IHszdata.
                            rewrite H. rewrite Hsp22.
                            unfold lift_set,fmap.
                            with_strategy transparent [propset_fmap] unfold propset_fmap.
                            clear.
                            set_unfold.
                            split; intros H.
                            {
                                destruct_and_ex!.
                                subst.
                                exists (inl x1).
                                split.
                                { reflexivity. }
                                exists x1. split;[reflexivity|].
                                split; done.
                            }
                            {
                                destruct_and_ex!.
                                subst.
                                split;[|exact I].
                                exists (inl x1).
                                split;[reflexivity|].
                                exists x1.
                                split; done.
                            }
                        }
                    }
                    {
                        (* patt_exists_of_sort (patt_sym s) ϕ *)
                        unshelve(erewrite eval_exists_of_sort).
                        3: { rewrite HSortImptDef. apply Mext_satisfies_definedness. }
                        { intros. apply Mext_indec. assumption. }
                        unshelve(erewrite eval_exists_of_sort).
                        3: { rewrite HSortImptDef. assumption. }
                        { intros. apply indec. assumption. }
                        rewrite lift_set_fa_union.
                        unfold_leibniz.
                        unfold stdpp_ext.propset_fa_union.
                        apply set_subseteq_antisymm.
                        {
                            apply elem_of_subseteq. intros x Hx.
                            rewrite elem_of_PropSet. rewrite elem_of_PropSet in Hx.
                            destruct Hx as [c Hc].
                            destruct (Mext_indec _ H c ρ) as [Hin|Hnotin].
                            {
                                unfold Minterp_inhabitant in Hin.
                                (* [c] comes from [Domain M] *)
                                destruct c.
                                {
                                    exfalso.
                                    rewrite eval_app_simpl in Hin.
                                    do 2 rewrite eval_sym_simpl in Hin.
                                    unfold app_ext in Hin. simpl in Hin.
                                    unfold new_sym_interp,new_app_interp in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct_and_ex!. repeat case_match; subst; auto; try congruence.
                                    {
                                        clear -H3.
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        set_solver.
                                    }
                                    {
                                        clear -H3. 
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        set_solver.
                                    }
                                }
                                {
                                    exfalso.
                                    rewrite eval_app_simpl in Hin.
                                    do 2 rewrite eval_sym_simpl in Hin.
                                    unfold app_ext in Hin. simpl in Hin.
                                    unfold new_sym_interp,new_app_interp in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct_and_ex!. repeat case_match; subst; auto; try congruence.
                                    {
                                        clear -H3.
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        set_solver.
                                    }
                                    {
                                        clear -H3. 
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        set_solver.
                                    }
                                }
                                destruct el.
                                2: {
                                    exfalso.
                                    rewrite eval_app_simpl in Hin.
                                    do 2 rewrite eval_sym_simpl in Hin.
                                    unfold app_ext in Hin. simpl in Hin.
                                    unfold new_sym_interp,new_app_interp in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct_and_ex!. repeat case_match; subst; auto; try congruence.
                                    {
                                        clear -H3. 
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        set_solver.
                                    }
                                    {
                                        clear -H2. 
                                        unfold fmap in H2.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H2.
                                        set_solver.
                                    }
                                }
                                rewrite update_evar_val_lift_val_comm in Hc.
                                rewrite IHszdata in Hc.
                                3: { wf_auto2. }
                                2: { apply is_SData_evar_open. assumption. }
                                1: { rewrite evar_open_size'. lia. }

                                (* [x] comes from [Domain M] *)
                                unfold lift_set,fmap in Hc.
                                with_strategy transparent [propset_fmap] unfold propset_fmap in Hc.
                                destruct x.
                                {
                                    exfalso.
                                    clear -Hc.
                                    set_solver.
                                }
                                {
                                    exfalso.
                                    clear -Hc.
                                    set_solver.
                                }
                                destruct el.
                                2: {
                                    exfalso.
                                    clear -Hc.
                                     set_solver.
                                }

                                rewrite IHszdata in Hin.
                                3: { wf_auto2. }
                                2: { constructor. assumption. }
                                1: { simpl. lia. }

                                exists d.
                                destruct (indec _ H d ρ) as [Hin'|Hnotin'].
                                2: {
                                    exfalso.
                                    unfold Minterp_inhabitant in Hnotin'.
                                    unfold lift_set,fmap in Hin.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in Hin.
                                    clear -Hin Hnotin'.
                                    set_solver.
                                }
                                apply Hc.
                            }
                            {
                                exfalso. clear -Hc. set_solver.
                            }
                        }
                        {
                            rewrite elem_of_subseteq.
                            intros x Hx.
                            rewrite elem_of_PropSet in Hx.
                            destruct Hx as [c Hc].
                            unfold lift_set,fmap in Hc.
                            with_strategy transparent [propset_fmap] unfold propset_fmap in Hc.
                            destruct x.
                            {
                                exfalso. clear -Hc. set_solver.
                            }
                            {
                                exfalso. clear -Hc. set_solver.
                            }
                            destruct el.
                            2: {
                                exfalso. clear -Hc. set_solver.
                            }
                            rewrite elem_of_PropSet in Hc.
                            destruct Hc as [a [Ha Ha'] ].
                            destruct a.
                            2: {
                                inversion Ha.
                            }
                            inversion Ha. clear Ha. subst.
                            rewrite elem_of_PropSet in Ha'.
                            destruct Ha' as [a [Ha Ha'] ].
                            inversion Ha. clear Ha. subst.
                            rewrite elem_of_PropSet.
                            destruct (indec _ H c ρ).
                            2: {
                                exfalso. clear -Ha'. set_solver.
                            }
                            exists (lift_value c).
                            rewrite update_evar_val_lift_val_comm.
                            destruct (Mext_indec _ H (lift_value c) ρ) as [Hin | Hnotin].
                            {
                                rewrite IHszdata.
                                3: { wf_auto2. }
                                2: { apply is_SData_evar_open. assumption. }
                                1: { rewrite evar_open_size'. lia. }
                                unfold lift_set,fmap.
                                with_strategy transparent [propset_fmap] unfold propset_fmap.
                                rewrite elem_of_PropSet.
                                exists (inl a).
                                split;[reflexivity|].
                                rewrite elem_of_PropSet.
                                exists a.
                                split;[reflexivity|].
                                apply Ha'.
                            }
                            {
                                exfalso. rename e into Hin.
                                unfold Minterp_inhabitant in Hin, Hnotin.
                                rewrite IHszdata in Hnotin.
                                3: { wf_auto2. }
                                2: { constructor. assumption. }
                                1: { simpl. lia. }
                                clear -Hin Hnotin.
                                unfold lift_value,lift_set,fmap in Hnotin.
                                with_strategy transparent [propset_fmap] unfold propset_fmap in Hnotin.
                                set_solver.
                            }
                        }
                    }
                    {
                        (* patt_mu (patt_sym s) ϕ *)
                        do 2 rewrite eval_mu_simpl.
                        cbn zeta.
                        match goal with
                        | [ |- (Lattice.LeastFixpointOf ?fF = lift_set (Lattice.LeastFixpointOf ?fG))] =>
                            remember fF as F; remember fG as G
                        end.

                        symmetry.
                        assert (HmonoF: @Lattice.MonotonicFunction
                            (propset Carrier)
                            (Lattice.PropsetOrderedSet Carrier) F).
                        {
                            subst F.
                            pose proof (Hmono := @is_monotonic Σ Mext).
                            simpl in Hmono.
                            apply Hmono.
                            {
                                unfold well_formed in Hwf. simpl in Hwf.
                                destruct_and!. split_and!; assumption.
                            }
                            {
                                apply set_svar_fresh_is_fresh.
                            }
                        }
                        assert (HmonoG: @Lattice.MonotonicFunction
                            (propset (Domain M))
                            (Lattice.PropsetOrderedSet (Domain M)) G).
                        {
                            subst G.
                            apply is_monotonic.
                            { unfold well_formed in Hwf. simpl in Hwf. wf_auto2. }
                            { apply set_svar_fresh_is_fresh. }
                        }
                        set (Lattice.PowersetLattice (Domain M)) as L in |-.
                        set (Lattice.PowersetLattice (Domain Mext)) as L' in |-.
                        assert (HGmuG: G (@Lattice.LeastFixpointOf _ _ L G) = (@Lattice.LeastFixpointOf _ _ L G)).
                        {
                            apply Lattice.LeastFixpoint_fixpoint. apply HmonoG.
                        }
                        apply Lattice.LeastFixpoint_unique_2.
                        {
                            exact HmonoF.
                        }
                        {
                            fold L.
                            rewrite -[x in (_ = (lift_set x))]HGmuG.
                            rewrite HeqF.
                            rewrite update_svar_val_lift_set_comm.
                            rewrite IHszdata.
                            {
                                rewrite svar_open_size'. lia.
                            }
                            {
                                apply is_SData_svar_open. assumption.
                            }
                            {
                                wf_auto2.
                            }
                            rewrite HeqG.
                            reflexivity.
                        }
                        {
                            set (λ (A : propset (Domain Mext)), PropSet (λ (m : Domain M), lift_value m ∈ A)) as strip.
                            set (λ A, lift_set (eval (update_svar_val (fresh_svar ϕ) (strip A) ρ) (ϕ^{svar: 0 ↦ (fresh_svar ϕ)}))) as G'.

                            assert (Hstripmono: forall x y, x ⊆ y -> strip x ⊆ strip y).
                            {
                                intros x y Hxy.
                                unfold strip. unfold lift_value.
                                clear -Hxy. set_solver.
                            }

                            assert (Hstriplift: forall X, strip (lift_set X) = X).
                            {
                                intros X. unfold strip,lift_set,lift_value,fmap.
                                with_strategy transparent [propset_fmap] unfold propset_fmap.
                                clear. set_solver.
                            }

                            assert (HmonoG' : @Lattice.MonotonicFunction _ (Lattice.PropsetOrderedSet (Domain Mext)) G').
                            {
                                unfold Lattice.MonotonicFunction.
                                intros x y Hxy.
                                unfold G'.
                                simpl.
                                apply lift_set_mono.
                                simpl in Hxy.
                                rewrite HeqG in HmonoG.
                                unfold Lattice.MonotonicFunction in HmonoG.
                                simpl in HmonoG.
                                specialize (HmonoG (strip x) (strip y)).
                                apply HmonoG.
                                apply Hstripmono.
                                apply Hxy.
                            }

                            assert (Hls: lift_set (@Lattice.LeastFixpointOf _ _ L G) = (@Lattice.LeastFixpointOf _ _ L' G')).
                            {
                                assert (G'liftlfpG: G' (lift_set (@Lattice.LeastFixpointOf _ _ L G)) =
                                    lift_set (@Lattice.LeastFixpointOf _ _ L G)).
                                {
                                    rewrite <- HGmuG at 2.
                                    unfold G'.
                                    rewrite Hstriplift.
                                    f_equal.
                                    rewrite HeqG.
                                    reflexivity.
                                }
                                apply Lattice.LeastFixpoint_unique_2.
                                {
                                    exact HmonoG'.
                                }
                                {
                                    apply G'liftlfpG.
                                }
                                {
                                    intros A HA.
                                    rewrite -HA.
                                    unfold G'.
                                    simpl.
                                    apply lift_set_mono.
                                    pose proof (Htmp := Lattice.LeastFixpoint_LesserThanPrefixpoint _ _ L G).
                                    simpl in Htmp. apply Htmp. clear Htmp.
                                    replace (eval (update_svar_val (fresh_svar ϕ) (strip A) ρ)
                                    (ϕ^{svar: 0 ↦ (fresh_svar ϕ)}))
                                    with (G (strip A)) by (subst; reflexivity).
                                    apply HmonoG. simpl.
                                    rewrite <- HA at 2.
                                    unfold G'.
                                    rewrite HeqG.
                                    rewrite Hstriplift.
                                    apply reflexivity.
                                }
                            }
                            (*replace (propset Carrier) with (propset (Domain Mext)) by reflexivity.*)
                            intros A HA.
                            rewrite Hls.
                            apply Lattice.LeastFixpoint_LesserThanPrefixpoint.
                            simpl.
                            rewrite <- HA at 2.
                            unfold G'.
                            rewrite HeqF.
                            assert (Hliftstrip: lift_set (strip A) ⊆ A).
                            {
                                clear.
                                unfold lift_set,strip,lift_value,fmap.
                                with_strategy transparent [propset_fmap] unfold propset_fmap.
                                set_solver.
                            }

                            assert (@eval Σ Mext (update_svar_val (fresh_svar ϕ) (lift_set (strip A)) (lift_val ρ)) (ϕ^{svar: 0 ↦ (fresh_svar ϕ)})
                            ⊆  @eval Σ Mext (update_svar_val (fresh_svar ϕ) A (lift_val ρ)) (ϕ^{svar: 0 ↦ (fresh_svar ϕ)})).
                            {
                                apply is_monotonic.
                                { unfold well_formed in Hwf. destruct_and!. assumption. }
                                { apply set_svar_fresh_is_fresh. }
                                apply Hliftstrip.
                            }
                            eapply transitivity.
                            2: { apply H. }
                            rewrite update_svar_val_lift_set_comm.
                            rewrite IHszdata.
                            { rewrite svar_open_size'. lia. }
                            { apply is_SData_svar_open. assumption. }
                            { wf_auto2. }
                            apply reflexivity.
                        }
                    }
                }
                {   (* preservation of predicates *)
                    intros ψ ρ Hszϕ HSPred Hwf.
                    destruct HSPred; simpl in Hszϕ.
                    {
                        (* patt_bott *)
                        rewrite eval_bott_simpl.
                        rewrite eval_bott_simpl.
                        split.
                        {
                            split; auto.
                        }
                        {
                            split; intros H; exfalso; clear -H.
                            {
                                apply full_impl_not_empty in H; unfold Empty in H; contradiction.
                            }
                            {
                                apply full_impl_not_empty in H; unfold Empty in H; contradiction.
                            }
                        }
                    }
                    {
                        (* patt_defined ϕ *)
                        unfold patt_defined.
                        do 2 rewrite eval_app_simpl.
                        do 2 rewrite eval_sym_simpl.
                        rewrite IHszdata.
                        { lia. }
                        { assumption. }
                        { wf_auto2. }
                        Arguments Domain : simpl never.
                        unfold app_ext.
                        simpl.
                        assert (Htmp: new_sym_interp (Definedness_Syntax.inj definedness) = {[cdef]}).
                        {
                            unfold new_sym_interp.
                            repeat case_match.
                            { reflexivity. }
                            { contradiction. }
                            { contradiction. }
                        }
                        rewrite Htmp.
                        unfold new_app_interp.
                        unfold_leibniz.
                        destruct (classic (eval ρ ϕ = ∅)) as [Hempty|Hnonempty].
                        {
                            rewrite Hempty.
                            split.
                            {
                                split.
                                {

                                    intros H'.
                                    apply set_subseteq_antisymm.
                                    2: {
                                        clear. set_solver.
                                    }
                                    {
                                        rewrite set_equiv_subseteq in H'.
                                        destruct H' as [H' _].
                                        rewrite elem_of_subseteq in H'.
                                        rewrite elem_of_subseteq.
                                        intros x.
                                        rewrite elem_of_PropSet.
                                        intros [le [re H''] ].
                                        specialize (H' (lift_value x)).
                                        exfalso.
                                        rewrite elem_of_PropSet in H'.
                                        cut (@elem_of _ (propset (@Domain Σ Mext)) _ (lift_value x) (@empty (propset (@Domain _ Mext)) _)).
                                        {
                                            intros Hcontra. clear -Hcontra. set_solver.
                                        }
                                        apply H'. clear H'.
                                        exists cdef.
                                        destruct H'' as [H''1 [H''2 H''3] ].
                                        exfalso. clear -H''2.
                                        set_solver.
                                    }
                                }
                                {
                                    intros H'.
                                    rewrite set_equiv_subseteq.
                                    rewrite elem_of_subseteq.
                                    split.
                                    2: {
                                        clear. set_solver.
                                    }
                                    intros x.
                                    rewrite elem_of_PropSet.
                                    rewrite set_equiv_subseteq in H'.
                                    destruct H' as [H' _].
                                    rewrite elem_of_subseteq in H'.
                                    intros HContra.
                                    destruct HContra as [le [re [Hle [HContra Hrest] ] ] ].
                                    exfalso. clear -HContra.
                                    unfold lift_set in HContra.
                                    unfold fmap in HContra.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in HContra.
                                    set_solver.
                                }
                            }
                            {
                                split.
                                {
                                    intros H'.
                                    rewrite set_equiv_subseteq.
                                    split.
                                    {
                                        clear. set_solver.
                                    }
                                    rewrite elem_of_subseteq.
                                    intros x Hx.
                                    rewrite set_equiv_subseteq in H'.
                                    destruct H' as [_ H'2].
                                    rewrite elem_of_subseteq in H'2.
                                    specialize (H'2 (lift_value x)).
                                    ospecialize* H'2.
                                    {
                                        clear. set_solver.
                                    }
                                    rewrite elem_of_PropSet in H'2.
                                    destruct H'2 as [le [re [Hle [Hre Hmatch] ] ] ].
                                    exfalso. clear -Hre.
                                    unfold lift_set in Hre.
                                    unfold fmap in Hre.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in Hre.
                                    set_solver.
                                }
                                {
                                    intros H'.
                                    rewrite set_equiv_subseteq.
                                    rewrite set_equiv_subseteq in H'.
                                    destruct H' as [_ H'].
                                    rewrite elem_of_subseteq in H'.
                                    rewrite elem_of_subseteq.
                                    split.
                                    {
                                        intros x H''.
                                        clear. set_solver.
                                    }
                                    {
                                        rewrite elem_of_subseteq.
                                        intros x Hx.
                                        rewrite elem_of_PropSet.
                                        specialize (H' (@stdpp.base.inhabitant (@Domain _ M) (@Domain_inhabited _ M))).
                                        ospecialize* H'.
                                        {
                                            clear. set_solver.
                                        }
                                        rewrite elem_of_PropSet in H'.
                                        destruct H' as [le [re [H'1 [H'2 H'3] ] ] ].
                                        exfalso. clear -H'2.
                                        set_solver.
                                    }
                                }
                            }
                        }
                        {
                            split.
                            {
                                split.
                                {
                                    intros H'.
                                    rewrite set_equiv_subseteq in H'.
                                    rewrite elem_of_subseteq in H'.
                                    destruct H' as [H'1 _].
                                    rewrite set_equiv_subseteq.
                                    split.
                                    {
                                        rewrite elem_of_subseteq.
                                        intros x Hx.
                                        cut (@elem_of (@Domain Σ Mext) (propset (@Domain Σ Mext))
                                        (@propset_elem_of (@Domain Σ Mext)) (lift_value x)
                                        (@empty (propset (@Domain Σ Mext)) (@propset_empty (@Domain Σ Mext)))).
                                        {
                                            intros HContra.
                                            clear -HContra.
                                            set_solver.
                                        }
                                        apply H'1.
                                        rewrite elem_of_PropSet in Hx.
                                        destruct Hx as [le [re [Hx1 [Hx2 Hx3] ] ] ].
                                        rewrite elem_of_PropSet.
                                        exists cdef. exists (lift_value re).
                                        split.
                                        { clear. set_solver. }
                                        split.
                                        2: { clear. set_solver. }
                                        clear -Hx2.
                                        unfold lift_value,lift_set,fmap.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                                        set_solver.
                                    }
                                    {
                                        clear. set_solver.
                                    }
                                }
                                {
                                    intros H'.
                                    rewrite set_equiv_subseteq.
                                    split.
                                    {
                                        rewrite elem_of_subseteq.
                                        intros x Hx.
                                        rewrite elem_of_PropSet in Hx.
                                        destruct Hx as [le [re [Hx1 [Hx2 Hx3] ] ] ].
                                        rewrite set_equiv_subseteq in H'.
                                        destruct H' as [H' _].
                                        rewrite elem_of_subseteq in H'.
                                        rewrite elem_of_singleton in Hx1. subst.
                                        repeat case_match; subst; auto.
                                        destruct re.
                                        {
                                            unfold lift_set,fmap in Hx2.
                                            with_strategy transparent [propset_fmap] unfold propset_fmap in Hx2.
                                            exfalso. clear -Hx2. set_solver.
                                        }
                                        {
                                            unfold lift_set,fmap in Hx2.
                                            with_strategy transparent [propset_fmap] unfold propset_fmap in Hx2.
                                            exfalso. clear -Hx2. set_solver.
                                        }
                                        destruct el.
                                        2: {
                                            unfold lift_set,fmap in Hx2.
                                            with_strategy transparent [propset_fmap] unfold propset_fmap in Hx2.
                                            exfalso. clear -Hx2. set_solver.
                                        }
                                        exfalso. specialize (H' d).
                                        ospecialize* H'.
                                        {
                                            clear H' Hx3.
                                            rewrite elem_of_PropSet.

                                            unfold lift_set,fmap in Hx2.
                                            with_strategy transparent [propset_fmap] unfold propset_fmap in Hx2.
                                            rewrite elem_of_PropSet in Hx2.
                                            destruct Hx2 as [a [Hx21 Hx22] ].
                                            inversion Hx21. clear Hx21. subst.
                                            rewrite elem_of_PropSet in Hx22.
                                            destruct Hx22 as [a [Hx21 Hx22] ].
                                            inversion Hx21. clear Hx21. subst.

                                            pose proof (Hel := @satisfies_definedness_implies_has_element_for_every_element Σ _ M).
                                            ospecialize* Hel.
                                            {
                                                assumption.
                                            }
                                            (* specialize (Hel a a). *)
                                            destruct Hel as [z [Hz1 Hz2] ].
                                            exists z. exists a.
                                            split.
                                            { exact Hz1. }
                                            split.
                                            { exact Hx22. }
                                            exact Hz2.
                                        }
                                        {
                                            clear -H'. set_solver.
                                        }
                                    }
                                    {
                                        clear. set_solver.
                                    }
                                }
                            }
                            {
                                split.
                                {
                                    intros H'.
                                    rewrite set_equiv_subseteq in H'.
                                    rewrite set_equiv_subseteq.
                                    split.
                                    {
                                        clear. set_solver.
                                    }
                                    {
                                        rewrite elem_of_subseteq.
                                        rewrite elem_of_subseteq in H'.
                                        intros x Hx.
                                        rewrite elem_of_PropSet.
                                        destruct H' as [_ H'].
                                        rewrite elem_of_subseteq in H'.
                                        specialize (H' (lift_value x)).
                                        specialize (H' I).
                                        rewrite elem_of_PropSet in H'.
                                        destruct H' as [le [re [Hle [Hre H'] ] ] ].
                                        rewrite elem_of_singleton in Hle. subst le.
                                        unfold lift_set,fmap in Hre.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in Hre.
                                        rewrite elem_of_PropSet in Hre.
                                        destruct Hre as [a [Ha Hre] ].
                                        subst re.
                                        rewrite elem_of_PropSet in Hre.
                                        destruct Hre as [a0 [Ha0 Hre] ].
                                        subst a.
                                        pose proof (Hel := @satisfies_definedness_implies_has_element_for_every_element Σ _ M).
                                        ospecialize* Hel.
                                        {
                                            assumption.
                                        }
                                        (* specialize (Hel a0 x). *)
                                        destruct Hel as [z [Hz1 Hz2] ].
                                        exists z. exists a0.
                                        split.
                                        { exact Hz1. }
                                        split.
                                        { exact Hre. }
                                        exact Hz2.
                                    }
                                }
                                {
                                    intros H'.
                                    rewrite set_equiv_subseteq in H'.
                                    destruct H' as [_ H'].
                                    rewrite elem_of_subseteq in H'.
                                    rewrite set_equiv_subseteq.
                                    split.
                                    {
                                        clear. set_solver.
                                    }
                                    {
                                        rewrite elem_of_subseteq.
                                        intros x Hx.
                                        rewrite elem_of_PropSet.
                                        exists cdef.
                                        assert (Hex : exists el, el ∈ eval ρ ϕ).
                                        {
                                            clear -Hnonempty.
                                            apply NNPP. intros HContra.
                                            set_solver.
                                        }
                                        destruct Hex as [el Hel].
                                        exists (lift_value el).
                                        split.
                                        { clear. set_solver. }
                                        split.
                                        2: { clear. set_solver. }
                                        unfold lift_value,lift_set,fmap.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                                        clear -Hel. set_solver.
                                    }
                                }
                            }
                        }
                    }
                    {
                        (* patt_equal ϕ₁ ϕ₂ *)
                        rewrite equal_iff_interpr_same.
                        1: { apply Mext_satisfies_definedness. }
                        rewrite equal_iff_interpr_same.
                        1: { apply M_def. }
                        rewrite not_equal_iff_not_interpr_same_1.
                        1: { apply Mext_satisfies_definedness. }
                        rewrite not_equal_iff_not_interpr_same_1.
                        1: { apply M_def. }
                        rewrite IHszdata.
                        { lia. }
                        { assumption. }
                        { wf_auto2. }
                        rewrite IHszdata.
                        { lia. }
                        { assumption. }
                        { wf_auto2. }
                        rewrite lift_set_injective.
                        tauto.
                    }
                    {
                        (* patt_subseteq ϕ₁ ϕ₂ *)
                        rewrite subseteq_iff_interpr_subseteq.
                        1: { apply Mext_satisfies_definedness. }
                        rewrite subseteq_iff_interpr_subseteq.
                        1: { apply M_def. }
                        rewrite not_subseteq_iff_not_interpr_subseteq_1.
                        1: { apply Mext_satisfies_definedness. }
                        rewrite not_subseteq_iff_not_interpr_subseteq_1.
                        1: { apply M_def. }
                        rewrite IHszdata.
                        { lia. }
                        { assumption. }
                        { wf_auto2. }
                        rewrite IHszdata.
                        { lia. }
                        { assumption. }
                        { wf_auto2. }
                        rewrite lift_set_mono.
                        tauto.
                    }
                    {
                        (* patt_impl ψ₁ ψ₂*)
                        do 2 rewrite eval_imp_simpl.
                        pose proof (IH1 := IHszpred ϕ₁ ρ).
                        ospecialize* IH1.
                        { lia. }
                        { assumption. }
                        { wf_auto2. }
                        destruct IH1 as [IH11 IH12].
                        pose proof (IH2 := IHszpred ϕ₂ ρ).
                        ospecialize* IH2.
                        { lia. }
                        { assumption. }
                        { wf_auto2. }
                        destruct IH2 as [IH21 IH22].
                        split.
                        {
                            split; intros H.
                            {
                                rewrite empty_union_L in H.
                                destruct H as [H1 H2].
                                rewrite empty_union_L.
                                split.
                                {
                                    rewrite stdpp_ext.complement_empty_iff_full in H1.
                                    rewrite stdpp_ext.complement_empty_iff_full.
                                    rewrite -IH12.
                                    assumption.
                                }
                                {
                                    rewrite -IH21.
                                    assumption.
                                }
                            }
                            {
                                rewrite empty_union_L in H.
                                destruct H as [H1 H2].
                                rewrite empty_union_L.
                                split.
                                {
                                    rewrite stdpp_ext.complement_empty_iff_full.
                                    rewrite stdpp_ext.complement_empty_iff_full in H1.
                                    rewrite IH12.
                                    exact H1.
                                }
                                {
                                    rewrite IH21.
                                    exact H2.
                                }
                            }
                        }
                        {
                            apply SPred_is_predicate in HSPred1.
                            2: {
                                unfold well_formed,well_formed_closed in Hwf.
                                simpl in Hwf.
                                destruct_and!.
                                assumption.
                            }
                            apply SPred_is_predicate in HSPred2.
                            2: {
                                unfold well_formed,well_formed_closed in Hwf.
                                simpl in Hwf.
                                destruct_and!.
                                assumption.
                            }
                            specialize (HSPred1 ρ).
                            specialize (HSPred2 ρ).
                            split; intros H.
                            {
                                destruct HSPred1 as [H1T|H1B],
                                HSPred2 as [H2T|H2B].
                                {
                                    rewrite H2T.
                                    clear.
                                    set_solver.
                                }
                                {
                                    rewrite H2B.
                                    apply IH21 in H2B.
                                    rewrite H2B in H.
                                    assert (H': eval (lift_val ρ) ϕ₁  = ∅).
                                    {
                                        clear -H. set_solver.
                                    }
                                    rewrite IH11 in H'.
                                    rewrite H'.
                                    clear. set_solver.
                                }
                                {
                                    rewrite H1B. rewrite H2T.
                                    clear. set_solver.
                                }
                                {
                                    rewrite H1B. rewrite H2B. clear. set_solver.
                                }
                            }
                            {
                                destruct HSPred1 as [H1T|H1B],
                                HSPred2 as [H2T|H2B].
                                {
                                    apply IH12 in H1T.
                                    rewrite H1T.
                                    apply IH22 in H2T.
                                    rewrite H2T.
                                    clear.
                                    set_solver.
                                }
                                {
                                    rewrite H1T in H.
                                    rewrite H2B in H.
                                    exfalso. clear -H.
                                    pose proof (Hinh := Domain_inhabited M).
                                    inversion Hinh.
                                    set_solver.
                                }
                                {
                                    apply IH11 in H1B.
                                    rewrite H1B.
                                    apply IH22 in H2T.
                                    rewrite H2T.
                                    clear.
                                    set_solver.
                                }
                                {
                                    apply IH11 in H1B.
                                    rewrite H1B.
                                    apply IH21 in H2B.
                                    rewrite H2B.
                                    clear.
                                    set_solver.
                                }
                            }
                        }
                    }
                    {
                        unshelve (erewrite eval_exists_of_sort).
                        3: { rewrite HSortImptDef. apply Mext_satisfies_definedness. }
                        1: { intros m. apply Mext_indec. assumption. }

                        unshelve (erewrite eval_exists_of_sort).
                        3: { rewrite HSortImptDef. assumption. }
                        1: { intros m. apply indec. assumption. }

                        do 2 rewrite stdpp_ext.propset_fa_union_empty.

                        specialize (IHszpred (ϕ^{evar: 0 ↦ fresh_evar ϕ})).
                        split.
                        {
                            split; intros H'; intros c.
                            {
                                destruct (indec _ H c ρ) as [Hin|Hnotin].
                                2: { reflexivity. }
                                specialize (H' (lift_value c)).
                                rewrite update_evar_val_lift_val_comm in H'.
                                specialize (IHszpred (update_evar_val (fresh_evar ϕ) c ρ)).
                                ospecialize* IHszpred.
                                {
                                    rewrite evar_open_size'. lia.
                                }
                                {
                                    apply is_SPredicate_evar_open. assumption.
                                }
                                {
                                    wf_auto2.
                                }
                                destruct IHszpred as [IH1 IH2].
                                destruct (Mext_indec _ H (lift_value c) ρ) as [Hin'|Hnotin'].
                                {
                                    apply IH1 in H'. apply H'.
                                }
                                {
                                    exfalso.
                                    unfold Minterp_inhabitant in Hin,Hnotin'.
                                    rewrite eval_app_simpl in Hin.
                                    rewrite eval_app_simpl in Hnotin'.
                                    do 2 rewrite eval_sym_simpl in Hin.
                                    do 2 rewrite eval_sym_simpl in Hnotin'.
                                    unfold app_ext in Hin,Hnotin'.
                                    unfold lift_value in Hnotin'. simpl in Hnotin'.
                                    unfold new_sym_interp in Hnotin'.
                                    rewrite elem_of_PropSet in Hnotin'.
                                    unfold is_not_core_symbol,is_core_symbol in H.
                                    repeat case_match; subst; auto; try contradiction.
                                    apply Hnotin'.
                                    clear -Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct Hin as [le [re [Hle [Hre Hin] ] ] ].
                                    exists cinh. exists (cel (inl re)).
                                    split.
                                    { clear. set_solver. }
                                    split.
                                    {
                                        unfold fmap.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                                        rewrite elem_of_PropSet.
                                        exists (inl re).
                                        split;[reflexivity|].
                                        rewrite elem_of_PropSet.
                                        exists re.
                                        split;[reflexivity|].
                                        assumption.
                                    }
                                    unfold new_app_interp.
                                    unfold fmap.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap.
                                    rewrite elem_of_PropSet.
                                    exists (inl c).
                                    split;[reflexivity|].
                                    rewrite elem_of_PropSet.
                                    exists c.
                                    split;[reflexivity|].
                                    unfold app_ext.
                                    rewrite elem_of_PropSet.
                                    exists le. exists re.
                                    split;[assumption|].
                                    split;[(clear; set_solver)|].
                                    assumption.
                                }
                            }
                            {
                                destruct (Mext_indec _ H c ρ) as [Hin|Hnotin].
                                {
                                    unfold Minterp_inhabitant in Hin.
                                    rewrite eval_app_simpl in Hin.
                                    do 2 rewrite eval_sym_simpl in Hin.
                                    unfold app_ext in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct Hin as [le [re [Hle [Hre Hin] ] ] ].
                                    simpl in Hle,Hre,Hin.
                                    unfold is_not_core_symbol,is_core_symbol in H.
                                    unfold new_app_interp in Hin.
                                    unfold new_sym_interp in Hle,Hre.
                                    repeat case_match; subst; try contradiction; try congruence.
                                    2: {
                                        exfalso. clear -Hre.
                                        unfold fmap in Hre.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in Hre.
                                        set_solver.
                                    }
                                    unfold fmap in Hin.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in Hin.
                                    destruct c.
                                    {
                                        exfalso. clear -Hin.  set_solver.
                                    }
                                    {
                                        exfalso. clear -Hin.  set_solver.
                                    }
                                    destruct el.
                                    2: {
                                        exfalso. clear -Hin.  set_solver.
                                    }
                                    rewrite update_evar_val_lift_val_comm.
                                    clear -IHszpred Hszϕ HSPred Hwf H' Hin Hre.
                                    specialize (IHszpred (update_evar_val (fresh_evar ϕ) d0 ρ)).
                                    ospecialize* IHszpred.
                                    {
                                        rewrite evar_open_size'. lia.
                                    }
                                    {
                                        apply is_SPredicate_evar_open. assumption.
                                    }
                                    {
                                        wf_auto2.
                                    }
                                    destruct IHszpred as [IH1 IH2].
                                    rewrite IH1.
                                    specialize (H' d0).
                                    destruct (indec _ H d0 ρ) as [Hin'|Hnotin'].
                                    {
                                        apply H'.
                                    }
                                    {
                                        exfalso. apply Hnotin'. clear Hnotin'.
                                        unfold Minterp_inhabitant.
                                        rewrite eval_app_simpl.
                                        do 2 rewrite eval_sym_simpl.
                                        rewrite elem_of_PropSet in Hin.
                                        destruct Hin as [a [Ha Hin] ].
                                        inversion Ha. clear Ha. subst.
                                        rewrite elem_of_PropSet in Hin.
                                        destruct Hin as [a [Ha Hin] ].
                                        inversion Ha. clear Ha. subst.
                                        unfold app_ext in Hin.
                                        rewrite elem_of_PropSet in Hin.
                                        destruct Hin as [le [re [Hle' [Hre' Hin] ] ] ].
                                        rewrite elem_of_singleton in Hre'. subst re.
                                        unfold app_ext.
                                        rewrite elem_of_PropSet.
                                        unfold fmap in Hre.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in Hre.
                                        rewrite elem_of_PropSet in Hre.
                                        destruct Hre as [a' [Ha' Hre'] ].
                                        rewrite elem_of_PropSet in Hre'.
                                        destruct Hre' as [a'' [Ha'' Hre'] ].
                                        subst.
                                        inversion Ha'. clear Ha'. subst.
                                        exists le. exists a''.
                                        split;[assumption|].
                                        split;assumption.
                                    }
                                }
                                reflexivity.
                            }
                        }
                        {
                            do 2 rewrite stdpp_ext.propset_fa_union_full.
                            pose proof (HSPred' := HSPred).
                            apply SPred_is_pre_predicate in HSPred'.
                            apply (@M_pre_predicate_evar_open Σ M ϕ (fresh_evar ϕ)) in HSPred'.
                            specialize (HSPred' 0).
                            apply closed_M_pre_pre_predicate_is_M_predicate in HSPred'.
                            2: {
                                unfold well_formed,well_formed_closed in Hwf. simpl in Hwf.
                                destruct_and!.
                                wf_auto2.
                            }
                            split; intros H' t.
                            {
                                specialize (H' stdpp.base.inhabitant).
                                destruct H' as [c Hc].
                                destruct (Mext_indec _ H c ρ) as [Hin|Hnotin].
                                {
                                    unfold Minterp_inhabitant in Hin.
                                    rewrite eval_app_simpl in Hin.
                                    do 2 rewrite eval_sym_simpl in Hin.
                                    unfold app_ext in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    simpl in Hin.
                                    destruct Hin as [le [re [Hle [Hre Hin] ] ] ].
                                    unfold is_not_core_symbol,is_core_symbol in H.
                                    unfold new_sym_interp in Hle,Hre.
                                    unfold new_app_interp in Hin.
                                    repeat case_match; subst; try contradiction; try congruence;
                                    unfold fmap in Hre;
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in Hre;
                                    rewrite elem_of_PropSet in Hre;
                                    destruct Hre as [amr [Hamr Hamr'] ];
                                    inversion Hamr; clear Hamr; subst;
                                    rewrite elem_of_PropSet in Hamr';
                                    destruct Hamr' as [amr' [Hamr'' Hamr'] ];
                                    inversion Hamr''; clear Hamr''; subst.
                                    unfold fmap in Hin.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct Hin as [a [Htmp Ha] ].
                                    subst.
                                    rewrite elem_of_PropSet in Ha.
                                    destruct Ha as [a0 [Htmp Ha0] ].
                                    subst.
                                    unfold app_ext in Ha0.
                                    rewrite elem_of_PropSet in Ha0.
                                    destruct Ha0 as [le' [re' [Hle' [Hre' Hle're'] ] ] ].
                                    rewrite elem_of_singleton in Hre'. subst re'.
                                    exists a0.
                                    destruct (indec _ H a0 ρ) as [Hin'|Hnotin'].
                                    2: {
                                        exfalso. apply Hnotin'.
                                        unfold Minterp_inhabitant.
                                        rewrite eval_app_simpl.
                                        do 2 rewrite eval_sym_simpl.
                                        unfold app_ext.
                                        rewrite elem_of_PropSet.
                                        exists le'. exists amr'.
                                        repeat split; try assumption.
                                    }
                                    {
                                        clear -IHszpred Hc Hwf Hszϕ HSPred HSPred'.
                                        rewrite update_evar_val_lift_val_comm in Hc.
                                        specialize (IHszpred (update_evar_val (fresh_evar ϕ) a0 ρ)).
                                        ospecialize* IHszpred.
                                        {
                                            rewrite evar_open_size'. lia.
                                        }
                                        {
                                            apply is_SPredicate_evar_open. assumption.
                                        }
                                        {
                                            wf_auto2.
                                        }
                                        destruct IHszpred as [IH1 IH2].
                                        specialize (HSPred' (update_evar_val (fresh_evar ϕ) a0 ρ)).
                                        destruct HSPred' as [HFull|HEmpty].
                                        {
                                            rewrite HFull. clear. set_solver.
                                        }
                                        {
                                            apply IH1 in HEmpty.
                                            exfalso.
                                            rewrite HEmpty in Hc.
                                            clear -Hc.
                                            set_solver.
                                        }
                                    }
                                }
                                {
                                    exfalso. clear -Hc. set_solver.
                                }
                            }
                            {
                                specialize (H' (@stdpp.base.inhabitant _ (Domain_inhabited M))).
                                destruct H' as [c Hc].
                                destruct (indec _ H c ρ) as [Hin|Hnotin].
                                {
                                    exists (lift_value c).
                                    destruct (Mext_indec _ H (lift_value c) ρ) as [Hin'|Hnotin'].
                                    {
                                        rewrite update_evar_val_lift_val_comm.
                                        specialize (IHszpred (update_evar_val (fresh_evar ϕ) c ρ)).
                                        ospecialize* IHszpred.
                                        {
                                            rewrite evar_open_size'. lia.
                                        }
                                        {
                                            apply is_SPredicate_evar_open. assumption.
                                        }
                                        {
                                            wf_auto2.
                                        }
                                        destruct IHszpred as [IH1 IH2].

                                        specialize (HSPred' (update_evar_val (fresh_evar ϕ) c ρ)).
                                        destruct HSPred' as [HFull|HEmpty].
                                        {
                                            apply IH2 in HFull.
                                            rewrite HFull.
                                            clear.
                                            set_solver.
                                        }
                                        {
                                            rewrite HEmpty in Hc.
                                            exfalso. clear -Hc.
                                            set_solver.
                                        }
                                    }
                                    {
                                        exfalso. apply Hnotin'. clear Hnotin'.
                                        unfold Minterp_inhabitant.
                                        rewrite eval_app_simpl.
                                        do 2 rewrite eval_sym_simpl.
                                        simpl.
                                        unfold app_ext.
                                        rewrite elem_of_PropSet.
                                        unfold Minterp_inhabitant in Hin.
                                        rewrite eval_app_simpl in Hin.
                                        do 2 rewrite eval_sym_simpl in Hin.
                                        unfold app_ext in Hin.
                                        rewrite elem_of_PropSet in Hin.
                                        destruct Hin as [le [re [Hle [Hre Hlere] ] ] ].
                                        simpl.
                                        exists cinh.
                                        exists (lift_value re).
                                        split.
                                        {
                                            unfold new_sym_interp.
                                            repeat case_match; try congruence.
                                        }
                                        simpl.
                                        split.
                                        {
                                            unfold new_sym_interp,lift_value.
                                            simpl in *.
                                            unfold is_not_core_symbol,is_core_symbol in H.
                                            repeat case_match; subst; try tauto.
                                            unfold fmap.
                                            with_strategy transparent [propset_fmap] unfold propset_fmap.
                                            rewrite elem_of_PropSet.
                                            exists (inl re).
                                            split;[reflexivity|].
                                            rewrite elem_of_PropSet.
                                            exists re.
                                            split;[reflexivity|].
                                            assumption.
                                        }
                                        {
                                            unfold fmap,lift_value.
                                            with_strategy transparent [propset_fmap] unfold propset_fmap.
                                            rewrite elem_of_PropSet.
                                            exists (inl c).
                                            split;[reflexivity|].
                                            rewrite elem_of_PropSet.
                                            exists c.
                                            split;[reflexivity|].
                                            rewrite elem_of_PropSet.
                                            exists le. exists re.
                                            split;[assumption|].
                                            split;[(clear;set_solver)|].
                                            assumption.
                                        }
                                    }
                                }
                                {
                                    exfalso. clear -Hc. set_solver.
                                }
                            }
                        }
                    }
                    {
                        unshelve (erewrite eval_forall_of_sort).
                        3: { rewrite HSortImptDef. apply Mext_satisfies_definedness. }
                        1: { intros m. apply Mext_indec. assumption. }

                        unshelve (erewrite eval_forall_of_sort).
                        3: { rewrite HSortImptDef. assumption. }
                        1: { intros m. apply indec. assumption. }

                        do 2 rewrite stdpp_ext.propset_fa_intersection_full.
                        rewrite stdpp_ext.propset_fa_intersection_empty.
                        unshelve (erewrite @stdpp_ext.propset_fa_intersection_empty).
                        3: { apply _. }
                        2: { apply Domain_inhabited. }

                        split.
                        {
                            split.
                            {
                                intros H'.
                                intros t.
                                specialize (H' (stdpp.base.inhabitant)).
                                destruct H' as [c Hc].
                                destruct (Mext_indec _ H c ρ) as [Hin|Hnotin].
                                {
                                    unfold Minterp_inhabitant in Hin.
                                    rewrite eval_app_simpl in Hin.
                                    do 2 rewrite eval_sym_simpl in Hin.
                                    unfold app_ext in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    simpl in Hin.
                                    destruct Hin as [le [re [Hle [Hre Hin] ] ] ].
                                    unfold is_not_core_symbol,is_core_symbol in H.
                                    unfold new_sym_interp in Hle,Hre.
                                    repeat case_match; subst; try contradiction; try congruence; try (solve [exfalso;tauto]).
                                    unfold fmap in Hre.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in Hre.
                                    rewrite elem_of_PropSet in Hre.
                                    destruct Hre as [amr [Hamr Hre] ].
                                    subst re.
                                    rewrite elem_of_PropSet in Hre.
                                    destruct Hre as [a [Ha Hre] ].
                                    subst amr.
                                    rewrite elem_of_singleton in Hle. subst le.
                                    unfold new_app_interp in Hin.
                                    repeat case_match; subst.
                                    unfold fmap in Hin.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct Hin as [amr [Hamr Hin] ].
                                    subst c.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct Hin as [a0 [Hamr Hin] ].
                                    subst amr.
                                    unfold app_ext in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct Hin as [le [re [Hle [Hre' Hin] ] ] ].
                                    rewrite elem_of_singleton in Hre'. subst re.
                                    specialize (IHszpred (ϕ^{evar: 0 ↦ fresh_evar ϕ}) (update_evar_val (fresh_evar ϕ) a0 ρ)).
                                    ospecialize* IHszpred.
                                    {
                                        rewrite evar_open_size'.
                                        lia.
                                    }
                                    {
                                        apply is_SPredicate_evar_open.
                                        assumption.
                                    }
                                    {
                                        wf_auto2.
                                    }
                                    destruct IHszpred as [IH1 IH2].
                                    pose proof (HSPred' := HSPred).
                                    apply SPred_is_pre_predicate in HSPred'.
                                    apply (@M_pre_predicate_evar_open Σ M ϕ (fresh_evar ϕ)) in HSPred'.
                                    exists a0.
                                    destruct (indec _ H a0 ρ) as [Hin'|Hnotin'].
                                    {
                                        rewrite update_evar_val_lift_val_comm in Hc.
                                        intros HContra. apply Hc. clear Hc.
                                        unfold M_pre_predicate in HSPred'.
                                        specialize (HSPred' 0).
                                        apply closed_M_pre_pre_predicate_is_M_predicate in HSPred'.
                                        2: {
                                            unfold well_formed,well_formed_closed in Hwf.
                                            simpl in Hwf.
                                            destruct_and!.
                                            wf_auto2.
                                        }
                                        specialize (HSPred' (update_evar_val (fresh_evar ϕ) a0 ρ)).
                                        destruct HSPred' as [HFull|HEmpty].
                                        {
                                            apply IH2 in HFull.
                                            rewrite HFull.
                                            clear.
                                            set_solver.
                                        }
                                        {
                                            rewrite HEmpty in HContra.
                                            exfalso. clear -HContra.
                                            set_solver.
                                        }
                                    }
                                    {
                                        exfalso. apply Hnotin'.
                                        unfold Minterp_inhabitant.
                                        rewrite eval_app_simpl.
                                        do 2 rewrite eval_sym_simpl.
                                        unfold app_ext.
                                        rewrite elem_of_PropSet.
                                        exists le. exists a.
                                        repeat split; assumption.
                                    }
                                }
                                {
                                    exfalso. clear -Hc. set_solver.
                                }
                            }
                            {
                                intros H'.
                                intros t.
                                specialize (H' (@stdpp.base.inhabitant _ (Domain_inhabited M))).
                                destruct H' as [c Hc].
                                destruct (indec _ H c ρ) as [Hin|Hnotin].
                                {
                                    unfold Minterp_inhabitant in Hin.
                                    rewrite eval_app_simpl in Hin.
                                    do 2 rewrite eval_sym_simpl in Hin.
                                    unfold app_ext in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct Hin as [le [re [Hle [Hre Hin] ] ] ].

                                    specialize (IHszpred (ϕ^{evar: 0 ↦ fresh_evar ϕ}) (update_evar_val (fresh_evar ϕ) c ρ)).
                                    ospecialize* IHszpred.
                                    {
                                        rewrite evar_open_size'.
                                        lia.
                                    }
                                    {
                                        apply is_SPredicate_evar_open.
                                        assumption.
                                    }
                                    {
                                        wf_auto2.
                                    }
                                    destruct IHszpred as [IH1 IH2].
                                    pose proof (HSPred' := HSPred).
                                    apply SPred_is_pre_predicate in HSPred'.
                                    apply (@M_pre_predicate_evar_open Σ M ϕ (fresh_evar ϕ)) in HSPred'.

                                    exists (lift_value c).
                                    destruct (Mext_indec _ H (lift_value c) ρ) as [Hin'|Hnotin'].
                                    {
                                        rewrite update_evar_val_lift_val_comm.
                                        unfold M_pre_predicate in HSPred'.
                                        specialize (HSPred' 0).
                                        apply closed_M_pre_pre_predicate_is_M_predicate in HSPred'.
                                        2: {
                                            unfold well_formed,well_formed_closed in Hwf. 
                                            simpl in Hwf.
                                            destruct_and!.
                                            wf_auto2.
                                        }
                                        specialize (HSPred' (update_evar_val (fresh_evar ϕ) c ρ)).
                                        destruct HSPred' as [HFull|HEmpty].
                                        {
                                            intros HContra. apply Hc. clear Hc.
                                            rewrite HFull.
                                            clear. set_solver.
                                        }
                                        {
                                            apply IH1 in HEmpty.
                                            rewrite HEmpty.
                                            clear. set_solver.
                                        }
                                    }
                                    {
                                        exfalso.
                                        apply Hnotin'. clear Hnotin'.
                                        unfold Minterp_inhabitant.
                                        rewrite eval_app_simpl.
                                        do 2 rewrite eval_sym_simpl.
                                        unfold app_ext.
                                        rewrite elem_of_PropSet.
                                        exists cinh.
                                        exists (lift_value re).
                                        simpl.
                                        unfold lift_value,new_sym_interp.
                                        unfold is_not_core_symbol,is_core_symbol in H.
                                        repeat case_match; subst; try congruence; try contradiction; try tauto.
                                        split.
                                        {
                                            clear. set_solver.
                                        }
                                        unfold fmap.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                                        split.
                                        {
                                            rewrite elem_of_PropSet.
                                            exists (inl re).
                                            split;[reflexivity|].
                                            rewrite elem_of_PropSet.
                                            exists re.
                                            split;[reflexivity|].
                                            assumption.
                                        }
                                        {
                                            rewrite elem_of_PropSet.
                                            exists (inl c).
                                            split;[reflexivity|].
                                            rewrite elem_of_PropSet.
                                            exists c.
                                            split;[reflexivity|].
                                            rewrite elem_of_PropSet.
                                            exists le. exists re.
                                            split;[assumption|].
                                            split;[(clear; set_solver)|].
                                            assumption.
                                        }
                                    }
                                }
                                {
                                    exfalso. clear -Hc.
                                    set_solver.
                                }
                            }
                        }
                        {
                            split;
                            intros H'.
                            {
                                intros c.
                                destruct (indec _ H c ρ) as [Hin|Hnotin].
                                {
                                    specialize (IHszpred (ϕ^{evar: 0 ↦ fresh_evar ϕ}) (update_evar_val (fresh_evar ϕ) c ρ)).
                                    ospecialize* IHszpred.
                                    {
                                        rewrite evar_open_size'.
                                        lia.
                                    }
                                    {
                                        apply is_SPredicate_evar_open.
                                        assumption.
                                    }
                                    {
                                        wf_auto2.
                                    }
                                    destruct IHszpred as [IH1 IH2].
                                    specialize (H' (lift_value c)).
                                    destruct (Mext_indec _ H (lift_value c) ρ) as [Hin'|Hnotin'].
                                    {
                                        rewrite update_evar_val_lift_val_comm in H'.
                                        apply IH2 in H'.
                                        exact H'.
                                    }
                                    {
                                        exfalso. apply Hnotin'. clear Hnotin' H'.
                                        unfold Minterp_inhabitant in Hin.
                                        rewrite eval_app_simpl in Hin.
                                        do 2 rewrite eval_sym_simpl in Hin.
                                        unfold app_ext in Hin.
                                        rewrite elem_of_PropSet in Hin.
                                        destruct Hin as [le [re [Hle [Hre Hin] ] ] ].
                                        unfold Minterp_inhabitant.
                                        rewrite eval_app_simpl.
                                        do 2 rewrite eval_sym_simpl.
                                        unfold app_ext.
                                        rewrite elem_of_PropSet.
                                        exists cinh.
                                        exists (lift_value re).
                                        simpl.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                                        unfold new_sym_interp.
                                        unfold is_not_core_symbol,is_core_symbol in H.
                                        repeat case_match; subst; try congruence; try contradiction; try tauto.
                                        split;[(clear; set_solver)|].
                                        unfold fmap.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                                        unfold lift_value.
                                        repeat setoid_rewrite elem_of_PropSet.
                                        split.
                                        {
                                            exists (inl re).
                                            split;[reflexivity|].
                                            exists re.
                                            split;[reflexivity|].
                                            assumption.
                                        }
                                        {
                                            exists (inl c).
                                            split;[reflexivity|].
                                            exists c.
                                            split;[reflexivity|].
                                            exists le.
                                            exists re.
                                            split;[assumption|].
                                            split;[(clear;set_solver)|].
                                            assumption.
                                        }
                                    }
                                }
                                { reflexivity. }
                            }
                            {
                                intros c.
                                destruct (Mext_indec _ H c ρ) as [Hin|Hnotin].
                                2: { reflexivity. }
                                unfold Minterp_inhabitant in Hin.
                                rewrite eval_app_simpl in Hin.
                                do 2 rewrite eval_sym_simpl in Hin.
                                unfold app_ext in Hin.
                                rewrite elem_of_PropSet in Hin.
                                simpl in Hin.
                                unfold new_sym_interp,new_app_interp in Hin.
                                destruct Hin as [le [re [Hle [Hre Hin] ] ] ].
                                unfold is_not_core_symbol,is_core_symbol in H.
                                repeat case_match; subst; try congruence; try contradiction.
                                2: { 
                                    unfold fmap in Hre.
                                    with_strategy transparent [propset_fmap] unfold propset_fmap in Hre.
                                    rewrite elem_of_PropSet in Hre.
                                    destruct Hre as [a [Ha Hre] ].
                                    inversion Ha. clear Ha. subst.
                                    rewrite elem_of_PropSet in Hre.
                                    destruct Hre as [a [Ha Hre] ].
                                    inversion Ha.
                                 }
                                unfold fmap in Hre.
                                with_strategy transparent [propset_fmap] unfold propset_fmap in Hre.
                                rewrite elem_of_PropSet in Hre.
                                destruct Hre as [a [Ha Hre] ].
                                inversion Ha. clear Ha. subst.
                                rewrite elem_of_PropSet in Hre.
                                destruct Hre as [a [Ha Hre] ].
                                inversion Ha. clear Ha. subst.

                                unfold fmap in Hin.
                                with_strategy transparent [propset_fmap] unfold propset_fmap in Hin.
                                rewrite elem_of_PropSet in Hin.
                                destruct Hin as [a0 [Ha0 Hin] ].
                                subst.
                                rewrite elem_of_PropSet in Hin.
                                destruct Hin as [a1 [Ha1 Hin] ].
                                subst.
                                unfold app_ext in Hin.
                                rewrite elem_of_PropSet in Hin.
                                destruct Hin as [le' [re' [Hle' [Hre' Hin] ] ] ].
                                rewrite elem_of_singleton in Hre'. subst.
                                rewrite update_evar_val_lift_val_comm.

                                specialize (IHszpred (ϕ^{evar: 0 ↦ fresh_evar ϕ}) (update_evar_val (fresh_evar ϕ) a1 ρ)).
                                ospecialize* IHszpred.
                                {
                                    rewrite evar_open_size'.
                                    lia.
                                }
                                {
                                    apply is_SPredicate_evar_open.
                                    assumption.
                                }
                                {
                                    wf_auto2.
                                }
                                destruct IHszpred as [IH1 IH2].
                                specialize (H' a1).
                                destruct (indec _ H a1 ρ) as [Hin'|Hnotin'].
                                {
                                    apply IH2 in H'.
                                    apply H'.
                                }
                                {
                                    exfalso.
                                    apply Hnotin'. clear Hnotin'.
                                    unfold Minterp_inhabitant.
                                    rewrite eval_app_simpl.
                                    do 2 rewrite eval_sym_simpl.
                                    unfold app_ext.
                                    rewrite elem_of_PropSet.
                                    exists le'. exists a.
                                    repeat split; assumption.
                                }
                            }
                        }
                    }
                }
            }
        Qed.

    End semantic_preservation.

    End ext.
End with_syntax.

