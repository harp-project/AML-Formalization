From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Import MatchingLogic.Semantics.Notations.

Section with_syntax.
    Context
        {Σ : Signature}
        (* TODO: maybe remove and use the imported one from Sorts_Syntax? *)
        {ds : Definedness_Syntax.Syntax}
        {ss : Sorts_Syntax.Syntax}
        (HSortImptDef : imported_definedness = ds)
        (HDefNeqInh : Definedness_Syntax.inj definedness <> Sorts_Syntax.inj inhabitant)
    .

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
        is_SData (bevar_subst ϕ₁ ϕ₂ dbi)
    with is_SPredicate_bevar_subst ψ ϕ₂ dbi:
        is_SPredicate ψ ->
        is_SData ϕ₂ ->
        is_SPredicate (bevar_subst ψ ϕ₂ dbi)
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
        is_SData (evar_open 0 x ϕ).
    Proof.
        intros H.
        unfold evar_open.
        apply is_SData_bevar_subst.
        { assumption. }
        constructor.
    Qed.

    Lemma is_SPredicate_evar_open x ϕ:
        is_SPredicate ϕ ->
        is_SPredicate (evar_open 0 x ϕ).
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
        is_SData (bsvar_subst ϕ₁ ϕ₂ dbi)
    with is_SPredicate_bsvar_subst ψ ϕ₂ dbi:
        is_SPredicate ψ ->
        is_SData ϕ₂ ->
        is_SPredicate (bsvar_subst ψ ϕ₂ dbi)
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
        is_SData (svar_open 0 x ϕ).
    Proof.
        intros H.
        unfold evar_open.
        apply is_SData_bsvar_subst.
        { assumption. }
        constructor.
    Qed.

    Lemma is_SPredicate_svar_open x ϕ:
        is_SPredicate ϕ ->
        is_SPredicate (svar_open 0 x ϕ).
    Proof.
        intros H.
        unfold evar_open.
        apply is_SPredicate_bsvar_subst.
        { assumption. }
        constructor.
    Qed.

    Section ext.
        Context
            (M : Model)
            (indec : forall (s : symbols),
              is_not_core_symbol s ->
              forall (m : Domain M) ρₑ ρₛ,
              Decision (m ∈ Minterp_inhabitant (patt_sym s) ρₑ ρₛ))
            (R : Type)
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
    
    Definition new_sym_interp (s : symbols) : Power Carrier :=
        match (decide (s = Definedness_Syntax.inj definedness)) with
        | left _ => {[ cdef ]}
        | right _ =>
            match (decide (s = Sorts_Syntax.inj inhabitant)) with
            | left _ => {[ cinh ]}
            | right _ => cel <$> (@fmap propset _ _ _ inl (@sym_interp _ M s))
            end
        end.
    
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
        Search NamedAxioms.theory_of_NamedAxioms.
        apply satisfies_theory_iff_satisfies_named_axioms.
        intros na. destruct na.
        apply single_element_definedness_impl_satisfies_definedness.
        exists cdef.
        simpl. split.
        {
            unfold new_sym_interp. case_match.
            { reflexivity. }
            contradiction n. reflexivity.
        }
        {
            auto.
        }
    Qed.

    Definition lift_value (x : Domain M) : (Domain Mext)
    := cel (inl x).

    Definition lift_set (xs : Power (Domain M)) : (Power (Domain Mext))
    := cel <$> (@fmap propset _ _ _ inl xs).

    (* Valuations lifted from the original model to the extended model. *)
    Definition lift_val_e (ρₑ : @EVarVal _ M) : (@EVarVal _ Mext)
    := λ (x : evar), (lift_value (ρₑ x)).

    Definition lift_val_s (ρₛ : @SVarVal _ M) : (@SVarVal _ Mext)
    := λ (X : svar), lift_set (ρₛ X).

    Lemma lift_set_mono (xs ys : Power (Domain M)) :
        xs ⊆ ys ->
        lift_set xs ⊆ lift_set ys.
    Proof.
        intros H.
        unfold lift_set,fmap.
        with_strategy transparent [propset_fmap] unfold propset_fmap.
        clear -H. set_solver.
    Qed.

    Lemma Mext_indec :
        forall (s : symbols),
            is_not_core_symbol s ->
            forall (m : Domain Mext) ρₑ ρₛ,
            Decision (m ∈ Minterp_inhabitant (patt_sym s) (lift_val_e ρₑ) (lift_val_s ρₛ)).
    Proof.
        intros. unfold Minterp_inhabitant.
        rewrite pattern_interpretation_app_simpl.
        unfold app_ext,lift_val_e,lift_val_s. simpl.
        destruct m.
        {
            right. intros HContra.
            rewrite elem_of_PropSet in HContra.
            destruct HContra as [le [re [HContra1 [HContra2 HContra3]]]].
            rewrite pattern_interpretation_sym_simpl in HContra1.
            rewrite pattern_interpretation_sym_simpl in HContra2.
            simpl in HContra1.
            simpl in HContra2.
            unfold new_sym_interp in HContra1, HContra2.
            unfold new_app_interp in HContra3.
            repeat case_match; subst; auto; try set_solver.
        }
        {
            right. intros HContra.
            rewrite elem_of_PropSet in HContra.
            destruct HContra as [le [re [HContra1 [HContra2 HContra3]]]].
            rewrite pattern_interpretation_sym_simpl in HContra1.
            rewrite pattern_interpretation_sym_simpl in HContra2.
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
            destruct HContra as [le [re [HContra1 [HContra2 HContra3]]]].
            rewrite pattern_interpretation_sym_simpl in HContra1.
            rewrite pattern_interpretation_sym_simpl in HContra2.
            simpl in HContra1.
            simpl in HContra2.
            unfold new_sym_interp in HContra1, HContra2.
            unfold new_app_interp in HContra3.
            repeat case_match; subst; auto; try set_solver.
        }
        destruct (indec H d ρₑ ρₛ) as [Hin|Hnotin].
        {
            left.
            unfold Minterp_inhabitant in Hin.
            rewrite pattern_interpretation_app_simpl in Hin.
            do 2 rewrite pattern_interpretation_sym_simpl in Hin.
            unfold app_ext in Hin.
            rewrite elem_of_PropSet in Hin.
            destruct Hin as [le [re [Hinle [Hinre Hin]]]].
            rewrite elem_of_PropSet.
            
            do 2 rewrite pattern_interpretation_sym_simpl.
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
            rewrite pattern_interpretation_app_simpl in Hnotin.
            do 2 rewrite pattern_interpretation_sym_simpl in Hnotin.
            unfold app_ext in Hnotin.
            rewrite elem_of_PropSet in Hnotin.
            rewrite elem_of_PropSet.
            intro HContra. apply Hnotin.
            do 2 rewrite pattern_interpretation_sym_simpl in HContra.
            simpl in HContra. unfold new_sym_interp in HContra.
            destruct HContra as [le [re [Hinle [Hinre Hin]]]].
            
            
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
                destruct Hin as [a [Hin1 Hin2]].
                inversion Hin1. subst. clear Hin1.
                rewrite elem_of_PropSet in Hin2.
                destruct Hin2 as [a [Hin2 Hin3]].
                inversion Hin2. subst. clear Hin2.
                rewrite elem_of_PropSet in Hin3.
                destruct Hin3 as [le [lre [Hle [Hre HAlmost]]]].
                rewrite elem_of_PropSet in Hre.
                inversion Hre. clear Hre. subst.
                destruct Hinre as [a' [Ha' Ha'']].
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
                destruct_and_ex!.
                inversion H2. subst. clear H2.
                inversion H0. subst. clear H0.
                rewrite elem_of_PropSet in H3.
                destruct H3 as [a [H3 H3']].
                inversion H3.
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
            (ρₑ : @EVarVal _ M)
            (ρₛ : @SVarVal _ M)
            ρe0 ρs0
            :
            is_not_core_symbol s ->
            pattern_interpretation ρe0 ρs0 (patt_sym s) =
            lift_set (pattern_interpretation ρₑ ρₛ (patt_sym s)).
        Proof.
            intros H.
            do 2 rewrite pattern_interpretation_sym_simpl.
            clear -H. unfold_leibniz.
            unfold is_not_core_symbol,is_core_symbol in H.
            unfold sym_interp at 1. simpl. unfold new_sym_interp.
            repeat case_match; subst.
            { exfalso. tauto. }
            { exfalso. tauto. }
            unfold lift_set,fmap. reflexivity.
        Qed.
        
        Lemma semantics_preservation_inhabitant_set (s : symbols)
            (ρₑ : @EVarVal _ M)
            (ρₛ : @SVarVal _ M)
            ρe0 ρs0
            :
            is_not_core_symbol s ->
            pattern_interpretation ρe0 ρs0 (patt_inhabitant_set (patt_sym s))
            = lift_set (pattern_interpretation ρₑ ρₛ (patt_inhabitant_set (patt_sym s))).
        Proof.
            intros H.
            rename H into Hnc.
            (* For some reason, the tactic [unfold_leibniz] performed later
               in the proof script does nothing. *)
            unfold_leibniz. 
            unfold patt_inhabitant_set.
            do 2 rewrite pattern_interpretation_app_simpl.
            rewrite (semantics_preservation_sym ρₑ ρₛ);[assumption|].
            remember (pattern_interpretation ρₑ ρₛ (patt_sym s)) as ps.
            unfold Sorts_Syntax.sym.
            do 2 rewrite pattern_interpretation_sym_simpl.
            unfold sym_interp at 1. simpl. unfold new_sym_interp.
            repeat case_match.
            { exfalso. clear -e HDefNeqInh. congruence. }
            2: { contradiction n0. reflexivity. }
            {
                clear e Heqs1 Heqs0 n.
                unfold app_ext at 1.
                unfold app_interp at 1. simpl. unfold new_app_interp.
                set_unfold. intros x. split.
                {
                    intros [x0 [x1 H]]. destruct_and!. subst.
                    repeat case_match.
                    { exfalso. clear -H2. set_solver. }
                    { exfalso. clear -H2. set_solver. }
                    { subst. set_solver. }
                    { subst. set_solver. }
                }
                {
                    intros [y H]. destruct_and!. subst.
                    destruct H1 as [y0 H]. destruct_and!. subst.
                    destruct H1 as [x [x0 H]].
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

        Lemma update_evar_val_lift_val_e_comm
            (ρₑ : @EVarVal _ M)
            (x : evar)
            (d : Domain M)
            :
            (@update_evar_val Σ Mext x (cel (inl d)) (lift_val_e ρₑ))
            = lift_val_e (@update_evar_val Σ M x d ρₑ).
        Proof.
            apply functional_extensionality.
            intros x'.
            unfold update_evar_val, lift_val_e,lift_value.
            case_match; reflexivity.
        Qed.
 
        Lemma update_svar_val_lift_set_comm
            (ρₛ : @SVarVal _ M)
            (X : svar)
            (D : propset (Domain M))
            :
        (@update_svar_val Σ Mext X (lift_set D) (lift_val_s ρₛ))
        = lift_val_s (@update_svar_val Σ M X D ρₛ).
        Proof.
            apply functional_extensionality.
            intros X'.
            unfold update_svar_val,lift_val_s,lift_set.
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
                forall (ϕ : Pattern) (ρₑ : @EVarVal _ M) (ρₛ : @SVarVal _ M),
                size' ϕ < sz ->
                is_SData ϕ ->
                well_formed ϕ ->
                pattern_interpretation (lift_val_e ρₑ) (lift_val_s ρₛ) ϕ
                = lift_set (pattern_interpretation ρₑ ρₛ ϕ)
            )
            /\
            (
                forall (ψ : Pattern) (ρₑ : @EVarVal _ M) (ρₛ : @SVarVal _ M),
                size' ψ < sz ->
                is_SPredicate ψ ->
                well_formed ψ ->
                (pattern_interpretation (lift_val_e ρₑ) (lift_val_s ρₛ) ψ = ∅
                <-> pattern_interpretation ρₑ ρₛ ψ = ∅)
                /\
                (pattern_interpretation (lift_val_e ρₑ) (lift_val_s ρₛ) ψ = ⊤
                <-> pattern_interpretation ρₑ ρₛ ψ = ⊤)
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
                    intros ϕ ρₑ ρₛ Hszϕ HSData Hwf.
                    destruct HSData; simpl in Hszϕ.
                    {
                        (* patt_bott *)
                        do 2 rewrite pattern_interpretation_bott_simpl.
                        unfold lift_set.
                        unfold fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear.
                        unfold_leibniz.
                        set_solver.
                    }
                    {
                        (* free_evar x*)
                        do 2 rewrite pattern_interpretation_free_evar_simpl.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear. unfold_leibniz. set_solver.
                    }
                    {
                        (* free_svar X *)
                        do 2 rewrite pattern_interpretation_free_svar_simpl.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear. unfold_leibniz. set_solver.
                    }
                    {
                        (* bound_evar X *)
                        do 2 rewrite pattern_interpretation_bound_evar_simpl.
                        unfold lift_set,fmap.
                        with_strategy transparent [propset_fmap] unfold propset_fmap.
                        clear. unfold_leibniz. set_solver.
                    }
                    {
                        (* bound_svar X *)
                        do 2 rewrite pattern_interpretation_bound_svar_simpl.
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
                        do 2 rewrite pattern_interpretation_and_simpl.
                        rewrite (semantics_preservation_inhabitant_set ρₑ ρₛ);[assumption|].
                        do 2 rewrite pattern_interpretation_not_simpl.
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
                        remember (pattern_interpretation ρₑ ρₛ (patt_inhabitant_set (patt_sym s))) as Xinh.
                        remember (pattern_interpretation ρₑ ρₛ ϕ) as Xϕ.
                        clear HeqXinh HeqXϕ IHszpred IHszdata.
                        unfold_leibniz.
                        set_solver.
                    }
                    {
                        (* patt_app ϕ₁ ϕ₂ *)
                        do 2 rewrite pattern_interpretation_app_simpl.
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
                            intros [x0 [x1 H]].
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
                        do 2 rewrite pattern_interpretation_or_simpl.
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
                        do 2 rewrite pattern_interpretation_and_simpl.

                        rename H into Hspred.
                    
                        destruct (classic (pattern_interpretation ρₑ ρₛ ψ = ∅)).
                        {
                            rewrite IHszdata.
                            { lia. }
                            { exact HSData. }
                            { wf_auto2. }
                            clear HSData IHszdata. 
                            unfold_leibniz.
                            specialize (IHszpred ψ ρₑ ρₛ ltac:(lia) ltac:(assumption) ltac:(wf_auto2)).
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
                            specialize (IHszpred ψ ρₑ ρₛ ltac:(lia) ltac:(assumption) ltac:(wf_auto2)).
                            specialize (IHszdata ϕ ρₑ ρₛ ltac:(lia) HSData ltac:(wf_auto2)).

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
                        unshelve(erewrite pattern_interpretation_exists_of_sort).
                        3: { rewrite HSortImptDef. apply Mext_satisfies_definedness. }
                        { intros. apply Mext_indec. assumption. }
                        unshelve(erewrite pattern_interpretation_exists_of_sort).
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
                            destruct (Mext_indec H c ρₑ ρₛ) as [Hin|Hnotin].
                            {
                                unfold Minterp_inhabitant in Hin.
                                (* [c] comes from [Domain M] *)
                                destruct c.
                                {
                                    exfalso.
                                    rewrite pattern_interpretation_app_simpl in Hin.
                                    do 2 rewrite pattern_interpretation_sym_simpl in Hin.
                                    unfold app_ext in Hin. simpl in Hin.
                                    unfold new_sym_interp,new_app_interp in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct_and_ex!. repeat case_match; subst; auto; try congruence.
                                    {
                                        clear Heqs2 n0 n Heqs1 n1 Heqs3 e Heqs4 H0.
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        clear -H3. set_solver.
                                    }
                                    {
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        clear -H3. set_solver.
                                    }
                                }
                                {
                                    exfalso.
                                    rewrite pattern_interpretation_app_simpl in Hin.
                                    do 2 rewrite pattern_interpretation_sym_simpl in Hin.
                                    unfold app_ext in Hin. simpl in Hin.
                                    unfold new_sym_interp,new_app_interp in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct_and_ex!. repeat case_match; subst; auto; try congruence.
                                    {
                                        clear Heqs2 n0 n Heqs1 n1 Heqs3 e Heqs4 H0.
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        clear -H3. set_solver.
                                    }
                                    {
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        clear -H3. set_solver.
                                    }
                                }
                                destruct el.
                                2: {
                                    exfalso.
                                    rewrite pattern_interpretation_app_simpl in Hin.
                                    do 2 rewrite pattern_interpretation_sym_simpl in Hin.
                                    unfold app_ext in Hin. simpl in Hin.
                                    unfold new_sym_interp,new_app_interp in Hin.
                                    rewrite elem_of_PropSet in Hin.
                                    destruct_and_ex!. repeat case_match; subst; auto; try congruence.
                                    {
                                        clear Heqs2 n0 n Heqs1 n1 Heqs3 e Heqs4 H0.
                                        unfold fmap in H3.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H3.
                                        clear -H3. set_solver.
                                    }
                                    {
                                        unfold fmap in H2.
                                        with_strategy transparent [propset_fmap] unfold propset_fmap in H2.
                                        clear -H2. set_solver.
                                    }
                                }
                                rewrite update_evar_val_lift_val_e_comm in Hc.
                                rewrite IHszdata in Hc.
                                4: { wf_auto2. }
                                3: { apply is_SData_evar_open. assumption. }
                                2: { rewrite evar_open_size'. lia. }

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
                                4: { wf_auto2. }
                                3: { constructor. assumption. }
                                2: { simpl. lia. }

                                exists d.
                                destruct (indec H d ρₑ ρₛ) as [Hin'|Hnotin'].
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
                            destruct Hc as [a [Ha Ha']].
                            destruct a.
                            2: {
                                inversion Ha.
                            }
                            inversion Ha. clear Ha. subst.
                            rewrite elem_of_PropSet in Ha'.
                            destruct Ha' as [a [Ha Ha']].
                            inversion Ha. clear Ha. subst.
                            rewrite elem_of_PropSet.
                            destruct (indec H c ρₑ ρₛ).
                            2: {
                                exfalso. clear -Ha'. set_solver.
                            }
                            exists (lift_value c).
                            rewrite update_evar_val_lift_val_e_comm.
                            destruct (Mext_indec H (lift_value c) ρₑ ρₛ) as [Hin | Hnotin].
                            {
                                rewrite IHszdata.
                                4: { wf_auto2. }
                                3: { apply is_SData_evar_open. assumption. }
                                2: { rewrite evar_open_size'. lia. }
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
                                4: { wf_auto2. }
                                3: { constructor. assumption. }
                                2: { simpl. lia. }
                                clear -Hin Hnotin.
                                unfold lift_value,lift_set,fmap in Hnotin.
                                with_strategy transparent [propset_fmap] unfold propset_fmap in Hnotin.
                                set_solver.
                            }
                        }
                    }
                    {
                        (* patt_mu (patt_sym s) ϕ *)
                        do 2 rewrite pattern_interpretation_mu_simpl.
                        simpl.
                        match goal with
                        | [ |- (Lattice.LeastFixpointOf ?fF = lift_set (Lattice.LeastFixpointOf ?fG))] =>
                            remember fF as F; remember fG as G
                        end.
                        Search Lattice.LeastFixpointOf.
                        symmetry.
                        assert (HmonoF: @Lattice.MonotonicFunction
                            (propset Carrier)
                            (Lattice.PropsetOrderedSet Carrier) F).
                        {
                            subst F.
                            replace Carrier with (Domain Mext) by reflexivity.
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
                            rewrite <- HGmuG at 2.
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
                            set (λ A, lift_set (pattern_interpretation ρₑ (update_svar_val (fresh_svar ϕ) (strip A) ρₛ) (svar_open 0 (fresh_svar ϕ) ϕ))) as G'.

                            assert (Hstripmono: forall x y, x ⊆ y -> strip x ⊆ strip y).
                            {
                                intros x y Hxy.
                                unfold strip. unfold lift_value.
                                clear -Hxy. set_solver.
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

                            assert (lift_set (@Lattice.LeastFixpointOf _ _ L G) = (@Lattice.LeastFixpointOf _ _ L' G')).
                            {
                                apply Lattice.LeastFixpoint_unique_2.
                        {
                            exact HmonoF.
                        }
                            }
                        }
                    }
                }
                admit.
            }
            {   (* preservation of predicates *)
                intros HSPred. induction HSPred.
            }
        Qed.

    End semantic_preservation.

End with_syntax.