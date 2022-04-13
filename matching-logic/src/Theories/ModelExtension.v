From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp
Require Import
    base
    decidable
    propset
    fin_maps
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
    | sdata_all (ϕ : Pattern) (s : symbols)
        : is_SData ϕ -> is_not_core_symbol s -> is_SData (patt_forall_of_sort (patt_sym s) ϕ)
    | sdata_mu (ϕ : Pattern)
        : is_SData ϕ -> is_SData (patt_mu ϕ)
    .

    Section ext.
        Context
            (M : Model)
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

    Definition lift_value (x : Domain M) : (Domain Mext)
    := cel (inl x).

    Definition lift_set (xs : Power (Domain M)) : (Power (Domain Mext))
    := cel <$> (@fmap propset _ _ _ inl xs).

    (* Valuations lifted from the original model to the extended model. *)
    Definition lift_val_e (ρₑ : @EVarVal _ M) : (@EVarVal _ Mext)
    := λ (x : evar), (lift_value (ρₑ x)).

    Definition lift_val_s (ρₛ : @SVarVal _ M) : (@SVarVal _ Mext)
    := λ (X : svar), lift_set (ρₛ X).

    Section semantic_preservation.
       Context
            (M_def : M ⊨ᵀ Definedness_Syntax.theory)
            (ρₑ : @EVarVal _ M)
            (ρₛ : @SVarVal _ M)
        .
        
        Lemma SPred_is_pre_predicate (ψ : Pattern) :
            is_SPredicate ψ ->
            M_pre_predicate M ψ.
        Proof.
            intros HSPred.
            induction HSPred.
            { apply (@M_pre_pre_predicate_impl_M_pre_predicate _ 0). apply M_pre_pre_predicate_bott. }
            { apply (@M_pre_pre_predicate_impl_M_pre_predicate _ 0). apply T_pre_predicate_defined. exact M_def. }
            { apply (@M_pre_pre_predicate_impl_M_pre_predicate _ 0). apply M_pre_pre_predicate_imp. exact IHHSPred1. exact IHHSPred2. }
            { unfold patt_exists_of_sort.
              apply M_pre_pre_predicate_exists.
              apply pre_predicate_0.
                intros l Hfa Hci Hwf'.
                apply M_predicate_exists_of_sort.
              { rewrite HSortImptDef. apply M_def. }
              Print M_predicate.
              unfold M_predicate in IHHSPred. intros ρₑ0 ρₛ0.
              Search "shadow".
              unfold evar_open.
              rewrite -> element_substitution_lemma with (x := fresh_evar ϕ).
              Search update_evar_val.
              rewrite update_evar_val_same_2.
              apply IHHSPred.
              Check element_substitution_lemma.
              specialize (IHHSPred ρₑ0 ρₛ0).
              Search pattern_interpretation evar_open.
              Check M_predicate_exists_of_sort.
              Search M_predicate evar_open.

        Qed.
    
        Lemma SPred_is_predicate (ψ : Pattern) :
            is_SPredicate ψ ->
            M_predicate M ψ.
        Proof. Qed.


        Lemma semantics_preservation_sym (s : symbols) :
            is_not_core_symbol s ->
            pattern_interpretation (lift_val_e ρₑ) (lift_val_s ρₛ) (patt_sym s) =
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
        
        Lemma semantics_preservation_inhabitant_set (s : symbols) :
            is_not_core_symbol s ->
            pattern_interpretation (lift_val_e ρₑ) (lift_val_s ρₛ) (patt_inhabitant_set (patt_sym s))
            = lift_set (pattern_interpretation ρₑ ρₛ (patt_inhabitant_set (patt_sym s))).
        Proof.
            intros H.
            rename H into Hnc.
            (* For some reason, the tactic [unfold_leibniz] performed later
               in the proof script does nothing. *)
            unfold_leibniz. 
            unfold patt_inhabitant_set.
            do 2 rewrite pattern_interpretation_app_simpl.
            rewrite semantics_preservation_sym;[assumption|].
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

        Lemma semantics_preservation_data
            (ϕ : Pattern)
            :
            is_SData ϕ ->
            pattern_interpretation (lift_val_e ρₑ) (lift_val_s ρₛ) ϕ
            = lift_set (pattern_interpretation ρₑ ρₛ ϕ)
        with semantics_preservation_pred
            (ψ : Pattern)
            :
            is_SPredicate ψ ->
            (pattern_interpretation (lift_val_e ρₑ) (lift_val_s ρₛ) ψ = ∅
             <-> pattern_interpretation ρₑ ρₛ ψ = ∅)
            /\
            (pattern_interpretation (lift_val_e ρₑ) (lift_val_s ρₛ) ψ = ⊤
             <-> pattern_interpretation ρₑ ρₛ ψ = ⊤).
        Proof.
            {
                (* preservation of data patterns *)
                intros HSData. induction HSData.
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
                    rewrite semantics_preservation_inhabitant_set;[assumption|].
                    do 2 rewrite pattern_interpretation_not_simpl.
                    rewrite IHHSData.
                    remember (pattern_interpretation ρₑ ρₛ (patt_inhabitant_set (patt_sym s))) as Xinh.
                    remember (pattern_interpretation ρₑ ρₛ ϕ) as Xϕ.
                    clear HeqXinh HeqXϕ IHHSData semantics_preservation_data semantics_preservation_pred.
                    unfold_leibniz.
                    set_solver.
                }
                {
                    (* patt_app ϕ₁ ϕ₂ *)
                    do 2 rewrite pattern_interpretation_app_simpl.
                    rewrite IHHSData1 IHHSData2.
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
                    rewrite IHHSData1 IHHSData2.
                    clear.
                    unfold_leibniz.
                    unfold lift_set,fmap.
                    with_strategy transparent [propset_fmap] unfold propset_fmap.
                    set_solver.
                }
                {
                    (* patt_and ϕ ψ *)
                    do 2 rewrite pattern_interpretation_and_simpl.
                    rewrite IHHSData.
                    clear semantics_preservation_data.
                    specialize (semantics_preservation_pred ψ ltac:(assumption)).
                    clear H HSData IHHSData.
                    unfold_leibniz.
                    (* TODO we have to destruct on whether the data pattern is empty or not *)
                    unfold lift_set,fmap.
                    with_strategy transparent [propset_fmap] unfold propset_fmap.
                    set_solver.
                }
                admit.
            }
            {   (* preservation of predicates *)
                intros HSPred. induction HSPred.
            }
        Qed.

    End semantic_preservation.

End with_syntax.