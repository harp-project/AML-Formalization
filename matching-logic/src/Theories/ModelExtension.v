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
    Pattern
    Syntax
    Semantics
    DerivedOperators_Syntax
    Theories.Definedness_Syntax
    Theories.Sorts_Syntax
.

Import MatchingLogic.Semantics.Notations.

Section with_syntax.
    Context
        {Σ : Signature}
        {ds : Definedness_Syntax.Syntax}
        {ss : Sorts_Syntax.Syntax}
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
                    clear -H M_def HDefNeqInh. rename H into Hnc.
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
                }
                admit.
            }
            {   (* preservation of predicates *)
                intros HSPred. induction HSPred.
            }
        Qed.

    End semantic_preservation.

End with_syntax.